[@@@flambda.o3]

open Datalog_types

module Int = struct
  include Numbers.Int
  module Tree = Patricia_tree.Make (Numbers.Int)
  module Map = Tree.Map
end

module type Heterogenous = Heterogenous

module Constant = Constant

let run_handler (type a) (value : a) (handler : a handler) =
  match handler with Ignore -> () | Set_ref r -> r := value

module Type = struct
  type (_, _) eq = Equal : ('a, 'a) eq

  module Id = struct
    type _ id = ..

    module type ID = sig
      type t

      type _ id += Id : t id
    end

    type !'a t = (module ID with type t = 'a)

    let make (type a) () : a t =
      (module struct
        type t = a

        type _ id += Id : t id
      end)

    let[@inline] uid (type a) ((module A) : a t) : int =
      (* This really should be [Obj.Extension_constructor.(id (of_val A.Id))],
         but we get uids frequently enough that the overhead of checking the
         constructor shape is noticeable.

         [A.Id] is clearly a constant extension constructor, though. *)
      Obj.(obj (field (repr A.Id) 1))

    let provably_equal (type a b) ((module A) : a t) ((module B) : b t) :
        (a, b) eq option =
      match A.Id with B.Id -> Some Equal | _ -> None
  end
end

module ColumnType : sig
  type 'a t

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist

  type 'a column = 'a t

  val print : Format.formatter -> 'a t -> unit

  val printer : 'a t -> Format.formatter -> 'a -> unit

  val make : string -> print:(Format.formatter -> int -> unit) -> int t

  val int : int t

  module Cell : sig
    type 'a t

    val create : 'a column -> 'a t

    val set : 'a t -> 'a -> unit

    val iterator : 'a t -> 'a Trie.Iterator.t
  end

  val is_trie : 'a hlist -> ('a, 'b) Trie.is_any_trie

  val provably_equal : 'a t -> 'b t -> ('a, 'b) Type.eq option

  val create_ref : 'a t -> 'a ref
end = struct
  type 'a t =
    { id : 'a Type.Id.t;
      name : string;
      print : Format.formatter -> 'a -> unit;
      is_int : ('a, int) Type.eq
    }

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist

  let print ppf { id; name; _ } =
    Format.fprintf ppf "%s/%d" name (Type.Id.uid id)

  let printer { print; _ } = print

  let make name ~print = { id = Type.Id.make (); name; print; is_int = Equal }

  let int = make "int" ~print:Format.pp_print_int

  let create_ref (type a) ({ is_int = Equal; _ } : a t) : a ref = ref 0

  let provably_equal t1 t2 = Type.Id.provably_equal t1.id t2.id

  type 'a column = 'a t

  let rec is_trie : type a b. a hlist -> (a, b) Trie.is_any_trie =
   fun s ->
    match s with
    | [] -> Is_trie Trie.value_is_trie
    | { is_int = Equal; _ } :: s' ->
      let (Is_trie t') = is_trie s' in
      Is_trie (Trie.map_is_trie Trie.is_map t')

  module Cell = struct
    type 'a t = Cell : unit Int.Map.t ref -> int t [@@unboxed]

    let create (type a) ({ is_int = Equal; _ } : a column) : a t =
      Cell (ref Int.Map.empty)

    let set (type a) (Cell r : a t) (v : a) : unit = r := Int.Map.singleton v ()

    let iterator (type a) (Cell cell : a t) : a Trie.Iterator.t =
      Trie.create_iterator Trie.is_map cell Ignore
  end
end

module Joined_iterator (Iterator : Iterator) : sig
  include Iterator

  val create : 'a Iterator.t list -> 'a t
end = struct
  type 'k t =
    { iterators : 'k Iterator.t array;
      mutable at_end : bool
    }

  let current (type a) ({ iterators; at_end } : a t) : a option =
    if at_end
    then None
    else Iterator.current iterators.(Array.length iterators - 1)

  let rec search : type a. a Iterator.t array -> int -> a -> a option =
   fun iterators index_of_lowest_key highest_key ->
    let iterator_with_lowest_key = iterators.(index_of_lowest_key) in
    let equal = Iterator.equal_key iterator_with_lowest_key in
    match Iterator.current iterator_with_lowest_key with
    | None -> None
    | Some lowest_key when equal lowest_key highest_key ->
      (* All iterators are on the same key. *)
      Some lowest_key
    | Some _ -> (
      Iterator.seek iterator_with_lowest_key highest_key;
      match Iterator.current iterator_with_lowest_key with
      | None -> None
      | Some new_highest_key ->
        search iterators
          ((index_of_lowest_key + 1) mod Array.length iterators)
          new_highest_key)

  let repair (type a) ({ iterators; at_end } as j : a t) =
    assert (not at_end);
    if Array.length iterators > 1
    then
      let iterator = iterators.(Array.length iterators - 1) in
      match Iterator.current iterator with
      | None -> j.at_end <- true
      | Some highest_key -> (
        match search iterators 0 highest_key with
        | None -> j.at_end <- true
        | Some _ -> ())

  let advance (type a) ({ iterators; at_end } as t : a t) =
    if not at_end
    then (
      let highest_iterator = iterators.(Array.length iterators - 1) in
      Iterator.advance highest_iterator;
      repair t)

  let seek (type a) ({ iterators; at_end } as t : a t) (key : a) =
    if not at_end
    then (
      let highest_iterator = iterators.(Array.length iterators - 1) in
      Iterator.seek highest_iterator key;
      repair t)

  exception Empty_iterator

  let init (type a) ({ iterators; _ } as j : a t) =
    try
      Array.iter
        (fun (it : a Iterator.t) ->
          Iterator.init it;
          match Iterator.current it with
          | None -> raise Empty_iterator
          | Some _ -> ())
        iterators;
      Array.sort
        (fun (it1 : a Iterator.t) (it2 : a Iterator.t) ->
          let compare = Iterator.compare_key it1 in
          Option.compare compare (Iterator.current it1) (Iterator.current it2))
        iterators;
      j.at_end <- false;
      repair j
    with Empty_iterator -> j.at_end <- true

  let accept (type a) ({ iterators; at_end } : a t) =
    if at_end then invalid_arg "Joined_iterator.accept: iterator is at end";
    Array.iter Iterator.accept iterators

  let equal_key { iterators; _ } = Iterator.equal_key iterators.(0)

  let compare_key { iterators; _ } = Iterator.compare_key iterators.(0)

  let create (iterators : _ Iterator.t list) : _ t =
    match iterators with
    | [] -> invalid_arg "Joined_iterator.create: cannot join an empty list"
    | _ -> { iterators = Array.of_list iterators; at_end = false }
end
[@@inline always]

module Table : sig
  module Id : sig
    type ('t, 'k, 'v) t

    type ('k, 'v) poly = Id : ('t, 'k, 'v) t -> ('k, 'v) poly

    val create_trie :
      name:string -> ('k -> 'r) ColumnType.hlist -> ('k -> 'r, 'v) poly

    val schema : ('t, 'k, 'v) t -> 'k ColumnType.hlist
  end

  val is_empty : ('t, 'k, 'v) Id.t -> 't -> bool

  val add : ('t, 'k, 'v) Id.t -> 'k Constant.hlist -> 'v -> 't -> 't

  val mem_refs : ('t, 'k, 'v) Id.t -> 'k Ref.hlist -> 't -> bool

  val remove_refs : ('t, 'k, 'v) Id.t -> 'k Ref.hlist -> 't -> 't

  type 't binder

  module Iterator : sig
    include Iterator

    type _ hlist =
      | [] : 'a option hlist
      | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist
  end

  val cell_iterator : 'a ColumnType.Cell.t -> 'a Iterator.t

  val iterator : ('t, 'k, 'v) Id.t -> 't binder * 'k Iterator.hlist

  val bind : ('t, 'k, 'v) Id.t -> 't -> 't binder -> unit

  module Map : sig
    type t

    val print : Format.formatter -> t -> unit

    val empty : t

    val get : t -> ('t, 'k, 'v) Id.t -> 't

    val set : t -> ('t, 'k, 'v) Id.t -> 't -> t

    val current_scope : t -> int Int.Map.t

    val cut : t -> cut_after:int Int.Map.t -> t
  end
end = struct
  module Repr = struct
    type ('t, 'k, 'v) trie =
      { trie : 't;
        facts : ('k Constant.hlist * 'v) Int.Map.t;
        last_fact_id : int
      }

    type ('t, 'k, 'v) t =
      | Trie :
          ('t, 'k -> 'r, int) Trie.is_trie
          -> (('t, 'k -> 'r, 'v) trie, 'k -> 'r, 'v) t

    type 't handler_ =
      | Handler : 't handler -> ('t, 'k -> 'r, 'v) trie handler_
    [@@unboxed]

    let run_handler (type a k v) (repr : (a, k, v) t) : a -> a handler_ -> unit
        =
      match repr with
      | Trie _ -> fun t (Handler handler) -> run_handler t.trie handler

    let iter (type a k v) (repr : (a, k, v) t)
        (f : k Constant.hlist -> v -> unit) (t : a) =
      match repr with
      | Trie is_trie ->
        Trie.iter is_trie
          (fun keys fact_id ->
            let _, value =
              try Int.Map.find fact_id t.facts with Not_found -> assert false
            in
            f keys value)
          t.trie

    let print repr ?(pp_sep = Format.pp_print_cut) pp_row ppf table =
      let first = ref true in
      iter repr
        (fun keys value ->
          if !first then first := false else pp_sep ppf ();
          pp_row keys value)
        table

    let iterator (type a k v) (repr : (a, k, v) t) :
        a handler_ * k Trie.Iterator.hlist =
      match repr with
      | Trie is_trie ->
        let handler, iterator = Trie.iterators is_trie Ignore in
        Handler handler, iterator

    let empty (type a k v) (repr : (a, k, v) t) : a =
      match repr with
      | Trie is_trie ->
        { trie = Trie.empty is_trie; facts = Int.Map.empty; last_fact_id = -1 }

    let is_empty (type a k v) (repr : (a, k, v) t) : a -> bool =
      match repr with Trie _ -> fun { facts; _ } -> Int.Map.is_empty facts

    let add (type a k v) (repr : (a, k, v) t) : k Constant.hlist -> v -> a -> a
        =
      match repr with
      | Trie is_trie -> (
        fun keys value t ->
          match Trie.find_opt is_trie keys t.trie with
          | Some _ -> t
          | None ->
            let last_fact_id = t.last_fact_id + 1 in
            let trie = Trie.add_or_replace is_trie keys last_fact_id t.trie in
            let facts = Int.Map.add last_fact_id (keys, value) t.facts in
            { last_fact_id; trie; facts })

    let mem_refs (type a k v) (repr : (a, k, v) t) : k Ref.hlist -> a -> bool =
      match repr with
      | Trie is_trie ->
        fun keys t -> Option.is_some (Trie.find_opt_refs is_trie keys t.trie)

    let remove_refs (type a k v) (repr : (a, k, v) t) : k Ref.hlist -> a -> a =
      match repr with
      | Trie is_trie -> (
        fun keys t ->
          match Trie.find_opt_refs is_trie keys t.trie with
          | None -> t
          | Some fact_id ->
            let trie = Trie.remove_refs is_trie keys t.trie in
            let facts = Int.Map.remove fact_id t.facts in
            { last_fact_id = t.last_fact_id; trie; facts })

    let current_scope (type a k v) (repr : (a, k, v) t) : a -> int =
      match repr with Trie _ -> fun { last_fact_id; _ } -> last_fact_id

    let cut (type a k v) (repr : (a, k, v) t) : a -> cut_after:int -> a =
      match repr with
      | Trie is_trie ->
        fun t ~cut_after ->
          let _, _, delta_facts = Int.Map.split cut_after t.facts in
          let trie =
            Int.Map.fold
              (fun fact_id (k, _) trie ->
                Trie.add_or_replace is_trie k fact_id trie)
              delta_facts (Trie.empty is_trie)
          in
          { facts = delta_facts; last_fact_id = t.last_fact_id; trie }
  end

  module Id = struct
    type ('t, 'k, 'v) t =
      { id : 't Type.Id.t;
        name : string;
        schema : 'k ColumnType.hlist;
        repr : ('t, 'k, 'v) Repr.t
      }

    type ('k, 'v) poly = Id : ('t, 'k, 'v) t -> ('k, 'v) poly

    let print ppf t = Format.fprintf ppf "%s/%d" t.name (Type.Id.uid t.id)

    let[@inline] create_trie ~name schema =
      let (Is_trie is_trie) = ColumnType.is_trie schema in
      Id { id = Type.Id.make (); name; repr = Trie is_trie; schema }

    let[@inline] uid { id; _ } = Type.Id.uid id

    let[@inline] schema { schema; _ } = schema

    let[@inline] provably_equal r1 r2 = Type.Id.provably_equal r1.id r2.id
  end

  type 't binder = 't Repr.handler_

  module Iterator = Trie.Iterator

  let cell_iterator = ColumnType.Cell.iterator

  let iterator id = Repr.iterator id.Id.repr

  let bind id table binder = Repr.run_handler id.Id.repr table binder

  let rec print_row :
      type a. a ColumnType.hlist -> Format.formatter -> a Constant.hlist -> unit
      =
   fun schema ppf ->
    match schema with
    | [] -> fun [] -> ()
    | [k] -> fun [x] -> ColumnType.printer k ppf x
    | k :: k' ->
      fun (x :: y) ->
        Format.fprintf ppf "%a,@ %a" (ColumnType.printer k) x (print_row k') y

  let print_table id ppf table =
    Format.fprintf ppf "@[<v>%a@]"
      (Repr.print id.Id.repr (fun keys _ ->
           Format.fprintf ppf "@[%a(%a).@]" Id.print id
             (print_row (Id.schema id))
             keys))
      table

  let print id ppf table =
    let header = Format.asprintf "%a" Id.print id in
    Format.fprintf ppf "@[<v>%s@ %s@ %a@]" header
      (String.make (String.length header) '=')
      (print_table id) table

  let is_empty id table = Repr.is_empty id.Id.repr table

  let add id keys value table = Repr.add id.Id.repr keys value table

  let mem_refs id args table = Repr.mem_refs id.Id.repr args table

  let remove_refs id keys table = Repr.remove_refs id.Id.repr keys table

  let empty id = Repr.empty id.Id.repr

  let current_scope id table = Repr.current_scope id.Id.repr table

  let cut id table ~cut_after = Repr.cut id.Id.repr table ~cut_after

  module Map = struct
    type binding = Binding : ('t, 'k, 'v) Id.t * 't -> binding

    type t = binding Int.Map.t

    let print ppf tables =
      Format.fprintf ppf "@[<v>";
      Int.Map.iter
        (fun _ (Binding (id, table)) ->
          print id ppf table;
          Format.fprintf ppf "@ ")
        tables;
      Format.fprintf ppf "@]"

    let get (type t k v) tables (id : (t, k, v) Id.t) : t =
      match Int.Map.find_opt (Id.uid id) tables with
      | Some (Binding (existing_id, table)) -> (
        match Id.provably_equal id existing_id with
        | Some Equal -> table
        | None -> Misc.fatal_error "Inconsistent type for uid.")
      | None -> empty id

    let set (type t k v) tables (id : (t, k, v) Id.t) (table : t) =
      if is_empty id table
      then
        if Int.Map.mem (Id.uid id) tables
        then Int.Map.remove (Id.uid id) tables
        else tables
      else
        match Int.Map.find_opt (Id.uid id) tables with
        | None -> Int.Map.add (Id.uid id) (Binding (id, table)) tables
        | Some (Binding (existing_id, existing_table)) ->
          if match Id.provably_equal id existing_id with
             | Some Equal -> table == existing_table
             | None -> assert false
          then tables
          else Int.Map.add (Id.uid id) (Binding (id, table)) tables

    let current_scope tables =
      Int.Map.map (fun (Binding (id, table)) -> current_scope id table) tables

    let cut tables ~cut_after:level =
      Int.Map.mapi
        (fun tid (Binding (id, table) as binding) ->
          match Int.Map.find_opt tid level with
          | Some cut_after -> Binding (id, cut id table ~cut_after)
          | None -> binding)
        tables

    let empty = Int.Map.empty
  end
end

module Iterator = Joined_iterator (Table.Iterator)

module Database = struct
  type t = { tables : Table.Map.t } [@@unboxed]

  let print ppf { tables } = Table.Map.print ppf tables

  let empty = { tables = Table.Map.empty }

  let get_table { tables } id = Table.Map.get tables id

  let set_table { tables } id table = { tables = Table.Map.set tables id table }

  let current_level { tables } = Table.Map.current_scope tables

  let cut { tables } ~cut_after = { tables = Table.Map.cut tables ~cut_after }
end

module Variable = struct
  type t = string

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : (t * 'a ColumnType.t) * 'b hlist -> ('a -> 'b) hlist
end

module Term = struct
  type 'a t =
    | Variable of Variable.t
    | Constant of 'a

  let variable v = Variable v

  let constant c = Constant c

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist

  let rec variables : type a. a Variable.hlist -> a hlist = function
    | [] -> []
    | (var, _) :: vars -> Variable var :: variables vars
end

type _ atom = Atom : ('t, 'k, 'v) Table.Id.t * 'k Term.hlist -> 'v atom

let atom (Table.Id.Id id) args = Atom (id, args)

module Cursor = struct
  type outcome =
    | Reject
    | Accept

  type _ instruction =
    | Reject : outcome instruction
    | Accept : outcome instruction
    | Mem : ('k, 'v) Table.Id.poly * 'k Ref.hlist -> bool instruction
    | Ite : bool instruction * 'a instruction * 'a instruction -> 'a instruction

  let rec run_instruction : type a. Database.t -> a instruction -> a =
   fun db instruction ->
    match instruction with
    | Accept -> Accept
    | Reject -> Reject
    | Mem (Id id, args) -> Table.mem_refs id args (Database.get_table db id)
    | Ite (c, t, e) ->
      if run_instruction db c
      then run_instruction db t
      else run_instruction db e

  type level =
    | Level :
        { iterator : 'a Iterator.t;
          cell : 'a ColumnType.Cell.t option;
          output : 'a handler;
          instruction : outcome instruction
        }
        -> level

  type binder = Bind : ('t, 'k, 'v) Table.Id.t * 't Table.binder -> binder

  type _ cells =
    | No_cells : 'a option cells
    | One_cell : 'a ColumnType.Cell.t * 'b cells -> ('a -> 'b) cells

  type ('p, 'v) bound_environment =
    { parameters : 'p cells;
      variables : 'v Ref.hlist;
      binders : binder list
    }

  type ('p, 'v) with_parameters =
    { environment : ('p, 'v) bound_environment;
      iterators : level array;
      last_iterator : int
    }

  type 'v t = (unit option, 'v) with_parameters

  let get_variables query = Ref.get_hlist query.environment.variables

  let iterator_ex _column it =
    Level { iterator = it; cell = None; output = Ignore; instruction = Accept }

  type constant_level =
    { order : int;
      mutable extra_bindings : level list
    }

  type 'a variable_level =
    { order : int;
      mutable extra_bindings : level list;
      column : 'a ColumnType.t;
      name : string;
      mutable iterators : 'a Table.Iterator.t list;
      mutable cell : 'a ColumnType.Cell.t option;
      (* [cell] is unused for constant bindings *)
      mutable output : 'a ref option;
      (* [output] is only for variable bindings *)
      mutable instruction : outcome instruction
    }

  type pre_level =
    | Constant_level of constant_level
    | Variable_level : 'a variable_level -> pre_level

  let order = function
    | Constant_level { order; _ } -> order
    | Variable_level { order; _ } -> order

  let add_extra_binding level binding =
    match level with
    | Constant_level level ->
      level.extra_bindings <- binding :: level.extra_bindings
    | Variable_level level ->
      level.extra_bindings <- binding :: level.extra_bindings

  let print_binding ppf { name; order; _ } =
    Format.fprintf ppf "Variable '%s' (with order %d)" name order

  let to_level = function
    | Constant_level binding -> binding.extra_bindings
    | Variable_level binding -> (
      let levels = binding.extra_bindings in
      match binding.iterators with
      | [] ->
        Misc.fatal_errorf "%a always appears after variables with lower order."
          print_binding binding
      | _ :: _ ->
        let output =
          match binding.output with None -> Ignore | Some ref -> Set_ref ref
        in
        Level
          { iterator = Iterator.create binding.iterators;
            cell = binding.cell;
            output;
            instruction = binding.instruction
          }
        :: levels)

  let get_or_create_cell binding =
    match binding.cell with
    | None ->
      let cell = ColumnType.Cell.create binding.column in
      binding.cell <- Some cell;
      cell
    | Some cell -> cell

  let get_or_create_output binding =
    match binding.output with
    | None ->
      let output = ColumnType.create_ref binding.column in
      binding.output <- Some output;
      output
    | Some output -> output

  type binding_info =
    | Binding_info : 'a variable_level -> binding_info
    | Existential of { order : int }

  type bindings =
    { constant_binding_info : constant_level;
      all_bindings : (string, binding_info) Hashtbl.t
    }

  let create_empty_binding ~name ~order column =
    { column;
      order;
      name;
      iterators = [];
      cell = None;
      output = None;
      extra_bindings = [];
      instruction = Accept
    }

  let create_bindings () =
    { constant_binding_info = { order = 0; extra_bindings = [] };
      all_bindings = Hashtbl.create 17
    }

  let ordered_bindings bindings =
    let ordered =
      Hashtbl.fold
        (fun _ info bindings ->
          match info with
          | Binding_info binding -> Variable_level binding :: bindings
          | Existential _ -> bindings)
        bindings.all_bindings
        [Constant_level bindings.constant_binding_info]
    in
    let ordered = Array.of_list ordered in
    Array.fast_sort (fun b1 b2 -> Int.compare (order b1) (order b2)) ordered;
    ordered

  let create_variable (type a) bindings var (ty : a ColumnType.t) :
      a variable_level =
    match Hashtbl.find_opt bindings.all_bindings var with
    | Some _ -> Misc.fatal_errorf "Variable '%s' is already defined" var
    | None ->
      let order = Hashtbl.length bindings.all_bindings + 1 in
      let binding = create_empty_binding ~name:var ~order ty in
      Hashtbl.add bindings.all_bindings var (Binding_info binding);
      binding

  let record_existential bindings var =
    match Hashtbl.find_opt bindings.all_bindings var with
    | Some _ -> Misc.fatal_errorf "Variable '%s' is already defined" var
    | None ->
      let order = Hashtbl.length bindings.all_bindings + 1 in
      Hashtbl.add bindings.all_bindings var (Existential { order })

  let get_binding (type a) bindings var (ty : a ColumnType.t) : a variable_level
      =
    match Hashtbl.find_opt bindings.all_bindings var with
    | Some (Binding_info binding) -> (
      let column = binding.column in
      match ColumnType.provably_equal ty column with
      | Some Equal -> binding
      | None ->
        Misc.fatal_errorf "Incompatible types for variable '%s': '%a' and '%a'"
          var ColumnType.print ty ColumnType.print column)
    | Some (Existential { order }) ->
      let binding = create_empty_binding ~name:var ~order ty in
      Hashtbl.replace bindings.all_bindings var (Binding_info binding);
      binding
    | None ->
      Misc.fatal_errorf "Variable '%s' is used (with type '%a') but not bound."
        var ColumnType.print ty

  let rec bind_atom :
      type a.
      bindings ->
      pre_level ->
      a ColumnType.hlist ->
      a Term.hlist ->
      a Table.Iterator.hlist ->
      unit =
   fun bindings last_binding schema args iterators ->
    match schema, args, iterators with
    | [], [], [] -> ()
    | ( this_column :: other_columns,
        this_arg :: other_args,
        this_iterator :: other_iterators ) -> (
      match this_arg with
      | Constant cte ->
        let cell = ColumnType.Cell.create this_column in
        ColumnType.Cell.set cell cte;
        let filter = Table.cell_iterator cell in
        let iterator = Iterator.create [this_iterator; filter] in
        add_extra_binding last_binding (iterator_ex this_column iterator);
        bind_atom bindings last_binding other_columns other_args other_iterators
      | Variable var ->
        let var_info = get_binding bindings var this_column in
        if var_info.order >= order last_binding
        then (
          var_info.iterators <- this_iterator :: var_info.iterators;
          bind_atom bindings (Variable_level var_info) other_columns other_args
            other_iterators)
        else
          let cell = get_or_create_cell var_info in
          let filter = Table.cell_iterator cell in
          let iterator = Iterator.create [this_iterator; filter] in
          add_extra_binding last_binding (iterator_ex this_column iterator);
          bind_atom bindings last_binding other_columns other_args
            other_iterators)

  type ('p, 'v) raw_query =
    { environment : ('p, 'v) bound_environment;
      bindings : bindings
    }

  let rec find_last_binding0 :
      type a.
      bindings -> pre_level -> a ColumnType.hlist -> a Term.hlist -> pre_level =
   fun bindings last_level schema args ->
    match schema, args with
    | [], [] -> last_level
    | column :: schema, arg :: args -> (
      match arg with
      | Constant _ -> find_last_binding0 bindings last_level schema args
      | Variable var ->
        let binding = get_binding bindings var column in
        if binding.order >= order last_level
        then find_last_binding0 bindings (Variable_level binding) schema args
        else find_last_binding0 bindings last_level schema args)

  let find_last_binding bindings schema args =
    find_last_binding0 bindings (Constant_level bindings.constant_binding_info)
      schema args

  let rec process_variables :
      type a. bindings -> a Variable.hlist -> a Ref.hlist =
   fun bindings variables ->
    match variables with
    | [] -> []
    | (var, column) :: other_variables ->
      let binding = create_variable bindings var column in
      get_or_create_output binding :: process_variables bindings other_variables

  let rec process_parameters : type a. bindings -> a Variable.hlist -> a cells =
   fun bindings parameters ->
    match parameters with
    | [] -> No_cells
    | (param, ty) :: other_params ->
      let binding = create_variable bindings param ty in
      let cell = get_or_create_cell binding in
      let filter = Table.cell_iterator cell in
      binding.iterators <- filter :: binding.iterators;
      One_cell (cell, process_parameters bindings other_params)

  let populate_bindings ~parameters ~variables ?(existentials = []) bindings =
    (* Compute the cells in which to pass parameter values. *)
    let parameter_cells = process_parameters bindings parameters in
    (* Create bindings for variables, in order. *)
    let output = process_variables bindings variables in
    List.iter (record_existential bindings) existentials;
    parameter_cells, output

  let rec compile_atom :
      type a. bindings -> a ColumnType.hlist -> a Term.hlist -> a Ref.hlist =
   fun bindings schema vars ->
    match schema, vars with
    | [], [] -> []
    | column :: schema, term :: terms -> (
      match term with
      | Constant cte -> ref cte :: compile_atom bindings schema terms
      | Variable var ->
        let binding = get_binding bindings var column in
        get_or_create_output binding :: compile_atom bindings schema terms)

  let create_raw bindings ~parameters:parameter_cells ~variables:output
      ?(negate = []) (atoms : unit atom list) : _ =
    let binders =
      List.fold_left
        (fun binders (Atom (id, args)) ->
          let handler, iterators = Table.iterator id in
          bind_atom bindings (Constant_level bindings.constant_binding_info)
            (Table.Id.schema id) args iterators;
          Bind (id, handler) :: binders)
        [] atoms
    in
    List.iter
      (fun (Atom (id, args)) ->
        let schema = Table.Id.schema id in
        let refs = compile_atom bindings schema args in
        match find_last_binding bindings schema args with
        | Constant_level _ ->
          Misc.fatal_error
            "Negation of terms involving only constants is not supported."
        | Variable_level level ->
          level.instruction <- Ite (Mem (Id id, refs), Reject, level.instruction))
      negate;
    { environment =
        { parameters = parameter_cells; variables = output; binders };
      bindings
    }

  exception Last_variable of int

  let make_iterators bindings =
    let ordered = ordered_bindings bindings in
    let last_order =
      try
        for i = Array.length ordered - 1 downto 0 do
          match ordered.(i) with
          | Constant_level _ -> raise (Last_variable i)
          | Variable_level level -> (
            match[@warning "-fragile-match"]
              level.cell, level.output, level.instruction
            with
            | None, None, Accept -> ()
            | _ -> raise (Last_variable i))
        done;
        -1
      with Last_variable i -> i
    in
    let last_iterator = ref (-1) in
    let all_iterators = ref ([] : _ list) in
    Array.iter
      (fun level ->
        if order level = last_order
        then last_iterator := List.length !all_iterators;
        all_iterators := List.rev_append (to_level level) !all_iterators)
      ordered;
    Array.of_list (List.rev !all_iterators), !last_iterator

  let from_raw { environment; bindings } =
    let iterators, last_iterator = make_iterators bindings in
    { environment; iterators; last_iterator }

  let create_with_parameters ~parameters variables ?negate f =
    let bindings = create_bindings () in
    let cells, output = populate_bindings ~parameters ~variables bindings in
    let query = f (Term.variables parameters) (Term.variables variables) in
    let negate =
      Option.map
        (fun f -> f (Term.variables parameters) (Term.variables variables))
        negate
    in
    from_raw
      (create_raw bindings ~parameters:cells ~variables:output ?negate query)

  let create variables ?negate f =
    create_with_parameters ~parameters:[] variables
      ?negate:
        (Option.map (fun f ([] : _ option Term.hlist) vars -> f vars) negate)
      (fun [] vars -> f vars)

  let rec bind_parameters0 : type a. a cells -> a Constant.hlist -> unit =
   fun cells values ->
    match cells, values with
    | No_cells, [] -> ()
    | One_cell (cell, cells'), value :: values' ->
      ColumnType.Cell.set cell value;
      bind_parameters0 cells' values'

  let bind_parameters environment values =
    bind_parameters0 environment.parameters values

  let rec advance db arr depth (Level level) =
    match Iterator.current level.iterator with
    | Some current_key -> (
      run_handler current_key level.output;
      match run_instruction db level.instruction with
      | Reject ->
        Iterator.advance level.iterator;
        advance db arr depth (Level level)
      | Accept ->
        (match level.cell with
        | Some cell -> ColumnType.Cell.set cell current_key
        | None -> ());
        Iterator.accept level.iterator;
        let next_depth = depth + 1 in
        if next_depth = Array.length arr
        then depth
        else
          let (Level next_level) = arr.(next_depth) in
          Iterator.init next_level.iterator;
          advance db arr next_depth (Level next_level))
    | None ->
      if depth = 0
      then -1
      else
        let prev_depth = depth - 1 in
        let (Level prev_level) = arr.(prev_depth) in
        Iterator.advance prev_level.iterator;
        advance db arr prev_depth (Level prev_level)

  let bind_environment environment database =
    List.iter
      (fun (Bind (id, handler)) ->
        let table = Database.get_table database id in
        Table.bind id table handler)
      environment.binders

  let[@inline] with_naive environment database acc f =
    bind_environment environment database;
    f acc

  let[@inline] with_seminaive ~diff:new_facts environment database f acc =
    let rec loop cnt acc =
      let cnt_this_run = ref 0 in
      List.iter
        (fun (Bind (relation, handler)) ->
          let table = Database.get_table database relation in
          let diff = Database.get_table new_facts relation in
          if Table.is_empty relation diff
          then Table.bind relation table handler
          else (
            if !cnt_this_run = cnt
            then Table.bind relation diff handler
            else Table.bind relation table handler;
            incr cnt_this_run))
        environment.binders;
      if cnt < !cnt_this_run then loop (cnt + 1) (f acc) else acc
    in
    loop 0 acc

  let[@inline] run_fold db (query : (_, _) with_parameters) f init =
    let (Level first_level) = query.iterators.(0) in
    Iterator.init first_level.iterator;
    let last = query.last_iterator in
    let rec loop depth acc =
      if depth < 0
      then acc
      else
        let acc = f (get_variables query) acc in
        if last < 0
        then acc
        else
          let (Level last_level) = query.iterators.(last) in
          Iterator.advance last_level.iterator;
          let depth = advance db query.iterators last (Level last_level) in
          loop depth acc
    in
    loop (advance db query.iterators 0 (Level first_level)) init

  let run_iter db query f = run_fold db query (fun keys () -> f keys) ()

  let fold_with_parameters (query : (_, _) with_parameters) parameters database
      ~init ~f =
    bind_parameters query.environment parameters;
    with_naive query.environment database init (run_fold database query f)

  let fold (query : _ t) database ~init ~f =
    fold_with_parameters query [] database ~init ~f

  let iter_with_parameters (query : (_, _) with_parameters) parameters database
      ~f =
    bind_parameters query.environment parameters;
    with_naive query.environment database () (fun () ->
        run_iter database query f)

  let iter (query : _ t) database ~f = iter_with_parameters query [] database ~f
end

module Rule = struct
  type t =
    | Rule :
        { query : unit option Cursor.t;
          table_id : ('t, 'k, 'v) Table.Id.t;
          arguments : 'k Ref.hlist;
          value : 'v option
        }
        -> t

  let create ~variables ?(existentials = []) conclusion value ?negate hypotheses
      =
    let bindings = Cursor.create_bindings () in
    let parameters, variables =
      Cursor.populate_bindings ~parameters:[] ~variables:[]
        ~existentials:(variables @ existentials) bindings
    in
    let raw =
      Cursor.create_raw bindings ~parameters ~variables ?negate hypotheses
    in
    let (Atom (table, args)) = conclusion in
    let arguments =
      Cursor.compile_atom raw.bindings (Table.Id.schema table) args
    in
    let query = Cursor.from_raw raw in
    Rule { query; table_id = table; arguments; value }

  let delete ~variables ?existentials conclusion ?negate hypotheses =
    create ~variables ?existentials conclusion None ?negate hypotheses

  let create ~variables ?existentials conclusion ?negate hypotheses =
    create ~variables ?existentials conclusion (Some ()) ?negate hypotheses

  let rec saturate ?diff rules db =
    let run_step new_db (Rule { table_id; arguments; value; query }) =
      let table = ref (Database.get_table new_db table_id) in
      let env = query.Cursor.environment in
      (match value with
      | Some value -> (
        let[@inline] step_add () =
          Cursor.run_iter db query (fun [] ->
              table := Table.add table_id (Ref.get_hlist arguments) value !table)
        in
        match diff with
        | None -> Cursor.with_naive env db () step_add
        | Some diff -> Cursor.with_seminaive ~diff env db step_add ())
      | None -> (
        let[@inline] step_remove () =
          Cursor.run_iter db query (fun [] ->
              table := Table.remove_refs table_id arguments !table)
        in
        match diff with
        | None -> Cursor.with_naive env db () step_remove
        | Some diff -> Cursor.with_seminaive ~diff env db step_remove ()));
      Database.set_table new_db table_id !table
    in
    let new_db = List.fold_left run_step db rules in
    if new_db == db
    then new_db
    else
      let diff = Database.cut new_db ~cut_after:(Database.current_level db) in
      saturate ~diff rules new_db
end

module Schedule = struct
  type t =
    | Fixpoint of t
    | Saturate of Rule.t list * int Int.Map.t
    | List of t list

  let fixpoint schedule = Fixpoint schedule

  let list schedules = List schedules

  let saturate rules = Saturate (rules, Int.Map.empty)

  let rec run db schedule : _ * t =
    match schedule with
    | Saturate (rules, last_ts) ->
      let new_db =
        if Int.Map.is_empty last_ts
        then Rule.saturate ?diff:None rules db
        else Rule.saturate ~diff:(Database.cut db ~cut_after:last_ts) rules db
      in
      new_db, Saturate (rules, Database.current_level new_db)
    | Fixpoint schedule ->
      let new_db, schedule = run db schedule in
      if new_db == db
      then new_db, Fixpoint schedule
      else run new_db (Fixpoint schedule)
    | List schedules ->
      let new_db, schedules = List.fold_left_map run db schedules in
      new_db, List schedules

  let run schedule db =
    let db', _schedule' = run db schedule in
    db'
end

type database = Database.t

let empty = Database.empty

let create_relation = Table.Id.create_trie

let add_fact (Table.Id.Id id) args db =
  Database.set_table db id (Table.add id args () (Database.get_table db id))

let print = Database.print

type 'k relation = ('k, unit) Table.Id.poly

type 'a rel1 = ('a -> unit option) relation

type ('a, 'b) rel2 = ('a -> 'b -> unit option) relation

type ('a, 'b, 'c) rel3 = ('a -> 'b -> 'c -> unit option) relation
