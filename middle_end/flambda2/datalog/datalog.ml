[@@@flambda.o3]

module Id = struct
  module T = struct
    include Int

    let print = Numbers.Int.print
  end

  include T
  module Tree = Patricia_tree.Make (T)
  module Map = Tree.Map
end

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

type _ handler =
  | Ignore : 'a handler
  | Set_ref : 'a ref -> 'a handler

let run_handler (type a) (value : a) (handler : a handler) =
  match handler with Ignore -> () | Set_ref r -> r := value

module type Iterator = sig
  type 'a t

  val current : 'a t -> 'a Leapfrog.position

  val advance : 'a t -> unit

  val seek : 'a t -> 'a -> unit

  val init : 'a t -> unit

  val accept : 'a t -> unit

  val equal_key : 'a t -> 'a -> 'a -> bool

  val compare_key : 'a t -> 'a -> 'a -> int
end

module type Heterogenous = sig
  type 'a t

  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : 'a t * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist
end

module Constant = struct
  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : 'a * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist
end

module Ref = struct
  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : 'a ref * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist

  let rec get_hlist : type a. (a, unit) hlist -> (a, unit) Constant.hlist =
    function
    | [] -> []
    | r :: rs -> !r :: get_hlist rs
end

module Trie : sig
  type ('m, 'k, 'v) is_map

  val is_map : ('v Id.Map.t, int, 'v) is_map

  type ('t, 'k, 'v) is_trie

  val value_is_trie : ('a, unit, 'a) is_trie

  val map_is_trie :
    ('t, 'a, 's) is_map -> ('s, 'b, 'v) is_trie -> ('t, 'a -> 'b, 'v) is_trie

  val empty : ('t, 'k, 'v) is_trie -> 't

  module Map_iterator : Iterator

  module Iterator : sig
    type _ t =
      | [] : unit t
      | ( :: ) : 'a Map_iterator.t * 'b t -> ('a -> 'b) t
  end

  type 'k iterator = 'k Iterator.t

  val map_iterator :
    ('m, 'k, 'v) is_map -> 'm ref -> 'v handler -> 'k Map_iterator.t

  val trie_add :
    ('t, 'k, 'v) is_trie -> ('k, unit) Constant.hlist -> 'v -> 't -> 't

  val remove : ('t, 'k, 'v) is_trie -> ('k, unit) Constant.hlist -> 't -> 't

  val find_opt :
    ('t, 'k, 'v) is_trie -> ('k, unit) Constant.hlist -> 't -> 'v option

  val find_opt_refs :
    ('t, 'k, 'v) is_trie -> ('k, unit) Ref.hlist -> 't -> 'v option

  val iterator : ('m, 'k, 'v) is_trie -> 'v handler -> 'm handler * 'k iterator

  val fold :
    ('t, 'k, 'v) is_trie ->
    (('k, unit) Constant.hlist -> 'v -> 'a -> 'a) ->
    't ->
    'a ->
    'a
end = struct
  type ('m, 'k, 'v) is_map = Is_map : ('v Id.Map.t, int, 'v) is_map

  let is_map = Is_map

  type (_, _, _) is_trie =
    | Value_is_trie : ('a, unit, 'a) is_trie
    | Map_is_trie :
        ('t, 'a, 's) is_map * ('s, 'b, 'v) is_trie
        -> ('t, 'a -> 'b, 'v) is_trie

  let value_is_trie = Value_is_trie

  let map_is_trie is_map is_trie = Map_is_trie (is_map, is_trie)

  let empty : type t k v. (t, k, v) is_trie -> t = function
    | Value_is_trie -> invalid_arg "Trie.empty"
    | Map_is_trie (Is_map, _) -> Id.Map.empty

  module Map_iterator = struct
    type _ t =
      | Iterator :
          { mutable iterator : 'v Id.Map.iterator;
            map : 'v Id.Map.t ref;
            handler : 'v handler
          }
          -> int t

    let equal_key (type a) (Iterator _ : a t) : a -> a -> bool = Int.equal

    let compare_key (type a) (Iterator _ : a t) : a -> a -> int = Int.compare

    let current (type a) (Iterator i : a t) : a Leapfrog.position =
      match Id.Map.current i.iterator with
      | Some (key, _) -> Leapfrog.Key key
      | None -> Leapfrog.At_end

    let advance (type a) (Iterator i : a t) : unit =
      i.iterator <- Id.Map.advance i.iterator

    let seek (type a) (Iterator i : a t) (k : a) : unit =
      i.iterator <- Id.Map.seek i.iterator k

    let init (type a) (Iterator i : a t) : unit =
      i.iterator <- Id.Map.iterator !(i.map)

    let accept (type a) (Iterator i : a t) : unit =
      match Id.Map.current i.iterator with
      | None -> invalid_arg "accept: iterator must have a value"
      | Some (_, value) -> (
        match i.handler with Ignore -> () | Set_ref r -> r := value)
  end

  let make_cell (type m k v) (Is_map : (m, k, v) is_map) : m ref =
    ref Id.Map.empty

  let map_iterator (type m k v) (Is_map : (m, k, v) is_map) (cell : m ref)
      (handler : v handler) : k Map_iterator.t =
    Map_iterator.Iterator
      { iterator = Id.Map.iterator Id.Map.empty; map = cell; handler }

  module Iterator = struct
    type _ t =
      | [] : unit t
      | ( :: ) : 'a Map_iterator.t * 'b t -> ('a -> 'b) t
  end

  type 'a iterator = 'a Iterator.t

  let rec iterator :
      type m k v. (m, k, v) is_trie -> v handler -> m handler * k Iterator.t =
   fun is_trie handler ->
    match is_trie with
    | Value_is_trie -> handler, []
    | Map_is_trie (is_map, is_trie) ->
      let next_handler, next_iterators = iterator is_trie handler in
      let this_cell = make_cell is_map in
      let this_iterator = map_iterator is_map this_cell next_handler in
      Set_ref this_cell, this_iterator :: next_iterators

  let rec fold :
      type t k v a.
      (t, k, v) is_trie ->
      ((k, unit) Constant.hlist -> v -> a -> a) ->
      t ->
      a ->
      a =
   fun w f t acc ->
    match w with
    | Value_is_trie -> f [] t acc
    | Map_is_trie (Is_map, w') ->
      Id.Map.fold
        (fun k t acc -> fold w' (fun k' v acc -> f (k :: k') v acc) t acc)
        t acc

  let rec find_opt :
      type t k v. (t, k, v) is_trie -> (k, unit) Constant.hlist -> t -> v option
      =
   fun w k t ->
    match k, w with
    | [], Value_is_trie -> Some t
    | k :: k', Map_is_trie (Is_map, w') -> (
      match Id.Map.find_opt k t with Some s -> find_opt w' k' s | None -> None)

  let rec find_opt_refs :
      type t k v. (t, k, v) is_trie -> (k, unit) Ref.hlist -> t -> v option =
   fun w k t ->
    match k, w with
    | [], Value_is_trie -> Some t
    | k :: k', Map_is_trie (Is_map, w') -> (
      let k = !k in
      match Id.Map.find_opt k t with
      | Some s -> find_opt_refs w' k' s
      | None -> None)

  let rec singleton :
      type t k v. (t, k, v) is_trie -> (k, unit) Constant.hlist -> v -> t =
   fun w k v ->
    match k, w with
    | [], Value_is_trie -> v
    | k :: k', Map_is_trie (Is_map, w') ->
      Id.Map.singleton k (singleton w' k' v)

  let rec trie_add :
      type t k v. (t, k, v) is_trie -> (k, unit) Constant.hlist -> v -> t -> t =
   fun w inputs output t ->
    match inputs, w with
    | [], Value_is_trie -> output
    | first_input :: other_inputs, Map_is_trie (Is_map, w') -> (
      match Id.Map.find_opt first_input t with
      | Some m -> Id.Map.add first_input (trie_add w' other_inputs output m) t
      | None -> Id.Map.add first_input (singleton w' other_inputs output) t)

  let is_empty : type t k v. (t, k, v) is_trie -> t -> bool =
   fun w t ->
    match w with
    | Value_is_trie -> false
    | Map_is_trie (Is_map, _) -> Id.Map.is_empty t

  let rec remove0 :
      type t k v.
      (t, k, v) is_trie ->
      t Id.Map.t ->
      int ->
      (k, unit) Constant.hlist ->
      t ->
      t Id.Map.t =
   fun w t k k' m ->
    match k', w with
    | [], Value_is_trie -> Id.Map.remove k t
    | a :: b, Map_is_trie (Is_map, w') -> (
      match Id.Map.find_opt a m with
      | None -> t
      | Some m' ->
        let m' = remove0 w' m a b m' in
        if is_empty w m' then Id.Map.remove k t else Id.Map.add k m' t)

  let remove :
      type t k v. (t, k, v) is_trie -> (k, unit) Constant.hlist -> t -> t =
   fun w k t ->
    match k, w with
    | [], Value_is_trie -> t
    | k :: k', Map_is_trie (Is_map, w') -> (
      match Id.Map.find_opt k t with None -> t | Some m -> remove0 w' t k k' m)
end

module ColumnType : sig
  include Heterogenous

  type 'a column = 'a t

  val print : Format.formatter -> 'a t -> unit

  val printer : 'a t -> Format.formatter -> 'a -> unit

  val make : string -> print:(Format.formatter -> int -> unit) -> int t

  val int : int t

  module Cell : sig
    type 'a t

    val create : 'a column -> 'a t

    val set : 'a column -> 'a t -> 'a -> unit

    val to_iterator : 'a column -> 'a t -> 'a Trie.Map_iterator.t
  end

  type (_, _) any_trie =
    | Any_trie : ('t, 'k, 'v) Trie.is_trie -> ('k, 'v) any_trie

  val is_trie : ('a, unit) hlist -> ('a, 'b) any_trie

  val provably_equal : 'a t -> 'b t -> ('a, 'b) Type.eq option

  val create_ref : 'a t -> 'a ref
end = struct
  type 'a t =
    { id : 'a Type.Id.t;
      name : string;
      print : Format.formatter -> 'a -> unit;
      is_int : ('a, int) Type.eq
    }

  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : 'a t * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist

  let is_int { is_int; _ } = is_int

  let print ppf { id; name; _ } =
    Format.fprintf ppf "%s/%d" name (Type.Id.uid id)

  let printer { print; _ } = print

  let make name ~print = { id = Type.Id.make (); name; print; is_int = Equal }

  let int = make "int" ~print:Format.pp_print_int

  let create_ref (type a) ({ is_int = Equal; _ } : a t) : a ref = ref 0

  let provably_equal t1 t2 = Type.Id.provably_equal t1.id t2.id

  type 'a column = 'a t

  type (_, _) any_trie =
    | Any_trie : ('t, 'k, 'v) Trie.is_trie -> ('k, 'v) any_trie

  let rec is_trie : type a b. (a, unit) hlist -> (a, b) any_trie =
   fun s ->
    match s with
    | [] -> Any_trie Trie.value_is_trie
    | { is_int = Equal; _ } :: s' ->
      let (Any_trie t') = is_trie s' in
      Any_trie (Trie.map_is_trie Trie.is_map t')

  module Cell : sig
    type 'a t

    val create : 'a column -> 'a t

    val set : 'a column -> 'a t -> 'a -> unit

    val to_iterator : 'a column -> 'a t -> 'a Trie.Map_iterator.t
  end = struct
    type 'a t = Cell : unit Id.Map.t ref -> 'a t [@@unboxed]

    let create _ = Cell (ref Id.Map.empty)

    let set (type a) (column : a column) (Cell cell : a t) (v : a) : unit =
      let Equal = is_int column in
      cell := Id.Map.singleton v ()

    let to_iterator (type a) (column : a column) (Cell cell : a t) :
        a Trie.Map_iterator.t =
      let Equal = is_int column in
      Trie.map_iterator Trie.is_map cell Ignore
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

  let current (type a) ({ iterators; at_end } : a t) : a Leapfrog.position =
    if at_end
    then Leapfrog.At_end
    else Iterator.current iterators.(Array.length iterators - 1)

  let rec search : type a. a Iterator.t array -> int -> a -> a Leapfrog.position
      =
   fun iterators index_of_lowest_key highest_key ->
    let iterator_with_lowest_key = iterators.(index_of_lowest_key) in
    let equal = Iterator.equal_key iterator_with_lowest_key in
    match Iterator.current iterator_with_lowest_key with
    | At_end -> Leapfrog.At_end
    | Key lowest_key when equal lowest_key highest_key ->
      (* All iterators are on the same key. *)
      Leapfrog.Key lowest_key
    | At_start | Key _ -> (
      Iterator.seek iterator_with_lowest_key highest_key;
      match Iterator.current iterator_with_lowest_key with
      | At_start -> Misc.fatal_error "Impossibru"
      | At_end -> Leapfrog.At_end
      | Key new_highest_key ->
        search iterators
          ((index_of_lowest_key + 1) mod Array.length iterators)
          new_highest_key)

  let repair (type a) ({ iterators; at_end } as j : a t) =
    assert (not at_end);
    if Array.length iterators > 1
    then
      let iterator = iterators.(Array.length iterators - 1) in
      match Iterator.current iterator with
      | At_start -> assert false
      | At_end -> j.at_end <- true
      | Key highest_key -> (
        match search iterators 0 highest_key with
        | At_end -> j.at_end <- true
        | At_start | Key _ -> ())

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
          | At_end -> raise Empty_iterator
          | At_start | Key _ -> ())
        iterators;
      Array.sort
        (fun (it1 : a Iterator.t) (it2 : a Iterator.t) ->
          let compare = Iterator.compare_key it1 in
          Leapfrog.compare_position compare (Iterator.current it1)
            (Iterator.current it2))
        iterators;
      j.at_end <- false;
      repair j
    with Empty_iterator -> j.at_end <- true

  let accept (type a) ({ iterators; at_end } : a t) =
    if at_end then invalid_arg "accept";
    Array.iter Iterator.accept iterators

  let equal_key { iterators; _ } = Iterator.equal_key iterators.(0)

  let compare_key { iterators; _ } = Iterator.compare_key iterators.(0)

  let create (iterators : _ Iterator.t list) : _ t =
    match iterators with
    | [] -> invalid_arg "join_iterators"
    | _ -> { iterators = Array.of_list iterators; at_end = false }
end
[@@inline always]

module Table = struct
  type ('t, 'k, 'v) is_table =
    { id : ('t -> 'k -> 'v) Type.Id.t;
      name : string;
      schema : ('k, unit) ColumnType.hlist;
      is_trie : ('t, 'k, int) Trie.is_trie
    }

  type ('t, 'k, 'v) table =
    { trie : 't;
      facts : (('k, unit) Constant.hlist * 'v) Id.Map.t;
      last_fact_id : int;
      is_table : ('t, 'k, 'v) is_table
    }

  let is_trie { is_trie; _ } = is_trie

  let print_is_table ppf is_table =
    Format.fprintf ppf "%s/%d" is_table.name (Type.Id.uid is_table.id)

  let rec print_row :
      type a.
      (a, unit) ColumnType.hlist ->
      Format.formatter ->
      (a, unit) Constant.hlist ->
      unit =
   fun schema ppf ->
    match schema with
    | [] -> fun [] -> ()
    | [k] -> fun [x] -> ColumnType.printer k ppf x
    | k :: k' ->
      fun (x :: y) ->
        Format.fprintf ppf "%a,@ %a" (ColumnType.printer k) x (print_row k') y

  let print_table is_table ppf table =
    Trie.fold is_table.is_trie
      (fun keys _ () ->
        Format.fprintf ppf "@[%a(%a).@]@ " print_is_table is_table
          (print_row is_table.schema)
          keys)
      table.trie ()

  let print is_table ppf table =
    let header = Format.asprintf "%a" print_is_table is_table in
    Format.fprintf ppf "@[<v>%s@ %s@ %a@]" header
      (String.make (String.length header) '=')
      (print_table is_table) table

  let create ~name is_trie schema =
    { id = Type.Id.make (); name; is_trie; schema }

  let is_empty _ table = Id.Map.is_empty table.facts

  type ('t, 'k, 'v) t = ('t, 'k, 'v) is_table

  let[@inline] uid { id; _ } = Type.Id.uid id

  let[@inline] provably_equal r1 r2 = Type.Id.provably_equal r1.id r2.id

  let add keys value table =
    let is_trie = is_trie table.is_table in
    match Trie.find_opt is_trie keys table.trie with
    | Some _ -> table
    | None ->
      let last_fact_id = table.last_fact_id + 1 in
      let trie = Trie.trie_add is_trie keys last_fact_id table.trie in
      let facts = Id.Map.add last_fact_id (keys, value) table.facts in
      { last_fact_id; trie; facts; is_table = table.is_table }

  let remove keys table =
    let is_trie = is_trie table.is_table in
    match Trie.find_opt is_trie keys table.trie with
    | None -> table
    | Some fact_id ->
      let trie = Trie.remove is_trie keys table.trie in
      let facts = Id.Map.remove fact_id table.facts in
      { last_fact_id = table.last_fact_id;
        trie;
        facts;
        is_table = table.is_table
      }

  let _fold { is_trie; _ } f keys acc = Trie.fold is_trie f keys acc

  let empty id =
    { trie = Trie.empty id.is_trie;
      facts = Id.Map.empty;
      last_fact_id = -1;
      is_table = id
    }

  let schema { schema; _ } = schema

  let iterator (type m k v) (id : (m, k, v) t) = Trie.iterator id.is_trie

  let cut table ~cut_after =
    let _, _, delta_facts = Id.Map.split cut_after table.facts in
    let is_trie = is_trie table.is_table in
    let trie =
      Id.Map.fold
        (fun fact_id (k, _) trie -> Trie.trie_add is_trie k fact_id trie)
        delta_facts (Trie.empty is_trie)
    in
    { facts = delta_facts;
      last_fact_id = table.last_fact_id;
      trie;
      is_table = table.is_table
    }
end

module Iterator = Joined_iterator (Trie.Map_iterator)

type (_, _) cells =
  | No_cells : ('a, 'a) cells
  | One_cell :
      'a ColumnType.t * 'a ColumnType.Cell.t * ('b, 'c) cells
      -> ('a -> 'b, 'c) cells

module Relation = struct
  type (_, _) t = Table : ('t, 'k, 'v) Table.t -> ('k, 'v) t [@@unboxed]

  let create ~name schema =
    let (Any_trie is_trie) = ColumnType.is_trie schema in
    Table (Table.create ~name is_trie schema)

  let add_fact (type t k v) (id : (t, k, v) Table.t)
      (keys : (k, unit) Constant.hlist) (value : v) table =
    let is_trie = Table.is_trie id in
    match Trie.find_opt is_trie keys table.Table.trie with
    | Some _ -> table
    | None ->
      let last_fact_id = table.Table.last_fact_id + 1 in
      let trie = Trie.trie_add is_trie keys last_fact_id table.Table.trie in
      let facts = Id.Map.add last_fact_id (keys, value) table.Table.facts in
      { Table.last_fact_id; trie; facts; is_table = table.Table.is_table }
end

module Database = struct
  type binding = Binding : ('t, 'k, 'v) Table.table -> binding [@@unboxed]

  type raw = { tables : binding Id.Map.t } [@@unboxed]

  let print ppf { tables } =
    Format.fprintf ppf "@[<v>";
    Id.Map.iter
      (fun _ (Binding table) ->
        Table.print table.Table.is_table ppf table;
        Format.fprintf ppf "@ ")
      tables;
    Format.fprintf ppf "@]"

  let empty = { tables = Id.Map.empty }

  let get_table (type t k v) { tables } (id : (t, k, v) Table.t) :
      (t, k, v) Table.table =
    match Id.Map.find_opt (Table.uid id) tables with
    | Some (Binding table) -> (
      match Table.provably_equal id table.Table.is_table with
      | Some Equal -> table
      | None -> invalid_arg "get_table")
    | None -> Table.empty id

  let set_table (type t k v) ({ tables } as db) (id : (t, k, v) Table.t)
      (table : (t, k, v) Table.table) =
    let tables' =
      if Table.is_empty id table
      then
        if Id.Map.mem (Table.uid id) tables
        then Id.Map.remove (Table.uid id) tables
        else tables
      else
        match Id.Map.find_opt (Table.uid id) tables with
        | None -> Id.Map.add (Table.uid id) (Binding table) tables
        | Some existing ->
          if Binding table == existing
          then tables
          else Id.Map.add (Table.uid id) (Binding table) tables
    in
    if tables == tables' then db else { tables = tables' }

  let current_level db =
    Id.Map.map (fun (Binding table) -> table.last_fact_id) db.tables

  let cut db ~cut_after:level =
    let tables =
      Id.Map.mapi
        (fun tid (Binding table) ->
          match Id.Map.find_opt tid level with
          | Some cut_after -> Binding (Table.cut table ~cut_after)
          | None -> Binding table)
        db.tables
    in
    { tables }
end

type incremental =
  { database : Database.raw;
    new_facts : Database.raw
  }

module Variable = struct
  type t = string

  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : (t * 'a ColumnType.t) * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist
end

module Term = struct
  type 'a t =
    | Variable of Variable.t
    | Constant of 'a

  let variable v = Variable v

  let constant c = Constant c

  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : 'a t * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist

  let rec variables : type a b. (a, b) Variable.hlist -> (a, b) hlist = function
    | [] -> []
    | (var, _) :: vars -> Variable var :: variables vars
end

module Atom = struct
  type _ t = Atom : ('a, 'b) Relation.t * ('a, unit) Term.hlist -> 'b t

  let create relation args = Atom (relation, args)
end

module Query = struct
  type _ instruction =
    | Accept : bool instruction
    | Reject : bool instruction
    | Mem : ('a, 'b) Relation.t * ('a, unit) Ref.hlist -> bool instruction
    | Ite : bool instruction * 'a instruction * 'a instruction -> 'a instruction

  type iterator_ex =
    | Iterator_ex :
        'a ColumnType.t
        * 'a Iterator.t
        * 'a ColumnType.Cell.t option
        * 'a ref option
        * bool instruction
        -> iterator_ex

  let rec run_instruction db = function
    | Accept -> true
    | Reject -> false
    | Mem (Table is_table, args) ->
      let table = Database.get_table db is_table in
      Option.is_some (Trie.find_opt_refs is_table.is_trie args table.trie)
    | Ite (c, t, e) ->
      if run_instruction db c
      then run_instruction db t
      else run_instruction db e

  type binder = Bind : ('t, 'k, 'v) Table.t * 't handler list -> binder

  type ('p, 'v) t =
    { parameters : ('p, unit) cells;
      variables : ('v, unit) Ref.hlist;
      binders : (int, binder) Hashtbl.t;
      iterators : iterator_ex array;
      last_iterator : int
    }

  let iterator_ex column it = Iterator_ex (column, it, None, None, Accept)

  type 'a binding =
    { column : 'a ColumnType.t option;
      order : int;
      name : string option;
      mutable iterators : 'a Trie.Map_iterator.t list;
      mutable cell : 'a ColumnType.Cell.t option;
      mutable output : 'a ref option;
      mutable extra_bindings : iterator_ex list;
      mutable instruction : bool instruction
    }

  let print_binding ppf { name; order; _ } =
    match name with
    | None -> Format.fprintf ppf "Unnamed variable (with order %d)" order
    | Some name -> Format.fprintf ppf "Variable '%s' (with order %d)" name order

  let get_column binding =
    match binding.column with
    | Some column -> column
    | None -> Misc.fatal_errorf "Could not infer the type."

  let get_or_create_cell binding =
    match binding.cell with
    | None ->
      let cell = ColumnType.Cell.create (get_column binding) in
      binding.cell <- Some cell;
      cell
    | Some cell -> cell

  let get_or_create_output binding =
    match binding.output with
    | None ->
      let output = ColumnType.create_ref (get_column binding) in
      binding.output <- Some output;
      output
    | Some output -> output

  type binding_info = Binding_info : 'a binding -> binding_info [@@unboxed]

  type bindings =
    { constant_binding_info : binding_info;
      all_bindings : (string, binding_info) Hashtbl.t
    }

  let create_empty_binding ?name ~order column =
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
    { constant_binding_info = Binding_info (create_empty_binding ~order:0 None);
      all_bindings = Hashtbl.create 17
    }

  let ordered_bindings bindings =
    let arr =
      Array.make
        (Hashtbl.length bindings.all_bindings + 1)
        bindings.constant_binding_info
    in
    Hashtbl.iter
      (fun _ (Binding_info binding) ->
        arr.(binding.order) <- Binding_info binding)
      bindings.all_bindings;
    arr

  let create_binding (type a) ?order bindings var (ty : a ColumnType.t option) :
      a binding =
    match Hashtbl.find_opt bindings.all_bindings var with
    | Some (Binding_info _) ->
      Misc.fatal_errorf "Variable '%s' is already defined" var
    | None ->
      let order =
        match order with
        | None -> Hashtbl.length bindings.all_bindings + 1
        | Some order -> order
      in
      let binding = create_empty_binding ~name:var ~order ty in
      Hashtbl.add bindings.all_bindings var (Binding_info binding);
      binding

  let get_binding (type a) bindings var (ty : a ColumnType.t) : a binding =
    match Hashtbl.find_opt bindings.all_bindings var with
    | Some (Binding_info binding) -> (
      match binding.column with
      | None ->
        let binding =
          create_empty_binding ?name:binding.name ~order:binding.order (Some ty)
        in
        Hashtbl.replace bindings.all_bindings var (Binding_info binding);
        binding
      | Some column -> (
        match ColumnType.provably_equal ty column with
        | Some Equal -> binding
        | None ->
          Misc.fatal_errorf
            "Incompatible types for variable '%s': '%a' and '%a'" var
            ColumnType.print ty ColumnType.print column))
    | None ->
      Misc.fatal_errorf "Variable '%s' is used (with type '%a') but not bound."
        var ColumnType.print ty

  let rec build_var_order :
      type a. bindings -> (a, unit) Variable.hlist -> (a, unit) Ref.hlist =
   fun bindings variables ->
    match variables with
    | [] -> []
    | (var, column) :: other_variables ->
      let binding = create_binding bindings var (Some column) in
      get_or_create_output binding :: build_var_order bindings other_variables

  let rec process_parameters :
      type a b. bindings -> (a, b) Variable.hlist -> (a, b) cells =
   fun bindings parameters ->
    match parameters with
    | [] -> No_cells
    | (param, ty) :: other_params ->
      let binding = create_binding bindings param (Some ty) in
      (* Note: we do not use the cell from [binding] here because it is used to
         propagate the value of the parameter downwards to other iterators once
         it has been joined with all its occurrences, whereas the cell here is
         used to initialize the filter from the toplevel *before* the join. *)
      let cell = ColumnType.Cell.create ty in
      let filter = ColumnType.Cell.to_iterator ty cell in
      binding.iterators <- filter :: binding.iterators;
      One_cell (ty, cell, process_parameters bindings other_params)

  let rec compile_atom :
      type a.
      bindings ->
      (a, unit) ColumnType.hlist ->
      (a, unit) Term.hlist ->
      (a, unit) Ref.hlist =
   fun bindings schema vars ->
    match schema, vars with
    | [], [] -> []
    | column :: schema, term :: terms -> (
      match term with
      | Constant cte -> ref cte :: compile_atom bindings schema terms
      | Variable var ->
        let binding = get_binding bindings var column in
        get_or_create_output binding :: compile_atom bindings schema terms)

  let rec process_atom :
      type a.
      bindings ->
      binding_info ->
      (a, unit) ColumnType.hlist ->
      (a, unit) Term.hlist ->
      a Trie.iterator ->
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
        ColumnType.Cell.set this_column cell cte;
        let filter = ColumnType.Cell.to_iterator this_column cell in
        let iterator = Iterator.create [this_iterator; filter] in
        let (Binding_info info) = last_binding in
        info.extra_bindings
          <- iterator_ex this_column iterator :: info.extra_bindings;
        process_atom bindings last_binding other_columns other_args
          other_iterators
      | Variable var ->
        let var_info = get_binding bindings var this_column in
        let (Binding_info last_info) = last_binding in
        if var_info.order >= last_info.order
        then (
          var_info.iterators <- this_iterator :: var_info.iterators;
          process_atom bindings (Binding_info var_info) other_columns other_args
            other_iterators)
        else
          let cell = get_or_create_cell var_info in
          let filter = ColumnType.Cell.to_iterator this_column cell in
          let iterator = Iterator.create [this_iterator; filter] in
          last_info.extra_bindings
            <- iterator_ex this_column iterator :: last_info.extra_bindings;
          process_atom bindings last_binding other_columns other_args
            other_iterators)

  let cast (type t1 k1 v1 t2 k2 v2) (t1 : (t1, k1, v1) Table.t)
      (t2 : (t2, k2, v2) Table.t) (handler : t1 handler) : t2 handler =
    match Table.provably_equal t1 t2 with
    | Some Equal -> handler
    | None -> assert false

  type ('p, 'v) raw_query =
    { parameters : ('p, unit) cells;
      variables : ('v, unit) Ref.hlist;
      bindings : bindings;
      binders : (int, binder) Hashtbl.t
    }

  let rec process_for_negation :
      type a.
      bindings ->
      binding_info ->
      (a, unit) ColumnType.hlist ->
      (a, unit) Term.hlist ->
      binding_info * (a, unit) Ref.hlist =
   fun bindings last_binding schema args ->
    match schema, args with
    | [], [] -> last_binding, []
    | column :: schema, arg :: args -> (
      match arg with
      | Constant cte ->
        let r = ColumnType.create_ref column in
        r := cte;
        let last_binding, refs =
          process_for_negation bindings last_binding schema args
        in
        last_binding, r :: refs
      | Variable var ->
        let var_info = get_binding bindings var column in
        let (Binding_info last_info) = last_binding in
        let last_binding, refs =
          if var_info.order >= last_info.order
          then process_for_negation bindings (Binding_info var_info) schema args
          else process_for_negation bindings last_binding schema args
        in
        last_binding, get_or_create_output var_info :: refs)

  let populate_bindings ~parameters ~variables ?(existentials = []) bindings =
    (* Compute the cells in which to pass parameter values. *)
    let parameter_cells = process_parameters bindings parameters in
    (* Create bindings for variables, in order. *)
    let output = build_var_order bindings variables in
    List.iter
      (fun var -> ignore (create_binding bindings var None))
      existentials;
    parameter_cells, output

  let create_raw bindings ~parameters:parameter_cells ~variables:output
      ?(negate = []) (atoms : unit Atom.t list) : _ =
    let binders = Hashtbl.create 17 in
    List.iter
      (fun (Atom.Atom (Table relation, args)) ->
        let handler, iterators = Table.iterator relation Ignore in
        process_atom bindings bindings.constant_binding_info
          (Table.schema relation) args iterators;
        let uid = Table.uid relation in
        match Hashtbl.find_opt binders uid with
        | None -> Hashtbl.replace binders uid (Bind (relation, [handler]))
        | Some (Bind (existing, handlers)) ->
          let handler = cast relation existing handler in
          Hashtbl.replace binders uid (Bind (existing, handler :: handlers)))
      atoms;
    List.iter
      (fun (Atom.Atom (Table relation, args)) ->
        let Binding_info last_binding, refs =
          process_for_negation bindings bindings.constant_binding_info
            (Table.schema relation) args
        in
        (* Weird things would happen with negation of only constants *)
        assert (last_binding.order > 0);
        last_binding.instruction
          <- Ite (Mem (Table relation, refs), Reject, last_binding.instruction))
      negate;
    { parameters = parameter_cells; variables = output; bindings; binders }

  exception Last_variable of int

  let make_iterators bindings =
    let ordered = ordered_bindings bindings in
    let last_order =
      try
        for i = Array.length ordered - 1 downto 0 do
          let (Binding_info info) = ordered.(i) in
          match[@warning "-fragile-match"]
            info.cell, info.output, info.instruction
          with
          | None, None, Accept -> ()
          | _ -> raise (Last_variable i)
        done;
        -1
      with Last_variable i -> i
    in
    let last_iterator = ref (-1) in
    let all_iterators = ref ([] : _ list) in
    Array.iter
      (fun (Binding_info info) ->
        (match info.iterators with
        | [] -> (
          (* Constants do not have iterators anyways. *)
          if info.order <> 0
          then
            Misc.fatal_errorf
              "%a always appears after variables with lower order."
              print_binding info;
          match[@warning "-fragile-match"] info.instruction with
          | Accept -> ()
          | _ -> assert false)
        | _ :: _ ->
          let iterator = Iterator.create info.iterators in
          let column = get_column info in
          let joe_schmuck =
            Iterator_ex
              (column, iterator, info.cell, info.output, info.instruction)
          in
          all_iterators := (joe_schmuck :: !all_iterators : _ list));
        if info.order = last_order
        then last_iterator := List.length !all_iterators - 1;
        all_iterators := List.rev_append info.extra_bindings !all_iterators)
      ordered;
    Array.of_list (List.rev !all_iterators), !last_iterator

  let from_raw { parameters; variables; bindings; binders } =
    let iterators, last_iterator = make_iterators bindings in
    { parameters; variables; binders; iterators; last_iterator }

  let _create ~parameters ~variables atoms =
    let bindings = create_bindings () in
    let parameters, variables =
      populate_bindings ~parameters ~variables bindings
    in
    from_raw (create_raw bindings ~parameters ~variables atoms)

  let create ~parameters variables f =
    let bindings = create_bindings () in
    let cells, output = populate_bindings ~parameters ~variables bindings in
    let query = f (Term.variables parameters) (Term.variables variables) in
    from_raw (create_raw bindings ~parameters:cells ~variables:output query)

  let rec bind_parameters :
      type a. (a, unit) cells -> (a, unit) Constant.hlist -> unit =
   fun cells values ->
    match cells, values with
    | No_cells, [] -> ()
    | One_cell (column, cell, cells'), value :: values' ->
      ColumnType.Cell.set column cell value;
      bind_parameters cells' values'

  let rec compiled_loop db arr depth
      (Iterator_ex (column, iterator, cell, output, instr) as this_level) =
    match Iterator.current iterator with
    | At_start -> assert false
    | Key current_key ->
      (match output with Some output -> output := current_key | None -> ());
      if run_instruction db instr
      then (
        (match cell with
        | Some cell -> ColumnType.Cell.set column cell current_key
        | None -> ());
        Iterator.accept iterator;
        let next_depth = depth + 1 in
        if next_depth = Array.length arr
        then depth
        else
          let next_level = arr.(next_depth) in
          let (Iterator_ex (_, next_iterator, _, _, _)) = next_level in
          Iterator.init next_iterator;
          compiled_loop db arr next_depth next_level)
      else (
        Iterator.advance iterator;
        compiled_loop db arr depth this_level)
    | At_end ->
      if depth = 0
      then -1
      else
        let prev_depth = depth - 1 in
        let prev_level = arr.(prev_depth) in
        let (Iterator_ex (_, prev_iterator, _, _, _)) = prev_level in
        Iterator.advance prev_iterator;
        compiled_loop db arr prev_depth prev_level

  let[@inline] with_naive binders database f acc =
    Hashtbl.iter
      (fun _ (Bind (relation, handlers)) ->
        let table = Database.get_table database relation in
        List.iter (fun handler -> run_handler table.trie handler) handlers)
      binders;
    f acc

  let[@inline] with_seminaive binders { database; new_facts } f acc =
    let rec loop cnt acc =
      let cnt_this_run = ref 0 in
      Hashtbl.iter
        (fun _ (Bind (relation, handlers)) ->
          let table = Database.get_table database relation in
          let diff = Database.get_table new_facts relation in
          if Table.is_empty diff.Table.is_table diff
          then
            List.iter (fun handler -> run_handler table.trie handler) handlers
          else
            List.iter
              (fun handler ->
                if !cnt_this_run = cnt
                then run_handler diff.trie handler
                else run_handler table.trie handler;
                incr cnt_this_run)
              handlers)
        binders;
      if cnt < !cnt_this_run then loop (cnt + 1) (f acc) else acc
    in
    loop 0 acc

  let run_fold db (query : (_, _) t) f init =
    let first_level = query.iterators.(0) in
    let (Iterator_ex (_, first_iterator, _, _, _)) = first_level in
    Iterator.init first_iterator;
    let last = query.last_iterator in
    let rec loop depth acc =
      if depth < 0
      then acc
      else
        let acc = f (Ref.get_hlist query.variables) acc in
        if last < 0
        then acc
        else
          let (Iterator_ex (_, iterator, _, _, _)) = query.iterators.(last) in
          Iterator.advance iterator;
          let depth =
            compiled_loop db query.iterators last query.iterators.(last)
          in
          loop depth acc
    in
    loop (compiled_loop db query.iterators 0 first_level) init

  let run_iter db (query : (_, _) t) f =
    let first_level = query.iterators.(0) in
    let (Iterator_ex (_, first_iterator, _, _, _)) = first_level in
    Iterator.init first_iterator;
    let last = query.last_iterator in
    let rec loop depth =
      if depth < 0
      then ()
      else (
        f ();
        if last < 0
        then ()
        else
          let (Iterator_ex (_, iterator, _, _, _)) = query.iterators.(last) in
          Iterator.advance iterator;
          loop (compiled_loop db query.iterators last query.iterators.(last)))
    in
    loop (compiled_loop db query.iterators 0 first_level)

  let generic_fold db with_ (query : (_, _) t) parameters database ~init ~f =
    bind_parameters query.parameters parameters;
    with_ query.binders database (run_fold db query f) init

  let fold query parameters database ~init ~f =
    generic_fold database with_naive query parameters database ~init ~f

  let incremental_fold query parameters database ~init ~f =
    generic_fold database.database with_seminaive query parameters database
      ~init ~f

  let iter query parameters database ~f =
    fold query parameters database ~init:() ~f:(fun row () -> f row)

  let _incremental_iter query parameters database ~f =
    incremental_fold query parameters database ~init:() ~f:(fun row () -> f row)
end

module Rule = struct
  type t =
    | Rule :
        { query : (unit, unit) Query.t;
          relation : ('k, 'v) Relation.t;
          arguments : ('k, unit) Ref.hlist;
          value : 'v option
        }
        -> t

  let create ~variables ?(existentials = []) conclusion value ?negate hypotheses
      =
    let bindings = Query.create_bindings () in
    let parameters, variables =
      Query.populate_bindings ~parameters:[] ~variables:[]
        ~existentials:(variables @ existentials) bindings
    in
    let raw =
      Query.create_raw bindings ~parameters ~variables ?negate hypotheses
    in
    let (Atom.Atom (Table table, args)) = conclusion in
    let arguments = Query.compile_atom raw.bindings (Table.schema table) args in
    let query = Query.from_raw raw in
    Rule { query; relation = Table table; arguments; value }

  let delete ~variables ?existentials conclusion ?negate hypotheses =
    create ~variables ?existentials conclusion None ?negate hypotheses

  let create ~variables ?existentials conclusion ?negate hypotheses =
    create ~variables ?existentials conclusion (Some ()) ?negate hypotheses

  let rec saturate_seminaive ?(use_naive = false) n rules incremental =
    let database = ref incremental.database in
    let[@inline] naive_runner (query : (_, _) Query.t) f =
      Query.with_naive query.Query.binders incremental.database
        (fun () -> Query.run_iter incremental.database query f)
        ()
    in
    let[@inline] seminaive_runner (query : (_, _) Query.t) f =
      Query.with_seminaive query.Query.binders incremental
        (fun () -> Query.run_iter incremental.database query f)
        ()
    in
    let[@inline] naive_run_step (Rule { relation; arguments; value; query }) =
      let (Table is_table) = relation in
      let table = ref (Database.get_table !database is_table) in
      (match value with
      | Some value ->
        naive_runner query (fun () ->
            let arguments = Ref.get_hlist arguments in
            table := Table.add arguments value !table)
      | None ->
        naive_runner query (fun () ->
            let arguments = Ref.get_hlist arguments in
            table := Table.remove arguments !table));
      database := Database.set_table !database is_table !table
    in
    let[@inline] seminaive_run_step (Rule { relation; arguments; value; query })
        =
      let (Table is_table) = relation in
      let table = ref (Database.get_table !database is_table) in
      (match value with
      | Some value ->
        seminaive_runner query (fun () ->
            let arguments = Ref.get_hlist arguments in
            table := Table.add arguments value !table)
      | None ->
        seminaive_runner query (fun () ->
            let arguments = Ref.get_hlist arguments in
            table := Table.remove arguments !table));
      database := Database.set_table !database is_table !table
    in
    if use_naive
    then List.iter naive_run_step rules
    else List.iter seminaive_run_step rules;
    if !database == incremental.database
    then !database
    else
      let diff =
        Database.cut !database
          ~cut_after:(Database.current_level incremental.database)
      in
      saturate_seminaive (n + 1) rules
        { database = !database; new_facts = diff }
end

module Schedule = struct
  type t =
    | Fixpoint of t
    | Saturate of Rule.t list * int Id.Map.t
    | List of t list

  let fixpoint schedule = Fixpoint schedule

  let list schedules = List schedules

  let saturate rules = Saturate (rules, Id.Map.empty)

  (* takes (db, current_level) and creates a new (db, current_level) *)
  let saturate_seminaive ~use_naive queries incremental =
    (* List.iter (fun query -> clear_updates query.updates) queries; *)
    Rule.saturate_seminaive ~use_naive 0 queries incremental

  let do_saturate ~use_naive queries database new_facts =
    saturate_seminaive ~use_naive queries { database; new_facts }

  let rec run db schedule : _ * t =
    match schedule with
    | Saturate (rules, last_ts) ->
      let use_naive = Id.Map.is_empty last_ts in
      let new_facts = Database.cut db ~cut_after:last_ts in
      let db' = do_saturate ~use_naive rules db new_facts in
      db', Saturate (rules, Database.current_level db')
    | Fixpoint schedule ->
      let db', schedule' = run db schedule in
      if db' == db
      then db', Fixpoint schedule'
      else run db' (Fixpoint schedule')
    | List schedules ->
      let db, schedules = List.fold_left_map run db schedules in
      db, List schedules

  let run schedule db =
    let db', _schedule' = run db schedule in
    db'
end

type database = Database.raw

let empty = Database.empty

let add_fact (Relation.Table id) args db =
  Database.set_table db id
    (Relation.add_fact id args () (Database.get_table db id))

let _ = ignore Trie.remove

let () =
  if false
  then (
    let db = Database.empty in
    let int = ColumnType.int in
    let p = Relation.create ~name:"p" [int; int] in
    let q = Relation.create ~name:"q" [int; int] in
    let r = Relation.create ~name:"r" [int; int; int] in
    let s = Relation.create ~name:"s" [int; int] in
    (* p *)
    let db = add_fact p [0; 1] db in
    let db = add_fact p [1; 0] db in
    let db = add_fact p [2; 1] db in
    let db = add_fact p [7; 3] db in
    let db = add_fact p [1; 7] db in
    (* q *)
    let db = add_fact q [1; 2] db in
    let db = add_fact q [3; 1] db in
    (* r *)
    let db = add_fact r [1; 3; 0] db in
    let db = add_fact r [7; 12; 1] db in
    let x = "x" in
    let y = "y" in
    let z = "z" in
    let rule1 =
      Rule.create ~variables:[z; y; x]
        (Atom.create r [Variable x; Constant 42; Variable z])
        [Atom (p, [Variable x; Variable y]); Atom (q, [Variable z; Variable y])]
    in
    Format.eprintf "rule 1 compiled@.";
    let rule2 =
      Rule.create ~variables:[x; z; y]
        (Atom.create p [Variable x; Variable y])
        [Atom (r, [Variable x; Variable z; Variable y])]
    in
    Format.eprintf "rule 2 compiled@.";
    let _rule5 =
      Rule.create ~variables:[x; y]
        (Atom.create s [Variable x; Variable y])
        ~negate:[Atom.create p [Variable y; Variable x]]
        [Atom.create p [Variable x; Variable y]]
    in
    let schedule =
      let open! Schedule in
      list
        [ fixpoint (list [saturate [rule1; rule2] (* ; saturate ([rule3]) *)]);
          saturate [_rule5] ]
    in
    Format.eprintf "@[<v>Before:@ %a@]@." Database.print db;
    let db = Schedule.run schedule db in
    (* let db = add_fact db (Fact (p, [| 57; 57 |])) in *)
    Format.eprintf "doit again@.";
    (* let db, _schedule = run_schedule db schedule in *)
    Format.eprintf "@[<v>After:@ %a@]@." Database.print db)

let print = Database.print
