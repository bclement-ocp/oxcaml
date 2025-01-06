(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Basile Clément, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2024 OCamlPro SAS                                          *)
(*   Copyright 2024 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@warning "-unused-module"]

open Heterogenous_list

(* Needs to be exported. *)
module Constant = Constant

module Int = struct
  include Numbers.Int
  module Tree = Patricia_tree.Make (Numbers.Int)
  module Map = Tree.Map
end

(* This is the [Type] module from OCaml 5's Stdlib *)
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
      (* NB: [Obj.Extension_constructor.of_val] does a bunch of checks; we could
         just do [let slot : extension_constructor = Obj.magic A.Id] here *)
      let slot = Obj.Extension_constructor.of_val A.Id in
      Obj.Extension_constructor.id slot

    let provably_equal (type a b) ((module A) : a t) ((module B) : b t) :
        (a, b) eq option =
      match A.Id with B.Id -> Some Equal | _ -> None
  end
end

module ColumnType : sig
  include Heterogenous_list.S

  val printer : 'a t -> Format.formatter -> 'a -> unit

  val make : string -> print:(Format.formatter -> int -> unit) -> int t

  val int : int t

  val is_trie : ('a -> 'c) hlist -> ('a -> 'c, 'b) Trie.is_any_trie
end = struct
  type 'a t =
    { id : 'a Type.Id.t;
      name : string;
      print : Format.formatter -> 'a -> unit;
      is_int : ('a, int) Type.eq
    }

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)

  let printer { print; _ } = print

  let make name ~print = { id = Type.Id.make (); name; print; is_int = Equal }

  let int = make "int" ~print:Format.pp_print_int

  let rec is_trie : type a b c. (a -> c) hlist -> (a -> c, b) Trie.is_any_trie =
   fun s ->
    match s with
    | [{ is_int = Equal; _ }] -> Is_trie Trie.patricia_map
    | { is_int = Equal; _ } :: (_ :: _ as s') ->
      let (Is_trie t') = is_trie s' in
      Is_trie (Trie.patricia_map_of_trie t')
end

module Table : sig
  module Iterator : sig
    include Leapfrog.Iterator

    include Heterogenous_list.S with type 'a t := 'a t
  end

  type ('t, 'k, 'v) repr

  val empty : ('t, 'k, 'v) repr -> 't

  val find_opt : ('t, 'k, 'v) repr -> 'k Constant.hlist -> 't -> 'v option

  val mem : ('t, 'k, 'v) repr -> 'k Constant.hlist -> 't -> bool

  val add_or_replace : ('t, 'k, 'v) repr -> 'k Constant.hlist -> 'v -> 't -> 't

  val iterator : ('t, 'k, 'v) repr -> 'v ref -> 't ref * 'k Iterator.hlist

  module Id : sig
    type ('t, 'k, 'v) t

    type ('k, 'v) poly = Id : ('t, 'k, 'v) t -> ('k, 'v) poly

    val create_trie :
      name:string -> ('k -> 'r) ColumnType.hlist -> ('k -> 'r, 'v) poly

    val repr : ('t, 'k, 'v) t -> ('t, 'k, 'v) repr
  end

  module Map : sig
    type t

    val print : Format.formatter -> t -> unit

    val empty : t

    val is_empty : t -> bool

    val get : t -> ('t, 'k, 'v) Id.t -> 't

    val set : t -> ('t, 'k, 'v) Id.t -> 't -> t

    val concat : earlier:t -> later:t -> t
  end
end = struct
  type ('t, 'k, 'v) repr =
    | Trie : ('t, 'k, 'v) Trie.is_trie -> ('t, 'k, 'v) repr

  let print (Trie is_trie) ?(pp_sep = Format.pp_print_cut) pp_row ppf table =
    let first = ref true in
    Trie.iter is_trie
      (fun keys value ->
        if !first then first := false else pp_sep ppf ();
        pp_row keys value)
      table

  let iterator (Trie is_trie) out =
    let handler = ref (Trie.empty is_trie) in
    let iterator = Trie.Iterator.create is_trie handler out in
    handler, iterator

  let empty (Trie is_trie) = Trie.empty is_trie

  let is_empty (Trie is_trie) = Trie.is_empty is_trie

  let add_or_replace (Trie is_trie) = Trie.add_or_replace is_trie

  let find_opt (Trie is_trie) = Trie.find_opt is_trie

  let mem (Trie is_trie) keys t = Option.is_some (Trie.find_opt is_trie keys t)

  let concat (Trie is_trie) ~earlier:t1 ~later:t2 =
    Trie.union is_trie (fun _ v -> Some v) t1 t2

  module Id = struct
    type ('t, 'k, 'v) t =
      { id : 't Type.Id.t;
        name : string;
        schema : 'k ColumnType.hlist;
        repr : ('t, 'k, 'v) repr
      }

    let repr { repr; _ } = repr

    type ('k, 'v) poly = Id : ('t, 'k, 'v) t -> ('k, 'v) poly

    let print ppf t = Format.fprintf ppf "%s" t.name

    let[@inline] create_trie ~name schema =
      let (Is_trie is_trie) = ColumnType.is_trie schema in
      Id { id = Type.Id.make (); name; repr = Trie is_trie; schema }

    let[@inline] uid { id; _ } = Type.Id.uid id

    let[@inline] schema { schema; _ } = schema

    let[@inline] cast_exn (type a b k v k' v') (r1 : (a, k, v) t)
        (r2 : (b, k', v') t) (t : a) : b =
      match Type.Id.provably_equal r1.id r2.id with
      | Some Equal -> t
      | None -> Misc.fatal_error "Inconsistent type for uid."
  end

  module Iterator = Trie.Iterator

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
      (print id.Id.repr (fun keys _ ->
           Format.fprintf ppf "@[%a(%a).@]" Id.print id
             (print_row (Id.schema id))
             keys))
      table

  let print id ppf table =
    let header = Format.asprintf "%a" Id.print id in
    Format.fprintf ppf "@[<v>%s@ %s@ %a@]" header
      (String.make (String.length header) '=')
      (print_table id) table

  module Map = struct
    type binding = Binding : ('t, 'k, 'v) Id.t * 't -> binding

    type t = binding Int.Map.t

    let print ppf tables =
      let first = ref true in
      Format.fprintf ppf "@[<v>";
      Int.Map.iter
        (fun _ (Binding (id, table)) ->
          if !first then first := false else Format.fprintf ppf "@ @ ";
          print id ppf table)
        tables;
      Format.fprintf ppf "@]"

    let get (type t k v) tables (id : (t, k, v) Id.t) : t =
      match Int.Map.find_opt (Id.uid id) tables with
      | Some (Binding (existing_id, table)) -> Id.cast_exn existing_id id table
      | None -> empty (Id.repr id)

    let set (type t k v) tables (id : (t, k, v) Id.t) (table : t) =
      if is_empty (Id.repr id) table
      then
        if Int.Map.mem (Id.uid id) tables
        then Int.Map.remove (Id.uid id) tables
        else tables
      else
        match Int.Map.find_opt (Id.uid id) tables with
        | None -> Int.Map.add (Id.uid id) (Binding (id, table)) tables
        | Some (Binding (existing_id, existing_table)) ->
          if table == Id.cast_exn existing_id id existing_table
          then tables
          else Int.Map.add (Id.uid id) (Binding (id, table)) tables

    let empty = Int.Map.empty

    let is_empty = Int.Map.is_empty

    let concat ~earlier:tables1 ~later:tables2 =
      Int.Map.union
        (fun _ (Binding (id1, table1)) (Binding (id2, table2)) ->
          let table =
            concat (Id.repr id1) ~earlier:table1
              ~later:(Id.cast_exn id2 id1 table2)
          in
          Some (Binding (id1, table)))
        tables1 tables2
  end
end

type database = Table.Map.t

let empty = Table.Map.empty

(* We could expose the fact that we do not support relations without arguments
   in the types, but a runtime error here allows us to give a better error
   message. Plus, we might support constant relations (represented as an option)
   in the future. *)
let create_relation (type k) ~name (schema : k ColumnType.hlist) :
    (k, _) Table.Id.poly =
  match schema with
  | [] ->
    invalid_arg "create_relation: relations with no arguments are unsupported"
  | _ :: _ -> Table.Id.create_trie ~name schema

let add_fact (Table.Id.Id id) args db =
  Table.Map.set db id
    (Table.add_or_replace (Table.Id.repr id) args () (Table.Map.get db id))

let print = Table.Map.print

(* Now we start cursors. *)

module Parameter = struct
  type 'a t =
    { name : string;
      cell : 'a option ref
    }

  let create name = { name; cell = ref None }

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)
end

module Join_iterator = Leapfrog.Make (Table.Iterator)

module Cursor = struct
  type _ vals =
    | Vals_nil : nil vals
    | Vals_constant : 'a * 'b vals -> ('a -> 'b) vals
    | Vals_option : 'a option ref * 'b vals -> ('a -> 'b) vals

  let rec get_vals : type a. a vals -> a Constant.hlist = function
    | Vals_nil -> []
    | Vals_constant (v, vs) -> v :: get_vals vs
    | Vals_option (r, vs) -> Option.get !r :: get_vals vs

  type _ op =
    | Add_incremental :
        { repr : ('t, 'k, unit) Table.repr;
          full : 't ref;
          diff : 't ref;
          keys : 'k vals
        }
        -> 'y op
    | Bind_iterator : 'a option ref * 'a Table.Iterator.t -> 'y op
    | Unless : ('t, 'k, 'v) Table.Id.t * 'k vals -> 'y op
    | Yield : 'a vals -> 'a Constant.hlist op

  type ('y, 's) instruction =
    | Advance : ('y, 's) instruction
    | Pop : ('y, 's) instruction -> ('y, 'a -> 's) instruction
    | Open : ('a, 'y, 's) level -> ('y, 's) instruction
    | Seq : 'y op * ('y, 's) instruction -> ('y, 's) instruction

  and ('a, 'y, 's) level =
    { iterator : 'a Join_iterator.t;
      output : 'a option ref option;
      instruction : ('y, 'a -> 's) instruction
    }

  type ('y, 's) stack =
    | Stack_nil : ('y, nil) stack
    | Stack_cons : ('a, 'y, 's) level * ('y, 's) stack -> ('y, 'a -> 's) stack

  type 'y outcome =
    | Yielded of 'y
    | Complete

  type 'y suspension =
    | Suspension :
        { stack : ('y, 's) stack;
          instruction : ('y, 's) instruction
        }
        -> 'y suspension

  let exhausted = Suspension { stack = Stack_nil; instruction = Advance }

  type 'y state =
    { input : Table.Map.t;
      mutable suspension : 'y suspension
    }

  let[@inline] rec execute :
      type y s.
      Table.Map.t ->
      (y, s) stack ->
      (y, s) instruction ->
      y suspension * y outcome =
   fun input stack instruction ->
    let[@local] dispatch :
        type a y s. (y, s) stack -> (a, y, s) level -> y suspension * y outcome
        =
     fun stack level ->
      match Join_iterator.current level.iterator with
      | Some current_key ->
        Option.iter (fun r -> r := Some current_key) level.output;
        Join_iterator.accept level.iterator;
        execute input (Stack_cons (level, stack)) level.instruction
      | None -> execute input stack Advance
    in
    let[@local] advance : type y s. (y, s) stack -> y suspension * y outcome =
      function
      | Stack_nil -> exhausted, Complete
      | Stack_cons (level, stack) ->
        Join_iterator.advance level.iterator;
        dispatch stack level
    in
    let[@local] evaluate :
        type y s.
        Table.Map.t ->
        (y, s) stack ->
        continuation:(y, s) instruction ->
        y op ->
        y suspension * y outcome =
     fun input stack ~continuation -> function
      | Yield vals ->
        let suspension = Suspension { stack; instruction = continuation } in
        suspension, Yielded (get_vals vals)
      | Add_incremental { repr; full; diff; keys } -> (
        let table = !full in
        let keys = get_vals keys in
        match Table.find_opt repr keys table with
        | Some _ ->
          (* CR bclement: support updates for non-unit values. *)
          execute input stack continuation
        | None ->
          diff := Table.add_or_replace repr keys () !diff;
          full := Table.add_or_replace repr keys () table;
          execute input stack continuation)
      | Bind_iterator (value, it) -> (
        let value = Option.get !value in
        Table.Iterator.init it;
        Table.Iterator.seek it value;
        match Table.Iterator.current it with
        | Some found when Table.Iterator.equal_key it found value ->
          Table.Iterator.accept it;
          execute input stack continuation
        | None | Some _ -> execute input stack Advance)
      | Unless (id, args) ->
        if Table.mem (Table.Id.repr id) (get_vals args) (Table.Map.get input id)
        then execute input stack Advance
        else execute input stack continuation
    in
    match instruction with
    | Advance -> advance stack
    | Open next_level ->
      Join_iterator.init next_level.iterator;
      dispatch stack next_level
    | Pop instruction ->
      let (Stack_cons (_, stack)) = stack in
      execute input stack instruction
    | Seq (op, continuation) -> evaluate input stack ~continuation op

  let execute : type y. y state -> y outcome =
   fun state ->
    let (Suspension { stack; instruction }) = state.suspension in
    let suspension, outcome = execute state.input stack instruction in
    state.suspension <- suspension;
    outcome

  let[@inline] run_fold f state init =
    let rec loop state acc =
      match execute state with
      | Yielded output -> loop state (f output acc)
      | Complete -> acc
    in
    loop state init

  let[@inline] run_iter f state = run_fold (fun keys () -> f keys) state ()

  let create_state input instruction =
    { input; suspension = Suspension { stack = Stack_nil; instruction } }

  type binder = Bind_table : ('t, 'k, 'v) Table.Id.t * 't ref -> binder

  type ('p, 'y) cursor =
    { parameters : 'p Parameter.hlist;
      binders : binder list;
      instruction : ('y, nil) instruction
    }

  type ('p, 'v) with_parameters = ('p, 'v Constant.hlist) cursor

  type 'v t = (nil, 'v) with_parameters

  let rec bind_parameters0 :
      type a. a Parameter.hlist -> a Constant.hlist -> unit =
   fun params values ->
    match params, values with
    | [], [] -> ()
    | param :: params', value :: values' ->
      param.cell := Some value;
      bind_parameters0 params' values'

  let bind_parameters cursor values = bind_parameters0 cursor.parameters values

  (* Naive evaluation iterates over all the matching tuples in the [current]
     database. *)
  let[@inline] with_naive ~current cursor f acc =
    List.iter
      (fun (Bind_table (id, handler)) -> handler := Table.Map.get current id)
      cursor.binders;
    f (create_state current cursor.instruction) acc

  (* Seminaive evaluation iterates over all the {b new} tuples in the [diff]
     database that are not in the [previous] database.

     [current] must be equal to [concat ~earlier:previous ~later:diff]. *)
  let[@inline] with_seminaive ~previous ~diff ~current cursor f acc =
    List.iter
      (fun (Bind_table (relation, handler)) ->
        handler := Table.Map.get current relation)
      cursor.binders;
    let rec loop binders acc =
      match binders with
      | [] -> acc
      | Bind_table (relation, handler) :: binders ->
        handler := Table.Map.get diff relation;
        let acc = f (create_state current cursor.instruction) in
        handler := Table.Map.get previous relation;
        loop binders acc
    in
    loop cursor.binders acc

  let fold_with_parameters cursor parameters database ~init ~f =
    bind_parameters cursor parameters;
    with_naive ~current:database cursor (run_fold f) init

  let fold cursor database ~init ~f =
    fold_with_parameters cursor [] database ~init ~f

  let iter_with_parameters cursor parameters database ~f =
    bind_parameters cursor parameters;
    with_naive ~current:database cursor (fun state () -> run_iter f state) ()

  let iter cursor database ~f = iter_with_parameters cursor [] database ~f
end

type void = |

type rule =
  | Rule :
      { cursor : (nil, void) Cursor.cursor;
        table_id : ('t, 'k, 'v) Table.Id.t;
        current_table : 't ref;
        diff_table : 't ref
      }
      -> rule

let run_rules rules ~previous ~diff ~current =
  let run_step (db_new, db_diff)
      (Rule { table_id; cursor; current_table; diff_table }) =
    current_table := Table.Map.get db_new table_id;
    diff_table := Table.Map.get db_diff table_id;
    let Complete =
      Cursor.with_seminaive ~previous ~diff ~current cursor Cursor.execute
        Cursor.Complete
    in
    ( Table.Map.set db_new table_id !current_table,
      Table.Map.set db_diff table_id !diff_table )
  in
  List.fold_left run_step (current, Table.Map.empty) rules

let rec saturate_rules ~previous ~diff ~current rules full_diff =
  let new_db, diff = run_rules ~previous ~diff ~current rules in
  if Table.Map.is_empty diff
  then current, full_diff
  else
    saturate_rules ~previous:current ~diff rules ~current:new_db
      (Table.Map.concat ~earlier:full_diff ~later:diff)

let saturate_rules rules ~previous ~diff ~current =
  saturate_rules rules Table.Map.empty ~previous ~diff ~current

let run_list fns ~previous ~diff ~current =
  let rec cut ~cut_after result = function
    | [] -> result
    | (ts, diff) :: diffs ->
      if ts > cut_after
      then cut ~cut_after (Table.Map.concat ~earlier:diff ~later:result) diffs
      else result
  in
  let rec loop (current, diffs, ts, full_diff) fns =
    let (current, diffs, ts', full_diff), fns =
      List.fold_left_map
        (fun (db, diffs, ts, full_diff) (fn, previous, cut_after) ->
          let diff = cut ~cut_after Table.Map.empty diffs in
          let new_db, diff = fn ~previous ~diff ~current:db in
          if Table.Map.is_empty diff
          then (db, diffs, ts, full_diff), (fn, db, ts)
          else
            let ts = ts + 1 in
            ( ( new_db,
                (ts, diff) :: diffs,
                ts,
                Table.Map.concat ~earlier:full_diff ~later:diff ),
              (fn, new_db, ts) ))
        (current, diffs, ts, full_diff)
        fns
    in
    if ts' = ts
    then current, full_diff
    else loop (current, diffs, ts', full_diff) fns
  in
  loop
    (current, [0, diff], 0, Table.Map.empty)
    (List.map (fun fn -> fn, previous, -1) fns)

module Schedule = struct
  type t =
    | Saturate of rule list * Table.Map.t * int
    | Fixpoint of t list

  let fixpoint schedule = Fixpoint schedule

  let saturate rules = Saturate (rules, Table.Map.empty, -999)

  let rec run0 schedule ~previous ~diff ~current =
    match schedule with
    | Saturate (rules, _, _) -> saturate_rules rules ~previous ~diff ~current
    | Fixpoint schedules ->
      run_list (List.map run0 schedules) ~previous ~diff ~current

  let run schedule db =
    fst (run0 schedule ~previous:Table.Map.empty ~diff:db ~current:db)
end

type 'k relation = ('k, unit) Table.Id.poly

type 'a rel1 = ('a -> nil) relation

type ('a, 'b) rel2 = ('a -> 'b -> nil) relation

type ('a, 'b, 'c) rel3 = ('a -> 'b -> 'c -> nil) relation

(* START HIGH LEVEL STUFF *)

module Variable = struct
  type condition =
    | Negate : ('t, 'k, 'v) Table.Id.t * 'k Cursor.vals -> condition

  type set_iterator =
    | Set_iterator : 'a option ref * 'a Table.Iterator.t -> set_iterator

  type post_level =
    { mutable rev_conditions : condition list;
      mutable rev_deps : set_iterator list
    }

  type 'a t =
    { name : string;
      order : int;
      post_level : post_level;
      mutable iterators : 'a Table.Iterator.t list;
      mutable output : 'a option ref option
    }

  let name { name; _ } = name

  let get_or_create_output binding =
    match binding.output with
    | None ->
      let output = ref None in
      binding.output <- Some output;
      output
    | Some output -> output

  let create ~order name =
    { name;
      order;
      output = None;
      iterators = [];
      post_level = { rev_deps = []; rev_conditions = [] }
    }

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)

  type elist = Elist : 'a hlist -> elist [@@unboxed]
end

module Term = struct
  type 'a t =
    | Variable of 'a Variable.t
    | Parameter of 'a Parameter.t
    | Constant of 'a

  let constant c = Constant c

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)

  let rec variables : type a. a Variable.hlist -> a hlist = function
    | [] -> []
    | var :: vars -> Variable var :: variables vars

  let rec parameters : type a. a Parameter.hlist -> a hlist = function
    | [] -> []
    | var :: vars -> Parameter var :: parameters vars
end

type _ atom = Atom : ('t, 'k, 'v) Table.Id.t * 'k Term.hlist -> 'v atom

let atom (Table.Id.Id id) args = Atom (id, args)

let constant_order = -1

let rec find_last_binding0 :
    type a.
    ?order:int -> Variable.post_level -> a Term.hlist -> Variable.post_level =
 fun ?order post_level args ->
  match args with
  | [] -> post_level
  | arg :: args -> (
    match arg with
    | Constant _ | Parameter _ -> find_last_binding0 ?order post_level args
    | Variable var ->
      if match order with None -> true | Some order -> var.order >= order
      then find_last_binding0 ~order:var.order var.post_level args
      else find_last_binding0 ?order post_level args)

let find_last_binding post_level args = find_last_binding0 post_level args

module String = struct
  include Heterogenous_list.Make (struct
    type 'a t = string
  end)
end

type variables =
  { mutable rev_vars : Variable.elist;
    mutable nvars : int
  }

type 'p info =
  { parameters : 'p Parameter.hlist;
    variables : variables;
    post_parameters : Variable.post_level;
    binders : Cursor.binder list
  }

type ('p, 'a) program = 'p info -> 'a

let rec add_parameters : type a. a String.hlist -> a Parameter.hlist = function
  | [] -> []
  | name :: names -> Parameter.create name :: add_parameters names

let with_parameters params f info =
  let [] = info.parameters in
  let parameters = add_parameters params in
  f (Term.parameters parameters) { info with parameters }

let rec add_variables : type a. variables -> a String.hlist -> a Variable.hlist
    =
 fun info names ->
  match names with
  | [] -> []
  | name :: names ->
    let var = Variable.create name ~order:info.nvars in
    let (Elist rev_vars) = info.rev_vars in
    info.rev_vars <- Elist (var :: rev_vars);
    info.nvars <- info.nvars + 1;
    var :: add_variables info names

let foreach vars f info =
  let variables = add_variables info.variables vars in
  f (Term.variables variables) info

let run compiler =
  compiler
    { post_parameters = Variable.{ rev_conditions = []; rev_deps = [] };
      parameters = [];
      variables = { nvars = 0; rev_vars = Elist [] };
      binders = []
    }

let compile xs f = run (foreach xs f)

let compile_with_parameters params f = run (with_parameters params f)

let add_dep (level : Variable.post_level) var iterator =
  level.rev_deps <- Set_iterator (var, iterator) :: level.rev_deps

let rec bind_atom :
    type a.
    order:int ->
    Variable.post_level ->
    a Term.hlist ->
    a Table.Iterator.hlist ->
    unit =
 fun ~order post_level args iterators ->
  match args, iterators with
  | [], [] -> ()
  | this_arg :: other_args, this_iterator :: other_iterators -> (
    match this_arg with
    | Constant cte ->
      add_dep post_level (ref (Some cte)) this_iterator;
      bind_atom ~order post_level other_args other_iterators
    | Parameter param ->
      add_dep post_level param.cell this_iterator;
      bind_atom ~order post_level other_args other_iterators
    | Variable var ->
      if var.order > order
      then (
        var.iterators <- this_iterator :: var.iterators;
        bind_atom ~order:var.order var.post_level other_args other_iterators)
      else (
        add_dep post_level (Variable.get_or_create_output var) this_iterator;
        bind_atom ~order post_level other_args other_iterators))

let unit_ref = ref ()

let where predicates f info =
  let info =
    List.fold_left
      (fun info (Atom (id, args)) ->
        let handler, iterators = Table.iterator (Table.Id.repr id) unit_ref in
        bind_atom ~order:constant_order info.post_parameters args iterators;
        { info with binders = Bind_table (id, handler) :: info.binders })
      info predicates
  in
  f info

let rec compile_terms : type a. a Term.hlist -> a Cursor.vals =
 fun vars ->
  match vars with
  | [] -> Vals_nil
  | term :: terms -> (
    match term with
    | Constant cte -> Vals_constant (cte, compile_terms terms)
    | Parameter param -> Vals_option (param.cell, compile_terms terms)
    | Variable var ->
      Vals_option (Variable.get_or_create_output var, compile_terms terms))

let unless predicates f info =
  List.iter
    (fun (Atom (id, args)) ->
      let refs = compile_terms args in
      let post_level = find_last_binding info.post_parameters args in
      post_level.rev_conditions
        <- Negate (id, refs) :: post_level.rev_conditions)
    predicates;
  f info

let postprocess post_level instruction =
  (* Note: conditions only depend on the value of variables, whereas dependences
     only affect iterators, so conditions and dependences can be freely
     reordered.

     However, we {b must} preserve the relative order of dependences in order to
     preserve the initialisation order of iterators; otherwise, we would
     miscompile [P(x, x, x)]. *)
  let instruction =
    List.fold_left
      (fun instruction (Variable.Negate (id, args)) ->
        Cursor.Seq (Cursor.Unless (id, args), instruction))
      instruction post_level.Variable.rev_conditions
  in
  let instruction =
    List.fold_left
      (fun instruction (Variable.Set_iterator (value, it)) ->
        Cursor.Seq (Cursor.Bind_iterator (value, it), instruction))
      instruction post_level.Variable.rev_deps
  in
  instruction

let make_level (var : _ Variable.t) instruction =
  match var.iterators with
  | [] ->
    Misc.fatal_errorf
      "@[<v>@[Variable '%s' is never used in a binding position.@]@ @[Hint: A \
       position is binding if it respects variable ordering.@]@]"
      (Variable.name var)
  | _ ->
    { Cursor.iterator = Join_iterator.create var.iterators;
      output = var.output;
      instruction = postprocess var.post_level instruction
    }

let rec push_vars :
    type s y.
    instruction:(y, s) Cursor.instruction ->
    s Variable.hlist ->
    (y, nil) Cursor.instruction =
 fun ~instruction vars ->
  match vars with
  | [] -> instruction
  | var :: vars ->
    let level = make_level var instruction in
    let next = Cursor.Open level in
    push_vars ~instruction:next vars

(* Optimisation: if we do not use the output from the last variable, we only
   need the first matching value of that variable. *)
let rec pop_vars : type s. s Variable.hlist -> ('y, s) Cursor.instruction =
  function
  | [] -> Advance
  | var :: vars -> (
    match var.output with None -> Pop (pop_vars vars) | _ -> Advance)

let cursor instruction info =
  let (Elist rev_vars) = info.variables.rev_vars in
  let instruction = Cursor.Seq (instruction, pop_vars rev_vars) in
  let instruction = push_vars ~instruction rev_vars in
  let instruction = postprocess info.post_parameters instruction in
  { Cursor.parameters = info.parameters; binders = info.binders; instruction }

let yield output info = cursor (Yield (compile_terms output)) info

let query variables f =
  compile variables @@ fun variables -> where (f variables) @@ yield variables

let deduce (Atom (tid, args)) (info : _ info) =
  let empty = Table.empty (Table.Id.repr tid) in
  let current_table = ref empty in
  let diff_table = ref empty in
  let cursor =
    cursor
      (Add_incremental
         { repr = Table.Id.repr tid;
           full = current_table;
           diff = diff_table;
           keys = compile_terms args
         })
      info
  in
  Rule { cursor; table_id = tid; current_table; diff_table }
