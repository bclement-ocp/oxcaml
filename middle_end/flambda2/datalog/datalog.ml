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

module type Name = sig
  val name : string
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

module Column = struct
  type (_, _, _) repr = Patricia_tree_repr : ('a Int.Map.t, int, 'a) repr

  let trie_repr : type a b c. (a, b, c) repr -> (a, b -> nil, c) Trie.is_trie =
   fun Patricia_tree_repr -> Trie.patricia_tree_is_trie

  let nested_trie_repr :
      type a b c d e.
      (a, b, c) repr -> (c, d, e) Trie.is_trie -> (a, b -> d, e) Trie.is_trie =
   fun Patricia_tree_repr is_trie -> Trie.patricia_tree_of_trie is_trie

  type ('t, 'k, 'v) id =
    { name : string;
      repr : ('t, 'k, 'v) repr
    }

  module type S = sig
    type t

    val print : Format.formatter -> t -> unit

    module Set : Container_types.Set with type elt = t

    module Map :
      Container_types.Map_plus_iterator with type key = t with module Set = Set

    val datalog_column_id : ('a Map.t, t, 'a) id
  end

  type 'a t = (module S with type t = 'a)

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)

  module Make (X : sig
    val name : string

    val print : Format.formatter -> int -> unit
  end) =
  struct
    type t = int

    let print = X.print

    module Tree = Patricia_tree.Make (X)
    module Set = Tree.Set
    module Map = Tree.Map

    let datalog_column_id = { name = X.name; repr = Patricia_tree_repr }
  end
end

module Schema = struct
  let rec print_values :
      type a. a Column.hlist -> Format.formatter -> a Constant.hlist -> unit =
   fun schema ppf ->
    match schema with
    | [] -> fun [] -> ()
    | [(module C)] -> fun [x] -> C.print ppf x
    | (module C) :: k' ->
      fun (x :: y) -> Format.fprintf ppf "%a,@ %a" C.print x (print_values k') y

  module type Value = sig
    type t

    val default : t
  end

  module type S = sig
    type keys

    module Value : Value

    type t

    val is_trie : (t, keys, Value.t) Trie.is_trie

    val schema : keys Column.hlist

    val empty : t

    val is_empty : t -> bool

    val singleton : keys Constant.hlist -> Value.t -> t

    val add_or_replace : keys Constant.hlist -> Value.t -> t -> t

    val remove : keys Constant.hlist -> t -> t

    val union : (Value.t -> Value.t -> Value.t option) -> t -> t -> t

    val find_opt : keys Constant.hlist -> t -> Value.t option
  end

  module Make_ops (T : sig
    type t

    type keys

    type value

    val is_trie : (t, keys, value) Trie.is_trie
  end) =
  struct
    let empty = Trie.empty T.is_trie

    let is_empty trie = Trie.is_empty T.is_trie trie

    let singleton keys value = Trie.singleton T.is_trie keys value

    let add_or_replace keys value trie =
      Trie.add_or_replace T.is_trie keys value trie

    let remove keys trie = Trie.remove T.is_trie keys trie

    let union f trie1 trie2 = Trie.union T.is_trie f trie1 trie2

    let find_opt keys trie = Trie.find_opt T.is_trie keys trie
  end

  type ('t, 'k, 'v) t =
    (module S with type t = 't and type keys = 'k and type Value.t = 'v)

  module Make (C : Column.S) (V : Value) :
    S with type keys = C.t -> nil and module Value = V and type t = V.t C.Map.t =
  struct
    type keys = C.t -> nil

    module Value = V

    type t = V.t C.Map.t

    let is_trie : (t, keys, Value.t) Trie.is_trie =
      Column.trie_repr C.datalog_column_id.repr

    let schema : keys Column.hlist = [(module C)]

    include Make_ops (struct
      type nonrec t = t

      type nonrec keys = keys

      type value = Value.t

      let is_trie = is_trie
    end)
  end

  module Cons (C : Column.S) (S : S) :
    S
      with type keys = C.t -> S.keys
       and module Value = S.Value
       and type t = S.t C.Map.t = struct
    type keys = C.t -> S.keys

    module Value = S.Value

    type t = S.t C.Map.t

    let is_trie = Column.nested_trie_repr C.datalog_column_id.repr S.is_trie

    let schema : keys Column.hlist = (module C) :: S.schema

    include Make_ops (struct
      type nonrec t = t

      type nonrec keys = keys

      type value = Value.t

      let is_trie = is_trie
    end)
  end

  module Unit = struct
    type t = unit

    let default = ()
  end

  module type C = Column.S

  module type Relation = S with type Value.t = unit

  module Relation1 (C1 : C) = Make (C1) (Unit)
  module Relation2 (C1 : C) (C2 : C) = Cons (C1) (Relation1 (C2))
  module Relation3 (C1 : C) (C2 : C) (C3 : C) = Cons (C1) (Relation2 (C2) (C3))
  module Relation4 (C1 : C) (C2 : C) (C3 : C) (C4 : C) =
    Cons (C1) (Relation3 (C2) (C3) (C4))

  type ('k, 'v) any = Any : ('t, 'k, 'v) t -> ('k, 'v) any

  type 'v value = (module Value with type t = 'v)

  let rec dyn : type k r v. (k -> r) Column.hlist -> v value -> (k -> r, v) any
      =
   fun keys (module Value) ->
    match keys with
    | [(module C)] -> Any (module Make (C) (Value))
    | (module C) :: (_ :: _ as keys) ->
      let (Any (module S)) = dyn keys (module Value) in
      Any (module Cons (C) (S))
end

module Table = struct
  type ('t, 'k, 'v) repr =
    | Trie : ('t, 'k, 'v) Trie.is_trie * 'v -> ('t, 'k, 'v) repr

  module Cursor = Leapfrog.Cursor (Trie.Iterator)

  let iter (Trie (is_trie, default_value)) f table =
    let out_ref = ref default_value in
    let iterator = Trie.Iterator.create is_trie (ref table) out_ref in
    let cursor = Cursor.iterator iterator in
    Cursor.iter (fun keys -> f keys !out_ref) cursor

  let print repr ?(pp_sep = Format.pp_print_cut) pp_row ppf table =
    let first = ref true in
    iter repr
      (fun keys value ->
        if !first then first := false else pp_sep ppf ();
        pp_row keys value)
      table

  let iterator (Trie (is_trie, default_value)) =
    let handler = ref (Trie.empty is_trie) in
    let out = ref default_value in
    let iterator = Trie.Iterator.create is_trie handler out in
    handler, iterator, out

  let empty (Trie (is_trie, _)) = Trie.empty is_trie

  let add_or_replace (Trie (is_trie, _)) = Trie.add_or_replace is_trie

  let find_opt (Trie (is_trie, _)) = Trie.find_opt is_trie

  let mem (Trie (is_trie, _)) keys t =
    Option.is_some (Trie.find_opt is_trie keys t)

  let concat (Trie (is_trie, _)) ~earlier:t1 ~later:t2 =
    Trie.union is_trie (fun _ v -> Some v) t1 t2

  module Id = struct
    type ('t, 'k, 'v) t =
      { id : 't Type.Id.t;
        name : string;
        schema : 'k Column.hlist;
        repr : ('t, 'k, 'v) repr
      }

    let repr { repr; _ } = repr

    type ('k, 'v) poly = Id : ('t, 'k, 'v) t -> ('k, 'v) poly

    let print ppf t = Format.fprintf ppf "%s" t.name

    let create (type a b c) ~name ((module Schema) : (a, b, c) Schema.t) =
      { id = Type.Id.make ();
        name;
        schema = Schema.schema;
        repr = Trie (Schema.is_trie, Schema.Value.default)
      }

    let[@inline] uid { id; _ } = Type.Id.uid id

    let[@inline] schema { schema; _ } = schema

    let[@inline] cast_exn (type a b k v k' v') (r1 : (a, k, v) t)
        (r2 : (b, k', v') t) (t : a) : b =
      match Type.Id.provably_equal r1.id r2.id with
      | Some Equal -> t
      | None -> Misc.fatal_error "Inconsistent type for uid."
  end

  module Iterator = Trie.Iterator

  let print_table id ppf table =
    Format.fprintf ppf "@[<v>%a@]"
      (print id.Id.repr (fun keys _ ->
           Format.fprintf ppf "@[%a(%a).@]" Id.print id
             (Schema.print_values (Id.schema id))
             keys))
      table

  let print id ppf table =
    let header = Format.asprintf "%a" Id.print id in
    Format.fprintf ppf "@[<v>%s@ %s@ %a@]" header
      (String.make (String.length header) '=')
      (print_table id) table

  module type S = sig
    include Schema.S

    val id : (t, keys, Value.t) Id.t
  end

  module Make (N : Name) (S : Schema.S) = struct
    include S

    let id = Id.create ~name:N.name (module S)
  end

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
      Int.Map.add (Id.uid id) (Binding (id, table)) tables

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

type binder = Bind_table : ('t, 'k, 'v) Table.Id.t * 't ref -> binder

type 'k relation = ('k, unit) Table.Id.poly

type 'a rel1 = ('a -> nil) relation

type ('a, 'b) rel2 = ('a -> 'b -> nil) relation

type ('a, 'b, 'c) rel3 = ('a -> 'b -> 'c -> nil) relation

(* START HIGH LEVEL STUFF *)

module Variable = struct
  type condition =
    | Negate : ('t, 'k, 'v) Table.Id.t * 'k Leapfrog.refs -> condition

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
    binders : binder list
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

let constant_order = -1

let where predicates f info =
  let info =
    List.fold_left
      (fun info (Atom (id, args)) ->
        let handler, iterators, _ = Table.iterator (Table.Id.repr id) in
        bind_atom ~order:constant_order info.post_parameters args iterators;
        { info with binders = Bind_table (id, handler) :: info.binders })
      info predicates
  in
  f info

let rec compile_terms : type a. a Term.hlist -> a Leapfrog.refs =
 fun vars ->
  match vars with
  | [] -> Refs_nil
  | term :: terms -> (
    match term with
    | Constant cte -> Refs_cons (ref (Some cte), compile_terms terms)
    | Parameter param -> Refs_cons (param.cell, compile_terms terms)
    | Variable var ->
      Refs_cons (Variable.get_or_create_output var, compile_terms terms))

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

let unless predicates f info =
  List.iter
    (fun (Atom (id, args)) ->
      let refs = compile_terms args in
      let post_level = find_last_binding info.post_parameters args in
      post_level.rev_conditions
        <- Negate (id, refs) :: post_level.rev_conditions)
    predicates;
  f info

let bind_database binders current =
  List.iter
    (fun (Bind_table (id, handler)) -> handler := Table.Map.get current id)
    binders

(* Seminaive evaluation iterates over all the {b new} tuples in the [diff]
   database that are not in the [previous] database.

   [current] must be equal to [concat ~earlier:previous ~later:diff]. *)
let[@inline] with_seminaive ~previous ~diff ~current binders f acc =
  bind_database binders current;
  let rec loop binders acc =
    match binders with
    | [] -> acc
    | Bind_table (relation, handler) :: binders ->
      handler := Table.Map.get diff relation;
      let acc = f acc in
      handler := Table.Map.get previous relation;
      loop binders acc
  in
  loop binders acc

module Join_iterator = Leapfrog.Join (Table.Iterator)
module Cursor0 = Leapfrog.Cursor (Join_iterator)

type action =
  | Add_incremental :
      { repr : ('t, 'k, unit) Table.repr;
        full : 't ref;
        diff : 't ref;
        keys : 'k Leapfrog.refs
      }
      -> action
  | Bind_iterator : 'a option ref * 'a Table.Iterator.t -> action
  | Unless : ('t, 'k, 'v) Table.Id.t * 'k Leapfrog.refs -> action

let evaluate op input =
  match op with
  | Add_incremental { repr; full; diff; keys } -> (
    let table = !full in
    let keys = Leapfrog.get_refs keys in
    match Table.find_opt repr keys table with
    | Some _ ->
      (* CR bclement: support updates for non-unit values. *)
      Leapfrog.Accept
    | None ->
      diff := Table.add_or_replace repr keys () !diff;
      full := Table.add_or_replace repr keys () table;
      Leapfrog.Accept)
  | Bind_iterator (value, it) -> (
    let value = Option.get !value in
    Table.Iterator.init it;
    Table.Iterator.seek it value;
    match Table.Iterator.current it with
    | Some found when Table.Iterator.equal_key it found value ->
      Table.Iterator.accept it;
      Leapfrog.Accept
    | None | Some _ -> Leapfrog.Skip)
  | Unless (id, args) ->
    if Table.mem (Table.Id.repr id) (Leapfrog.get_refs args)
         (Table.Map.get input id)
    then Leapfrog.Skip
    else Leapfrog.Accept

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
        Cursor0.seq (Unless (id, args)) instruction)
      instruction post_level.Variable.rev_conditions
  in
  let instruction =
    List.fold_left
      (fun instruction (Variable.Set_iterator (value, it)) ->
        Cursor0.seq (Bind_iterator (value, it)) instruction)
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
    let instruction = postprocess var.post_level instruction in
    Cursor0.open_
      (Join_iterator.create var.iterators)
      (match var.output with
      | Some output -> Cursor0.set_output output instruction
      | None -> instruction)

let rec push_vars :
    type s y.
    instruction:(action, y, s) Cursor0.instruction ->
    s Variable.hlist ->
    (action, y, nil) Cursor0.instruction =
 fun ~instruction vars ->
  match vars with
  | [] -> instruction
  | var :: vars -> push_vars ~instruction:(make_level var instruction) vars

(* Optimisation: if we do not use the output from the last variable, we only
   need the first matching value of that variable. *)
let rec pop_vars :
    type s. s Variable.hlist -> (action, 'y, s) Cursor0.instruction = function
  | [] -> Cursor0.advance
  | var :: vars -> (
    match var.output with
    | None -> Cursor0.pop (pop_vars vars)
    | _ -> Cursor0.advance)

module Cursor = struct
  let rec bind_parameters :
      type a. a Parameter.hlist -> a Constant.hlist -> unit =
   fun params values ->
    match params, values with
    | [], [] -> ()
    | param :: params', value :: values' ->
      param.cell := Some value;
      bind_parameters params' values'

  let create_state input instruction =
    Cursor0.create ~evaluate input instruction

  type ('p, 'y) cursor =
    { parameters : 'p Parameter.hlist;
      binders : binder list;
      instruction : (action, 'y, nil) Cursor0.instruction
    }

  type ('p, 'v) with_parameters = ('p, 'v Constant.hlist) cursor

  type 'v t = (nil, 'v) with_parameters

  let fold_with_parameters cursor parameters database ~init ~f =
    bind_parameters cursor.parameters parameters;
    bind_database cursor.binders database;
    Cursor0.fold f (create_state database cursor.instruction) init

  let fold cursor database ~init ~f =
    bind_database cursor.binders database;
    Cursor0.fold f (create_state database cursor.instruction) init

  let iter_with_parameters cursor parameters database ~f =
    bind_parameters cursor.parameters parameters;
    bind_database cursor.binders database;
    Cursor0.iter f (create_state database cursor.instruction)

  let iter cursor database ~f =
    bind_database cursor.binders database;
    Cursor0.iter f (create_state database cursor.instruction)

  let yield output (info : _ info) =
    let (Elist rev_vars) = info.variables.rev_vars in
    (* Must compile first because of execution order. *)
    let instruction = compile_terms output in
    let instruction = Cursor0.yield instruction (pop_vars rev_vars) in
    let instruction = push_vars ~instruction rev_vars in
    let instruction = postprocess info.post_parameters instruction in
    { parameters = info.parameters; binders = info.binders; instruction }

  let create variables f =
    compile variables @@ fun variables -> where (f variables) @@ yield variables

  let create_with_parameters ~parameters variables f =
    compile variables (fun variables ->
        with_parameters parameters (fun parameters ->
            where (f parameters variables) @@ yield variables))
end

type rule =
  | Rule :
      { binders : binder list;
        instruction : (action, nil, nil) Cursor0.instruction;
        table_id : ('t, 'k, 'v) Table.Id.t;
        current_table : 't ref;
        diff_table : 't ref
      }
      -> rule

let deduce (Atom (tid, args)) (info : _ info) =
  let [] = info.parameters in
  let empty = Table.empty (Table.Id.repr tid) in
  let current_table = ref empty in
  let diff_table = ref empty in
  let instruction =
    Add_incremental
      { repr = Table.Id.repr tid;
        full = current_table;
        diff = diff_table;
        keys = compile_terms args
      }
  in
  let instruction =
    let (Elist rev_vars) = info.variables.rev_vars in
    let instruction = Cursor0.seq instruction (pop_vars rev_vars) in
    let instruction = push_vars ~instruction rev_vars in
    let instruction = postprocess info.post_parameters instruction in
    instruction
  in
  Rule
    { binders = info.binders;
      instruction;
      table_id = tid;
      current_table;
      diff_table
    }

type database = Table.Map.t

let empty = Table.Map.empty

let table_relation table = Table.Id.Id table

(* We could expose the fact that we do not support relations without arguments
   in the types, but a runtime error here allows us to give a better error
   message. Plus, we might support constant relations (represented as an option)
   in the future. *)
let create_relation (type k) ~name (schema : k Column.hlist) :
    (k, _) Table.Id.poly =
  match schema with
  | [] -> Misc.fatal_error "Cannot create relations with no arguments."
  | _ :: _ ->
    let (Any schema) = Schema.dyn schema (module Schema.Unit) in
    table_relation (Table.Id.create ~name schema)

let add_fact (Table.Id.Id id) args db =
  Table.Map.set db id
    (Table.add_or_replace (Table.Id.repr id) args () (Table.Map.get db id))

let get_table id db = Table.Map.get db id

let set_table id table db = Table.Map.set db id table

let print = Table.Map.print

module Schedule = struct
  type t =
    | Saturate of rule list * Table.Map.t * int
    | Fixpoint of t list

  let fixpoint schedule = Fixpoint schedule

  let saturate rules = Saturate (rules, Table.Map.empty, -999)

  let run_rules rules ~previous ~diff ~current =
    let run_step (db_new, db_diff)
        (Rule { table_id; binders; instruction; current_table; diff_table }) =
      let table_new = Table.Map.get db_new table_id in
      let table_diff = Table.Map.get db_diff table_id in
      current_table := table_new;
      diff_table := table_diff;
      let () =
        with_seminaive ~previous ~diff ~current binders
          (fun () ->
            Cursor0.iter ignore (Cursor0.create ~evaluate current instruction))
          ()
      in
      let set_if_changed db ~before ~after =
        if after == before then db else Table.Map.set db table_id after
      in
      ( set_if_changed db_new ~before:table_new ~after:!current_table,
        set_if_changed db_diff ~before:table_diff ~after:!diff_table )
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

  let rec run0 schedule ~previous ~diff ~current =
    match schedule with
    | Saturate (rules, _, _) -> saturate_rules rules ~previous ~diff ~current
    | Fixpoint schedules ->
      run_list (List.map run0 schedules) ~previous ~diff ~current

  let run schedule db =
    fst (run0 schedule ~previous:Table.Map.empty ~diff:db ~current:db)
end
