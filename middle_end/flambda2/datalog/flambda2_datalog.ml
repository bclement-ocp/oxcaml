(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Basile Clément, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2024--2025 OCamlPro SAS                                    *)
(*   Copyright 2024--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Heterogenous_list

module Datalog = struct
  type nonrec nil = nil

  module Constant = Constant

  module type Value = sig
    type t

    val default : t
  end

  module Unit = struct
    type t = unit

    let default = ()
  end

  module Column = struct
    type (_, _, _) repr =
      | Patricia_tree_repr : ('a Patricia_tree.map, int, 'a) repr

    let trie_repr : type a b c. (a, b, c) repr -> (a, b -> nil, c) Trie.is_trie
        =
     fun Patricia_tree_repr -> Trie.patricia_tree_is_trie

    let nested_trie_repr :
        type a b c d e.
        (a, b, c) repr -> (c, d, e) Trie.is_trie -> (a, b -> d, e) Trie.is_trie
        =
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
        Container_types.Map_plus_iterator
          with type key = t
          with module Set = Set

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

  include Datalog

  module Schema = struct
    module type S = sig
      type keys

      val print_keys : Format.formatter -> keys Constant.hlist -> unit

      module Value : Value

      type t

      val is_trie : (t, keys, Value.t) Trie.is_trie
    end

    module Make_ops (T : S) = struct
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
      S
        with type keys = C.t -> nil
         and module Value = V
         and type t = V.t C.Map.t = struct
      type keys = C.t -> nil

      let print_keys ppf ([key] : keys Constant.hlist) = C.print ppf key

      module Value = V

      type t = V.t C.Map.t

      let is_trie : (t, keys, Value.t) Trie.is_trie =
        Column.trie_repr C.datalog_column_id.repr
    end

    module Cons (C : Column.S) (S : S) :
      S
        with type keys = C.t -> S.keys
         and module Value = S.Value
         and type t = S.t C.Map.t = struct
      type keys = C.t -> S.keys

      let print_keys ppf (key :: keys : keys Constant.hlist) =
        Format.fprintf ppf "%a,@ %a" C.print key S.print_keys keys

      module Value = S.Value

      type t = S.t C.Map.t

      let is_trie = Column.nested_trie_repr C.datalog_column_id.repr S.is_trie
    end

    module Unit = struct
      type t = unit

      let default = ()
    end

    type ('k, 'v) any = Any : ('t, 'k, 'v) t -> ('k, 'v) any [@@unboxed]

    type 'v value = (module Value with type t = 'v)

    let rec dyn :
        type k r v. (k -> r) Column.hlist -> v value -> (k -> r, v) any =
     fun keys (module Value) ->
      match keys with
      | [(module C)] -> Any (module Make (C) (Value))
      | (module C) :: (_ :: _ as keys) ->
        let (Any (module S)) = dyn keys (module Value) in
        Any (module Cons (C) (S))

    module type Relation = S with type Value.t = unit

    module type C = Column.S

    module Relation1 (C1 : C) = Make (C1) (Unit)
    module Relation2 (C1 : C) (C2 : C) = Cons (C1) (Relation1 (C2))
    module Relation3 (C1 : C) (C2 : C) (C3 : C) =
      Cons (C1) (Relation2 (C2) (C3))
    module Relation4 (C1 : C) (C2 : C) (C3 : C) (C4 : C) =
      Cons (C1) (Relation3 (C2) (C3) (C4))
  end

  module Table = struct
    include Table

    module type S = sig
      include Schema.S

      val empty : t

      val is_empty : t -> bool

      val singleton : keys Constant.hlist -> Value.t -> t

      val add_or_replace : keys Constant.hlist -> Value.t -> t -> t

      val remove : keys Constant.hlist -> t -> t

      val union : (Value.t -> Value.t -> Value.t option) -> t -> t -> t

      val find_opt : keys Constant.hlist -> t -> Value.t option

      val id : (t, keys, Value.t) Id.t
    end

    module Make (N : sig
      val name : string
    end)
    (S : Schema.S) =
    struct
      include S
      include Schema.Make_ops (S)

      let id =
        Id.create ~name:N.name ~is_trie:S.is_trie ~print_keys:S.print_keys
          ~default_value:S.Value.default
    end

    module type Relation = S with module Value = Schema.Unit

    module Relation1 (N : sig
      val name : string
    end)
    (C1 : Column.S) =
      Make (N) (Schema.Relation1 (C1))
    module Relation2 (N : sig
      val name : string
    end)
    (C1 : Column.S)
    (C2 : Column.S) =
      Make (N) (Schema.Relation2 (C1) (C2))
    module Relation3 (N : sig
      val name : string
    end)
    (C1 : Column.S)
    (C2 : Column.S)
    (C3 : Column.S) =
      Make (N) (Schema.Relation3 (C1) (C2) (C3))
    module Relation4 (N : sig
      val name : string
    end)
    (C1 : Column.S)
    (C2 : Column.S)
    (C3 : Column.S)
    (C4 : Column.S) =
      Make (N) (Schema.Relation4 (C1) (C2) (C3) (C4))
  end

  type 'k relation = ('k, unit) Table.Id.poly

  type 'a rel1 = ('a -> nil) relation

  type ('a, 'b) rel2 = ('a -> 'b -> nil) relation

  type ('a, 'b, 'c) rel3 = ('a -> 'b -> 'c -> nil) relation

  type ('a, 'b, 'c, 'd) rel4 = ('a -> 'b -> 'c -> 'd -> nil) relation

  let table_relation table = Table.Id.Id table

  (* We could expose the fact that we do not support relations without arguments
     in the types, but a runtime error here allows us to give a better error
     message. Plus, we might support constant relations (represented as an
     option) in the future. *)
  let create_relation (type k) ~name (schema : k Column.hlist) :
      (k, _) Table.Id.poly =
    match schema with
    | [] -> Misc.fatal_error "Cannot create relations with no arguments."
    | _ :: _ ->
      let (Any (module Schema)) = Schema.dyn schema (module Schema.Unit) in
      table_relation
        (Table.Id.create ~name ~is_trie:Schema.is_trie
           ~default_value:Schema.Value.default ~print_keys:Schema.print_keys)

  let add_fact (Table.Id.Id id) args db =
    Table.Map.set id
      (Trie.add_or_replace (Table.Id.is_trie id) args () (Table.Map.get id db))
      db

  type database = Table.Map.t

  let empty = Table.Map.empty

  let get_table = Table.Map.get

  let set_table = Table.Map.set

  let print = Table.Map.print

  module Schedule = Schedule

  type rule = Schedule.rule

  type atom = Atom : ('t, 'k, unit) Table.Id.t * 'k Term.hlist -> atom

  let deduce (`Atom (Atom (tid, args))) =
    Datalog.map_program (yield args) (fun cursor ->
        let cursor = Cursor.With_parameters.without_parameters cursor in
        Schedule.create_rule tid cursor)

  type hypothesis =
    [ `Atom of atom
    | `Not_atom of atom ]

  let atom (Table.Id.Id id) args = `Atom (Atom (id, args))

  let not (`Atom atom) = `Not_atom atom

  let where predicates f =
    List.fold_left
      (fun f predicate ->
        match predicate with
        | `Atom (Atom (id, args)) -> where_atom id args f
        | `Not_atom (Atom (id, args)) -> unless_atom id args f)
      f predicates

  module Cursor = struct
    type ('p, 'v) with_parameters = ('p, 'v) cursor
    (* ('p, (action, 'v Constant.hlist, nil) Cursor0.instruction) cursor *)

    type 'v t = (nil, 'v) with_parameters

    let create variables f =
      compile variables @@ fun variables ->
      where (f variables) @@ yield variables

    let create_with_parameters ~parameters variables f =
      compile variables (fun variables ->
          with_parameters parameters (fun parameters ->
              where (f parameters variables) @@ yield variables))

    let fold_with_parameters cursor parameters database ~init ~f =
      naive_fold cursor parameters database f init

    let fold cursor database ~init ~f = naive_fold cursor [] database f init

    let iter_with_parameters cursor parameters database ~f =
      naive_iter cursor parameters database f

    let iter cursor database ~f = naive_iter cursor [] database f
  end
end
