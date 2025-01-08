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

module Datalog = struct
  type nil = Heterogenous_list.nil

  include Datalog
  module Constant = Heterogenous_list.Constant
  module Column = Schema.Column

  module Schema = struct
    include Schema

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

      val id : (t, keys, Value.t) Id.t
    end

    module Make (N : sig
      val name : string
    end)
    (S : Schema.S) =
    struct
      include S

      let id =
        Id.create ~name:N.name ~is_trie:S.is_trie ~print_keys:S.print_keys
          ~default_value:S.Value.default
    end

    module type Relation = S with module Value = Schema.Unit
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
