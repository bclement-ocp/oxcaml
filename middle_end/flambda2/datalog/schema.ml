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

module type Value = sig
  type t

  val default : t
end

module Column = struct
  type (_, _, _) repr =
    | Patricia_tree_repr : ('a Patricia_tree.map, int, 'a) repr

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

module type S = sig
  type keys

  val print_keys : Format.formatter -> keys Constant.hlist -> unit

  module Value : Value

  type t

  val is_trie : (t, keys, Value.t) Trie.is_trie

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

  let print_keys ppf ([key] : keys Constant.hlist) = C.print ppf key

  module Value = V

  type t = V.t C.Map.t

  let is_trie : (t, keys, Value.t) Trie.is_trie =
    Column.trie_repr C.datalog_column_id.repr

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

  let print_keys ppf (key :: keys : keys Constant.hlist) =
    Format.fprintf ppf "%a,@ %a" C.print key S.print_keys keys

  module Value = S.Value

  type t = S.t C.Map.t

  let is_trie = Column.nested_trie_repr C.datalog_column_id.repr S.is_trie

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

type ('k, 'v) any = Any : ('t, 'k, 'v) t -> ('k, 'v) any [@@unboxed]

type 'v value = (module Value with type t = 'v)

let rec dyn : type k r v. (k -> r) Column.hlist -> v value -> (k -> r, v) any =
 fun keys (module Value) ->
  match keys with
  | [(module C)] -> Any (module Make (C) (Value))
  | (module C) :: (_ :: _ as keys) ->
    let (Any (module S)) = dyn keys (module Value) in
    Any (module Cons (C) (S))
