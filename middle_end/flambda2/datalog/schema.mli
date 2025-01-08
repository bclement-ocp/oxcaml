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

module Unit : Value with type t = unit

module Column : sig
  type ('t, 'k, 'v) id

  module type S = sig
    type t

    val print : Format.formatter -> t -> unit

    module Set : Container_types.Set with type elt = t

    module Map :
      Container_types.Map_plus_iterator with type key = t with module Set = Set

    val datalog_column_id : ('a Map.t, t, 'a) id
  end

  module Make (_ : sig
    val name : string

    val print : Format.formatter -> int -> unit
  end) : S with type t = int

  type 'a t = (module S with type t = 'a)

  include Heterogenous_list.S with type 'a t := 'a t
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

type ('t, 'k, 'v) t =
  (module S with type t = 't and type keys = 'k and type Value.t = 'v)

module Make (C : Column.S) (V : Value) :
  S
    with type keys = C.t -> Heterogenous_list.nil
     and module Value = V
     and type t = V.t C.Map.t

module Cons (C : Column.S) (S : S) :
  S
    with type keys = C.t -> S.keys
     and module Value = S.Value
     and type t = S.t C.Map.t

type 'v value = (module Value with type t = 'v)

type ('k, 'v) any = Any : ('t, 'k, 'v) t -> ('k, 'v) any [@@unboxed]

val dyn : ('k -> 'r) Column.hlist -> 'v value -> ('k -> 'r, 'v) any
