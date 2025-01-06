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

open Heterogenous_list

type ('m, 'k, 'v) repr

val patricia_tree_repr :
  ('a Patricia_tree.Make(Numbers.Int).Map.t, int, 'a) repr

(** [('t, 'k, 'v) is_trie] is a witness that the type ['t] is a trie from keys
    of type ['k Constant.hlist] to values of type ['v]. *)
type ('t, 'k, 'v) is_trie

val map_of_value : ('m, 'k, 'v) repr -> ('m, 'k -> nil, 'v) is_trie

val map_of_trie :
  ('m, 'k, 's) repr -> ('s, 'b, 'v) is_trie -> ('m, 'k -> 'b, 'v) is_trie

(** Existential witness for tries of given key and value types.

   {b Note}: This type is currently unused by the [Trie] module, but is provided
   as a convenience for users that need to create existentially quantified
   tries. *)
type ('k, 'v) is_any_trie =
  | Is_trie : ('t, 'k, 'v) is_trie -> ('k, 'v) is_any_trie

val empty : ('t, 'k, 'v) is_trie -> 't

val is_empty : ('t, 'k, 'v) is_trie -> 't -> bool

val singleton : ('t, 'k, 'v) is_trie -> 'k Constant.hlist -> 'v -> 't

val add_or_replace : ('t, 'k, 'v) is_trie -> 'k Constant.hlist -> 'v -> 't -> 't

val remove : ('t, 'k, 'v) is_trie -> 'k Constant.hlist -> 't -> 't

val union : ('t, 'k, 'v) is_trie -> ('v -> 'v -> 'v option) -> 't -> 't -> 't

val find_opt : ('t, 'k, 'v) is_trie -> 'k Constant.hlist -> 't -> 'v option

module Iterator : sig
  include Leapfrog.Iterator

  (** [create is_trie input output] creates a trie iterator.

      The [input] reference is used to initialize the first iterator when [init]
      is called.

      The [output] reference is set to the corresponding value when [accept] is
      called on the last iterator.
  *)
  val create : ('m, 'k, 'v) is_trie -> 'm ref -> 'v ref -> 'k hlist
end

module type Key = sig
  type t

  module Map : Container_types.Map_plus_iterator with type key = t

  val datalog_column_repr : ('a Map.t, t, 'a) repr
end

module type S = sig
  type keys

  type 'a t

  val is_trie : ('a t, keys, 'a) is_trie

  val empty : 'a t
  (* Put in the signature to work around the value restriction. *)
end

module Make (X : Key) : S with type keys = X.t -> nil and type 'a t = 'a X.Map.t

module Cons (X : Key) (T : S) :
  S with type keys = X.t -> T.keys and type 'a t = 'a T.t X.Map.t

module Make1 (X : Key) :
  S with type keys = X.t -> nil and type 'a t = 'a X.Map.t

module Make2 (X1 : Key) (X2 : Key) :
  S
    with type keys = X1.t -> Make1(X2).keys
     and type 'a t = 'a Make1(X2).t X1.Map.t

module Make3 (X1 : Key) (X2 : Key) (X3 : Key) :
  S
    with type keys = X1.t -> Make2(X2)(X3).keys
     and type 'a t = 'a Make2(X2)(X3).t X1.Map.t

module Make4 (X1 : Key) (X2 : Key) (X3 : Key) (X4 : Key) :
  S
    with type keys = X1.t -> Make3(X2)(X3)(X4).keys
     and type 'a t = 'a Make3(X2)(X3)(X4).t X1.Map.t
