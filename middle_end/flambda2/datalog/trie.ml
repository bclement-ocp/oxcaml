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

module Int = struct
  include Numbers.Int
  module Tree = Patricia_tree.Make (Numbers.Int)
  module Map = Tree.Map
  module Set = Tree.Set
end

type (_, _, _) is_trie =
  | Nil : ('v, nil, 'v) is_trie
  | Cons : ('s, 'b, 'v) is_trie -> ('s Int.Map.t, int -> 'b, 'v) is_trie

type ('k, 'v) is_any_trie =
  | Is_trie : ('t, 'k, 'v) is_trie -> ('k, 'v) is_any_trie

let nil = Nil

let patricia_tree_is_trie = Cons Nil

let patricia_tree_of_trie is_trie = Cons is_trie

let empty_or_null : type t k v. (t, k, v) is_trie -> t Or_null.t =
 fun w ->
  match w with Nil -> Or_null.null | Cons _ -> Or_null.this Int.Map.empty

let is_empty : type t k v. (t, k, v) is_trie -> t -> bool = function
  | Nil -> fun _ -> false
  | Cons _ -> Int.Map.is_empty

let rec find_or_null : type t k v.
    (t, k, v) is_trie -> k Constant.hlist -> t -> v Or_null.t =
 fun w k t ->
  match k, w with
  | [], Nil -> Or_null.this t
  | k :: ks, Cons w' -> (
    match Int.Map.find_or_null k t with
    | Null -> Or_null.null
    | This datum -> find_or_null w' ks datum)

let find_opt w k t = Or_null.to_option (find_or_null w k t)

let rec singleton : type t k v. (t, k, v) is_trie -> k Constant.hlist -> v -> t
    =
 fun w k v ->
  match k, w with
  | [], Nil -> v
  | k :: ks, Cons w' -> Int.Map.singleton k (singleton w' ks v)

let rec union_total : type t k v.
    (t, k, v) is_trie -> (v -> v -> v) -> t -> t -> t =
 fun w f t1 t2 ->
  match w with
  | Nil -> f t1 t2
  | Cons w' ->
    Int.Map.union_total (fun _ left right -> union_total w' f left right) t1 t2

let add_or_replace w ks v t = union_total w (fun _ v -> v) t (singleton w ks v)

let rec diff_or_null : type t k v.
    (t, k, v) is_trie -> (v -> v -> v Or_null.t) -> t -> t -> t Or_null.t =
 fun w f t1 t2 ->
  match w with
  | Nil -> f t1 t2
  | Cons w' ->
    let t =
      Int.Map.diff_sharing
        (fun _ left right ->
          match diff_or_null w' f left right with
          | Null -> None
          | This datum -> Some datum)
        t1 t2
    in
    if Int.Map.is_empty t then Or_null.null else Or_null.this t

let rec iter : type t k v.
    (t, k, v) is_trie -> (k Constant.hlist -> v -> unit) -> t -> unit =
 fun w f t ->
  match w with
  | Nil -> f [] t
  | Cons w' ->
    Int.Map.iter (fun k t' -> iter w' (fun ks v -> f (k :: ks) v) t') t

let rec fold : type t k v.
    (t, k, v) is_trie -> (k Constant.hlist -> v -> 'a -> 'a) -> t -> 'a -> 'a =
 fun is_trie f t acc ->
  match is_trie with
  | Nil -> f [] t acc
  | Cons w' ->
    Int.Map.fold
      (fun k t' acc -> fold w' (fun ks v acc -> f (k :: ks) v acc) t' acc)
      t acc

module Iterator = struct
  include Leapfrog.Map (Int)

  let create : type m k v.
      (m, k -> nil, v) is_trie ->
      m Channel.or_null_receiver ->
      v Channel.or_null_sender ->
      k t =
   fun (Cons Nil) -> create
end
