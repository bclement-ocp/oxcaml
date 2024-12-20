open Datalog_types

(** [('m, 'k, 'v) is_map] is a witness that the type ['m] is a map from keys
    of type ['k] to values of type ['v]. *)
type ('m, 'k, 'v) is_map

val is_map : ('v Patricia_tree.Make(Numbers.Int).Map.t, int, 'v) is_map

type ('t, 'k, 'v) is_trie

val value_is_trie : ('a, 'b option, 'a) is_trie

val map_is_trie :
  ('t, 'a, 's) is_map -> ('s, 'b, 'v) is_trie -> ('t, 'a -> 'b, 'v) is_trie

type ('k, 'v) is_any_trie =
  | Is_trie : ('t, 'k, 'v) is_trie -> ('k, 'v) is_any_trie

val empty : ('t, 'k -> 'r, 'v) is_trie -> 't

val add_or_replace : ('t, 'k, 'v) is_trie -> 'k Constant.hlist -> 'v -> 't -> 't

val remove_refs : ('t, 'k, 'v) is_trie -> 'k Ref.hlist -> 't -> 't

val find_opt : ('t, 'k, 'v) is_trie -> 'k Constant.hlist -> 't -> 'v option

val find_opt_refs : ('t, 'k, 'v) is_trie -> 'k Ref.hlist -> 't -> 'v option

module Iterator : sig
  include Iterator

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist
end

val create_iterator : ('m, 'k, 'v) is_map -> 'm ref -> 'v ref -> 'k Iterator.t

val iterators :
  ('m, 'k -> 'r, 'v) is_trie -> 'v ref -> 'm ref * ('k -> 'r) Iterator.hlist

val iter :
  ('t, 'k, 'v) is_trie -> ('k Constant.hlist -> 'v -> unit) -> 't -> unit

val fold :
  ('t, 'k, 'v) is_trie ->
  ('k Constant.hlist -> 'v -> 'a -> 'a) ->
  't ->
  'a ->
  'a
