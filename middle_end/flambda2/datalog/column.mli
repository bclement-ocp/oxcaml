type ('t, 'k, 'v) id

val trie_repr :
  ('t, 'k, 'v) id -> ('t, 'k -> Heterogenous_list.nil, 'v) Trie.is_trie

val nested_trie_repr :
  ('t, 'k, 's) id ->
  ('s, 'r, 'v) Trie.is_trie ->
  ('t, 'k -> 'r, 'v) Trie.is_trie

module type S = sig
  type t

  val print : Format.formatter -> t -> unit

  module Set : Container_types.Set with type elt = t

  module Map :
    Container_types.Map_plus_iterator with type key = t with module Set = Set

  val datalog_column_id : ('a Map.t, t, 'a) id
end

type 'a t = (module S with type t = 'a)

include Heterogenous_list.S with type 'a t := 'a t

module Make (_ : sig
  val name : string

  val print : Format.formatter -> int -> unit
end) : S with type t = int
