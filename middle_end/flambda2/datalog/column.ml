open Heterogenous_list

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

let trie_repr { repr; _ } = trie_repr repr

let nested_trie_repr { repr; _ } is_trie = nested_trie_repr repr is_trie

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
