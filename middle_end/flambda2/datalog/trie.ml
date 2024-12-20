open Datalog_types

module Int = struct
  include Numbers.Int
  module Tree = Patricia_tree.Make (Numbers.Int)
  module Map = Tree.Map
end

type ('m, 'k, 'v) is_map = Is_map : ('v Int.Map.t, int, 'v) is_map

let is_map = Is_map

type (_, _, _) is_trie =
  | Value_is_trie : ('a, 'b option, 'a) is_trie
  | Map_is_trie :
      ('t, 'a, 's) is_map * ('s, 'b, 'v) is_trie
      -> ('t, 'a -> 'b, 'v) is_trie

type ('k, 'v) is_any_trie =
  | Is_trie : ('t, 'k, 'v) is_trie -> ('k, 'v) is_any_trie

let value_is_trie = Value_is_trie

let map_is_trie is_map is_trie = Map_is_trie (is_map, is_trie)

let empty : type t k r v. (t, k -> r, v) is_trie -> t = function
  | Map_is_trie (Is_map, _) -> Int.Map.empty

module Iterator = struct
  type _ t =
    | Iterator :
        { mutable iterator : 'v Int.Map.iterator;
          map : 'v Int.Map.t ref;
          handler : 'v handler
        }
        -> int t

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist

  let equal_key (type a) (Iterator _ : a t) : a -> a -> bool = Int.equal

  let compare_key (type a) (Iterator _ : a t) : a -> a -> int = Int.compare

  let current (type a) (Iterator i : a t) : a option =
    match Int.Map.current i.iterator with
    | Some (key, _) -> Some key
    | None -> None

  let advance (type a) (Iterator i : a t) : unit =
    i.iterator <- Int.Map.advance i.iterator

  let seek (type a) (Iterator i : a t) (k : a) : unit =
    i.iterator <- Int.Map.seek i.iterator k

  let init (type a) (Iterator i : a t) : unit =
    i.iterator <- Int.Map.iterator !(i.map)

  let accept (type a) (Iterator i : a t) : unit =
    match Int.Map.current i.iterator with
    | None -> invalid_arg "accept: iterator must have a value"
    | Some (_, value) -> (
      match i.handler with Ignore -> () | Set_ref r -> r := value)
end

let make_ref (type m k v) (Is_map : (m, k, v) is_map) : m ref =
  ref Int.Map.empty

let create_iterator (type m k v) (Is_map : (m, k, v) is_map) (cell : m ref)
    (handler : v handler) : k Iterator.t =
  Iterator.Iterator
    { iterator = Int.Map.iterator Int.Map.empty; map = cell; handler }

let rec create_iterators :
    type m k v r.
    (m, k -> r, v) is_trie -> m ref -> v handler -> (k -> r) Iterator.hlist =
 fun (Map_is_trie (is_map, is_trie)) this_ref value_handler ->
  match is_trie with
  | Value_is_trie -> [create_iterator is_map this_ref value_handler]
  | Map_is_trie (next_map, _) ->
    let next_ref = make_ref next_map in
    create_iterator is_map this_ref (Set_ref next_ref)
    :: create_iterators is_trie next_ref value_handler

let iterators :
    type m k v. (m, k, v) is_trie -> v handler -> m handler * k Iterator.hlist =
 fun is_trie handler ->
  match is_trie with
  | Value_is_trie -> handler, []
  | Map_is_trie (is_map, _) ->
    let next_ref = make_ref is_map in
    Set_ref next_ref, create_iterators is_trie next_ref handler

let rec iter :
    type t k v.
    (t, k, v) is_trie -> (k Constant.hlist -> v -> unit) -> t -> unit =
 fun w f t ->
  match w with
  | Value_is_trie -> f [] t
  | Map_is_trie (Is_map, w') ->
    Int.Map.iter (fun k t -> iter w' (fun k' v -> f (k :: k') v) t) t

let rec fold :
    type t k v a.
    (t, k, v) is_trie -> (k Constant.hlist -> v -> a -> a) -> t -> a -> a =
 fun w f t acc ->
  match w with
  | Value_is_trie -> f [] t acc
  | Map_is_trie (Is_map, w') ->
    Int.Map.fold
      (fun k t acc -> fold w' (fun k' v acc -> f (k :: k') v acc) t acc)
      t acc

let rec find_opt :
    type t k v. (t, k, v) is_trie -> k Constant.hlist -> t -> v option =
 fun w k t ->
  match k, w with
  | [], Value_is_trie -> Some t
  | k :: k', Map_is_trie (Is_map, w') -> (
    match Int.Map.find_opt k t with Some s -> find_opt w' k' s | None -> None)

let rec find_opt_refs :
    type t k v. (t, k, v) is_trie -> k Ref.hlist -> t -> v option =
 fun w k t ->
  match k, w with
  | [], Value_is_trie -> Some t
  | k :: k', Map_is_trie (Is_map, w') -> (
    let k = !k in
    match Int.Map.find_opt k t with
    | Some s -> find_opt_refs w' k' s
    | None -> None)

let rec singleton : type t k v. (t, k, v) is_trie -> k Constant.hlist -> v -> t
    =
 fun w k v ->
  match k, w with
  | [], Value_is_trie -> v
  | k :: k', Map_is_trie (Is_map, w') -> Int.Map.singleton k (singleton w' k' v)

let rec add_or_replace :
    type t k v. (t, k, v) is_trie -> k Constant.hlist -> v -> t -> t =
 fun w inputs output t ->
  match inputs, w with
  | [], Value_is_trie -> output
  | first_input :: other_inputs, Map_is_trie (Is_map, w') -> (
    match Int.Map.find_opt first_input t with
    | Some m ->
      Int.Map.add first_input (add_or_replace w' other_inputs output m) t
    | None -> Int.Map.add first_input (singleton w' other_inputs output) t)

let is_empty : type t k v. (t, k, v) is_trie -> t -> bool =
 fun w t ->
  match w with
  | Value_is_trie -> false
  | Map_is_trie (Is_map, _) -> Int.Map.is_empty t

let rec remove0 :
    type t k v.
    (t, k, v) is_trie -> t Int.Map.t -> int -> k Ref.hlist -> t -> t Int.Map.t =
 fun w t k k' m ->
  match k', w with
  | [], Value_is_trie -> Int.Map.remove k t
  | a :: b, Map_is_trie (Is_map, w') -> (
    let a = !a in
    match Int.Map.find_opt a m with
    | None -> t
    | Some m' ->
      let m' = remove0 w' m a b m' in
      if is_empty w m' then Int.Map.remove k t else Int.Map.add k m' t)

let remove_refs : type t k v. (t, k, v) is_trie -> k Ref.hlist -> t -> t =
 fun w k t ->
  match k, w with
  | [], Value_is_trie -> t
  | k :: k', Map_is_trie (Is_map, w') -> (
    let k = !k in
    match Int.Map.find_opt k t with None -> t | Some m -> remove0 w' t k k' m)
