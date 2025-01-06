(* module type S = sig type key

   type keys

   type 'a t

   val empty : 'a t

   val is_empty : 'a t -> bool

   val singleton : keys Constant.hlist -> 'a -> 'a t

   val add_or_replace : keys Constant.hlist -> 'a -> 'a t -> 'a t

   val remove : keys Constant.hlist -> 'a t -> 'a t

   val union : ('a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

   val find : keys Constant.hlist -> 'a t -> 'a

   val find_opt : keys Constant.hlist -> 'a t -> 'a option

   module Iterator : sig type iterator

   type 'a value

   val create : 'a t ref -> 'a value ref -> iterator

   val current : iterator -> key option

   val advance : iterator -> unit

   val seek : iterator -> key -> unit

   val init : iterator -> unit

   val accept : iterator -> unit end end

   module Make (X : Container_types.S_plus_iterator) : S with type key = X.t and
   type keys = X.t -> nil and type 'a Iterator.value = 'a option = struct type
   key = X.t

   type keys = X.t -> nil

   type 'a t = 'a X.Map.t

   let empty = X.Map.empty

   let is_empty = X.Map.is_empty

   let singleton ([key] : keys Constant.hlist) value = X.Map.singleton key value

   let add_or_replace ([key] : keys Constant.hlist) value map = X.Map.add key
   value map

   let remove ([key] : keys Constant.hlist) map = X.Map.remove key map

   let union f m1 m2 = X.Map.union (fun _ left right -> f left right) m1 m2

   let find ([key] : keys Constant.hlist) map = X.Map.find key map

   let find_opt ([key] : keys Constant.hlist) map = X.Map.find_opt key map

   module Iterator = struct type iterator = | Iterator : { mutable iterator : 'v
   X.Map.iterator; map : 'v X.Map.t ref; output : 'v option ref } -> iterator

   type 'a value = 'a option

   let create mref vref = Iterator { iterator = X.Map.iterator !mref; map =
   mref; output = vref }

   let current (Iterator { iterator; _ }) = Option.map fst (X.Map.current
   iterator)

   let advance (Iterator i) = i.iterator <- X.Map.advance i.iterator

   let seek (Iterator i) key = i.iterator <- X.Map.seek i.iterator key

   let init (Iterator i) : unit = i.iterator <- X.Map.iterator !(i.map)

   let accept (Iterator i) = match X.Map.current i.iterator with | None ->
   invalid_arg "accept: iterator is exhausted" | Some (_, value) -> i.output :=
   Some value end end

   module Cons (X : Container_types.S_plus_iterator) (T : S) : S with type key =
   X.t and type keys = X.t -> T.keys and type 'a Iterator.value = 'a T.t =
   struct type key = X.t

   type keys = X.t -> T.keys

   type 'a t = 'a T.t X.Map.t

   let empty = X.Map.empty

   let is_empty = X.Map.is_empty

   let singleton (key :: keys : keys Constant.hlist) value = X.Map.singleton key
   (T.singleton keys value)

   let add_or_replace (key :: keys : keys Constant.hlist) value trie = match
   X.Map.find_opt key trie with | None -> X.Map.add key (T.singleton keys value)
   trie | Some m -> X.Map.add key (T.add_or_replace keys value m) trie

   let remove (key :: keys : keys Constant.hlist) trie = match X.Map.find_opt
   key trie with | None -> trie | Some subtrie -> let subtrie' = T.remove keys
   subtrie in if T.is_empty subtrie' then X.Map.remove key trie else X.Map.add
   key subtrie' trie

   let union f t1 t2 = X.Map.union (fun _ left right -> let subtrie = T.union f
   left right in if T.is_empty subtrie then None else Some subtrie) t1 t2

   let find (key :: keys : keys Constant.hlist) trie = T.find keys (X.Map.find
   key trie)

   let find_opt keys trie = match find keys trie with | exception Not_found ->
   None | datum -> Some datum

   module Iterator = struct type iterator = | Iterator : { mutable iterator : 'v
   T.t X.Map.iterator; map : 'v T.t X.Map.t ref; output : 'v T.t ref } ->
   iterator

   type 'a value = 'a T.t

   let create mref vref = Iterator { iterator = X.Map.iterator !mref; map =
   mref; output = vref }

   let current (Iterator { iterator; _ }) = Option.map fst (X.Map.current
   iterator)

   let advance (Iterator i) = i.iterator <- X.Map.advance i.iterator

   let seek (Iterator i) key = i.iterator <- X.Map.seek i.iterator key

   let init (Iterator i) : unit = i.iterator <- X.Map.iterator !(i.map)

   let accept (Iterator i) = match X.Map.current i.iterator with | None ->
   invalid_arg "accept: iterator is exhausted" | Some (_, value) -> i.output :=
   value end end *)
