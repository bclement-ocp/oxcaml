type 'a position =
  | At_start
  | Key of 'a
  | At_end

let compare_position compare_key p1 p2 =
  match p1, p2 with
  | At_start, At_start -> 0
  | At_start, (Key _ | At_end) -> -1
  | (Key _ | At_end), At_start -> 1
  | Key k1, Key k2 -> compare_key k1 k2
  | Key _, At_end -> -1
  | At_end, Key _ -> 1
  | At_end, At_end -> 0

module type Iterator = sig
  type key

  val compare_key : key -> key -> int

  val equal_key : key -> key -> bool

  val print_key : Format.formatter -> key -> unit

  type 'a t

  val current : 'a t -> key position

  val advance : 'a t -> unit

  val seek : 'a t -> key -> unit

  val down : 'a t -> unit

  val up : 'a t -> unit
end

module Iterator_operations (Iterator : Iterator) = struct
  type key = Iterator.key

  let compare_key = Iterator.compare_key

  let equal_key = Iterator.equal_key

  type 'a t =
    | Join :
        { iterators : 'a Iterator.t array;
          mutable at_end : bool
        }
        -> 'a t

  let current (type a) (t : a t) =
    let (Join { iterators; at_end }) = t in
    if at_end || Array.length iterators = 0
    then At_end
    else Iterator.current iterators.(Array.length iterators - 1)

  let rec search0 iterators index_of_lowest_key highest_key =
    let iterator_with_lowest_key = iterators.(index_of_lowest_key) in
    match Iterator.current iterator_with_lowest_key with
    | At_end -> At_end
    | Key lowest_key when Iterator.equal_key lowest_key highest_key ->
      (* All iterators are on the same key. *)
      Key lowest_key
    | At_start | Key _ -> (
      Iterator.seek iterator_with_lowest_key highest_key;
      match Iterator.current iterator_with_lowest_key with
      | At_start -> Misc.fatal_error "Impossibru"
      | At_end -> At_end
      | Key new_highest_key ->
        search0 iterators
          ((index_of_lowest_key + 1) mod Array.length iterators)
          new_highest_key)

  let search iterators highest_key = search0 iterators 0 highest_key

  let repair (Join ({ iterators; at_end } as j)) =
    assert (not at_end);
    match Iterator.current iterators.(Array.length iterators - 1) with
    | At_start -> assert false
    | At_end -> j.at_end <- true
    | Key highest_key -> (
      match search iterators highest_key with
      | At_end -> j.at_end <- true
      | At_start | Key _ -> ())

  let advance (type a) (t : a t) =
    let (Join { iterators; at_end }) = t in
    if not at_end
    then (
      let highest_iterator = iterators.(Array.length iterators - 1) in
      Iterator.advance highest_iterator;
      repair t)

  let seek (type a) (t : a t) key =
    let (Join { iterators; at_end }) = t in
    if not at_end
    then (
      let highest_iterator = iterators.(Array.length iterators - 1) in
      Iterator.seek highest_iterator key;
      repair t)

  exception Empty_iterator

  let init (type a) (t : a t) =
    let (Join ({ iterators; at_end = _ } as j)) = t in
    try
      Array.iter
        (fun it ->
          match Iterator.current it with
          | At_end -> raise Empty_iterator
          | At_start | Key _ -> ())
        iterators;
      Array.sort
        (fun it1 it2 ->
          compare_position Iterator.compare_key (Iterator.current it1)
            (Iterator.current it2))
        iterators;
      j.at_end <- false;
      repair t
    with Empty_iterator -> j.at_end <- true

  let join_array iters = Join { iterators = iters; at_end = false }

  type 'a triejoin =
    { levels : 'a t array;
      mutable depth : int
    }

  let triejoin iters = { levels = iters; depth = -1 }

  let current { levels; depth } = current levels.(depth)

  let advance { levels; depth } = advance levels.(depth)

  let seek { levels; depth } = seek levels.(depth)

  let down ({ levels; depth } as t) =
    let depth = depth + 1 in
    t.depth <- depth;
    if depth >= Array.length levels
    then (
      Format.eprintf "@[Going down to depth %d with only %d variables.@]@."
        depth (Array.length levels);
      invalid_arg "down");
    let (Join ({ iterators; at_end = _ } as j) as join) = levels.(depth) in
    j.at_end <- false;
    Array.iter Iterator.down iterators;
    init join

  let up ({ levels; depth } as t) =
    if depth < 0 then invalid_arg "up";
    let (Join { iterators; at_end = _ }) = levels.(depth) in
    Array.iter Iterator.up iterators;
    t.depth <- depth - 1

  let reset t = t.depth <- -1
end
