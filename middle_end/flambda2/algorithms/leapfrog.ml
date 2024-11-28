module type Iterator = sig
  type key

  val compare_key : key -> key -> int

  val equal_key : key -> key -> bool

  type 'a t

  type 'a is_value [@@immediate]

  val current_key : 'a t -> key option

  (** Raises [Not_found]. *)
  val current_data_exn : 'a t -> 'a

  val advance : 'a t -> key option

  val seek : 'a t -> key -> key option
end

module Iterator_operations (Iterator : Iterator) = struct
  type key = Iterator.key

  let compare_key = Iterator.compare_key

  let equal_key = Iterator.equal_key

  type _ is_value = Array : _ array is_value

  type 'a t = Join : { iterators : 'a Iterator.t array } -> 'a array t

  let empty = Join { iterators = [||] }

  let current_key (type a) (t : a t) =
    let (Join { iterators }) = t in
    if Array.length iterators = 0
    then None
    else Iterator.current_key iterators.(0)

  let current_data_exn (type a) (t : a t) : a =
    let (Join { iterators }) = t in
    Array.map Iterator.current_data_exn iterators

  let rec search0 iterators index_of_lowest_key highest_key =
    let iterator_with_lowest_key = iterators.(index_of_lowest_key) in
    match Iterator.current_key iterator_with_lowest_key with
    | None -> None
    | Some lowest_key -> (
      if Iterator.equal_key lowest_key highest_key
      then (* All iterators are on the same key. *)
        Some highest_key
      else
        (* lowest_key < highest_key *)
        match Iterator.seek iterator_with_lowest_key highest_key with
        | None -> None
        | Some new_highest_key ->
          search0 iterators
            ((index_of_lowest_key + 1) mod Array.length iterators)
            new_highest_key)

  let search iterators highest_key = search0 iterators 0 highest_key

  let advance (type a) (t : a t) =
    let (Join { iterators }) = t in
    match Iterator.advance iterators.(Array.length iterators - 1) with
    | None -> None
    | Some highest_key -> search iterators highest_key

  let seek (type a) (t : a t) key =
    let (Join { iterators }) = t in
    match Iterator.seek iterators.(Array.length iterators - 1) key with
    | None -> None
    | Some highest_key -> search iterators highest_key

  let join_array iters =
    if Array.exists (fun it -> Option.is_none (Iterator.current_key it)) iters
    then empty
    else
      let sorted_iterators = Array.copy iters in
      Array.sort
        (fun it1 it2 ->
          match Iterator.current_key it1, Iterator.current_key it2 with
          | None, None | None, Some _ | Some _, None -> assert false
          | Some k1, Some k2 -> Iterator.compare_key k1 k2)
        sorted_iterators;
      match Iterator.current_key iters.(Array.length iters - 1) with
      | None ->
        (* We have just checked *)
        assert false
      | Some highest_key -> (
        match search sorted_iterators highest_key with
        | None -> empty
        | Some _ ->
          (* All the iterators must be on the same key, so we can reuse the
             original array from now on, so that the output is in the expected
             order. *)
          Join { iterators = iters })
end
