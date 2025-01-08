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

module type Iterator = sig
  include Heterogenous_list.S

  val current : 'a t -> 'a option

  val advance : 'a t -> unit

  val seek : 'a t -> 'a -> unit

  val init : 'a t -> unit

  val accept : 'a t -> unit

  val equal_key : 'a t -> 'a -> 'a -> bool

  val compare_key : 'a t -> 'a -> 'a -> int
end

module Join (Iterator : Iterator) : sig
  include Iterator

  val create : 'a Iterator.t list -> 'a t
end = struct
  type 'k t =
    { iterators : 'k Iterator.t array;
      mutable at_end : bool
    }

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)

  let current (type a) ({ iterators; at_end } : a t) : a option =
    if at_end
    then None
    else Iterator.current iterators.(Array.length iterators - 1)

  let rec search : type a. a Iterator.t array -> int -> a -> a option =
   fun iterators index_of_lowest_key highest_key ->
    let iterator_with_lowest_key = iterators.(index_of_lowest_key) in
    let equal = Iterator.equal_key iterator_with_lowest_key in
    match Iterator.current iterator_with_lowest_key with
    | None -> None
    | Some lowest_key when equal lowest_key highest_key ->
      (* All iterators are on the same key. *)
      Some lowest_key
    | Some _ -> (
      Iterator.seek iterator_with_lowest_key highest_key;
      match Iterator.current iterator_with_lowest_key with
      | None -> None
      | Some new_highest_key ->
        search iterators
          ((index_of_lowest_key + 1) mod Array.length iterators)
          new_highest_key)

  let repair (type a) ({ iterators; at_end } as j : a t) =
    assert (not at_end);
    if Array.length iterators > 1
    then
      let iterator = iterators.(Array.length iterators - 1) in
      match Iterator.current iterator with
      | None -> j.at_end <- true
      | Some highest_key -> (
        match search iterators 0 highest_key with
        | None -> j.at_end <- true
        | Some _ -> ())

  let advance (type a) ({ iterators; at_end } as t : a t) =
    if not at_end
    then (
      let highest_iterator = iterators.(Array.length iterators - 1) in
      Iterator.advance highest_iterator;
      repair t)

  let seek (type a) (t : a t) (key : a) =
    let { iterators; at_end } = t in
    if not at_end
    then (
      let highest_iterator = iterators.(Array.length iterators - 1) in
      Iterator.seek highest_iterator key;
      repair t)

  exception Empty_iterator

  let init (type a) ({ iterators; _ } as j : a t) =
    try
      Array.iter
        (fun (it : a Iterator.t) ->
          Iterator.init it;
          match Iterator.current it with
          | None -> raise Empty_iterator
          | Some _ -> ())
        iterators;
      Array.sort
        (fun (it1 : a Iterator.t) (it2 : a Iterator.t) ->
          let compare = Iterator.compare_key it1 in
          Option.compare compare (Iterator.current it1) (Iterator.current it2))
        iterators;
      j.at_end <- false;
      repair j
    with Empty_iterator -> j.at_end <- true

  let accept (type a) ({ iterators; at_end } : a t) =
    if at_end then invalid_arg "Joined_iterator.accept: iterator is exhausted";
    Array.iter Iterator.accept iterators

  let equal_key { iterators; _ } = Iterator.equal_key iterators.(0)

  let compare_key { iterators; _ } = Iterator.compare_key iterators.(0)

  let create (iterators : _ Iterator.t list) : _ t =
    match iterators with
    | [] -> invalid_arg "Joined_iterator.create: cannot join an empty list"
    | _ -> { iterators = Array.of_list iterators; at_end = false }
end
[@@inline always]

open Heterogenous_list

type outcome =
  | Accept
  | Skip

module Cursor (Iterator : Iterator) = struct
  type ('a, 'y, 's) instruction =
    | Advance : ('a, 'y, 's) instruction
    | Pop : ('x, 'y, 's) instruction -> ('x, 'y, 'a -> 's) instruction
    | Open :
        'b Iterator.t * ('a, 'y, 'b -> 's) instruction
        -> ('a, 'y, 's) instruction
    | Action : 'a * ('a, 'y, 's) instruction -> ('a, 'y, 's) instruction
    | Yield :
        'y Option_ref.hlist * ('a, 'y Constant.hlist, 's) instruction
        -> ('a, 'y Constant.hlist, 's) instruction
    | Set_output :
        'a option ref * ('x, 'y, 'a -> 's) instruction
        -> ('x, 'y, 'a -> 's) instruction

  let advance = Advance

  let pop i = Pop i

  let open_ i a = Open (i, a)

  let action a i = Action (a, i)

  let yield y i = Yield (y, i)

  let set_output r i = Set_output (r, i)

  type ('x, 'y, 's) stack =
    | Stack_nil : ('x, 'y, nil) stack
    | Stack_cons :
        'a * 'a Iterator.t * ('x, 'y, 'a -> 's) instruction * ('x, 'y, 's) stack
        -> ('x, 'y, 'a -> 's) stack

  type ('x, 'y) suspension =
    | Suspension :
        { stack : ('x, 'y, 's) stack;
          instruction : ('x, 'y, 's) instruction
        }
        -> ('x, 'y) suspension

  let exhausted = Suspension { stack = Stack_nil; instruction = Advance }

  let rec refs : type s. s Iterator.hlist -> s Option_ref.hlist = function
    | [] -> []
    | _ :: iterators -> ref None :: refs iterators

  type erev = Erev : 's Iterator.hlist * 's Option_ref.hlist -> erev

  let iterate :
      type x s. s Iterator.hlist -> (x, s Constant.hlist, nil) instruction =
   fun iterators ->
    let rec rev0 :
        type s. s Iterator.hlist -> s Option_ref.hlist -> erev -> erev =
     fun iterators refs acc ->
      match iterators, refs with
      | [], [] -> acc
      | iterator :: iterators, r :: refs ->
        let (Erev (rev_iterators, rev_refs)) = acc in
        rev0 iterators refs (Erev (iterator :: rev_iterators, r :: rev_refs))
    in
    let rs = refs iterators in
    let (Erev (rev_iterators, rev_refs)) = rev0 iterators rs (Erev ([], [])) in
    let rec loop :
        type y s.
        s Iterator.hlist ->
        s Option_ref.hlist ->
        (x, y Constant.hlist, s) instruction ->
        (x, y Constant.hlist, nil) instruction =
     fun iterators refs instruction ->
      match iterators, refs with
      | [], [] -> instruction
      | iterator :: iterators, r :: refs ->
        loop iterators refs (Open (iterator, Set_output (r, instruction)))
    in
    loop rev_iterators rev_refs (Yield (rs, Advance))

  type ('a, 'y) state0 = ('a, 'y) suspension * 'y option

  type ('i, 'a, 'y) state =
    | State :
        { input : 'i;
          mutable suspension : ('a, 'y) suspension
        }
        -> ('i, 'a, 'y) state

  module Make (A : sig
    type action

    type input

    val evaluate : action -> input -> outcome
  end) =
  struct
    let create input instruction =
      State
        { input; suspension = Suspension { stack = Stack_nil; instruction } }

    let[@inline] rec execute :
        type y s.
        'i ->
        ('a, y, s) stack ->
        ('a, y, s) instruction ->
        ('a, y) suspension * y option =
     fun input stack instruction ->
      let[@local] dispatch :
          type x y s.
          ('a, y, s) stack ->
          x Iterator.t ->
          ('a, y, x -> s) instruction ->
          ('a, y) state0 =
       fun stack iterator instruction ->
        match Iterator.current iterator with
        | Some current_key ->
          Iterator.accept iterator;
          execute input
            (Stack_cons (current_key, iterator, instruction, stack))
            instruction
        | None -> execute input stack Advance
      in
      match instruction with
      | Advance -> (
        match stack with
        | Stack_nil -> exhausted, None
        | Stack_cons (_, iterator, level, stack) ->
          Iterator.advance iterator;
          dispatch stack iterator level)
      | Open (iterator, next_level) ->
        Iterator.init iterator;
        dispatch stack iterator next_level
      | Pop instruction ->
        let (Stack_cons (_, _, _, stack)) = stack in
        execute input stack instruction
      | Set_output (r, instruction) ->
        let (Stack_cons (v, _, _, _)) = stack in
        r := Some v;
        execute input stack instruction
      | Yield (rs, instruction) ->
        Suspension { stack; instruction }, Some (Option_ref.get rs)
      | Action (op, instruction) -> (
        match (A.evaluate [@inlined hint]) op input with
        | Accept -> execute input stack instruction
        | Skip -> execute input stack Advance)

    let step : type y. (_, _, y) state -> y option =
     fun (State state) ->
      let (Suspension { stack; instruction }) = state.suspension in
      let suspension, outcome = execute state.input stack instruction in
      state.suspension <- suspension;
      outcome
  end
  [@@inline]

  type 'y t =
    | Cursor :
        { state : ('i, 'a, 'y) state;
          step : ('i, 'a, 'y) state -> 'y option
        }
        -> 'y t

  let create (type a i) ~(evaluate : a -> i -> outcome) input instruction =
    let module M = Make (struct
      type action = a

      type input = i

      let evaluate = evaluate
    end) in
    Cursor { state = M.create input instruction; step = M.step }

  type void = |

  let iterator iterators =
    let evaluate : void -> unit -> outcome = function _ -> . in
    create ~evaluate () (iterate iterators)

  let[@inline] fold f (Cursor { state; step }) init =
    let rec loop state acc =
      match step state with
      | Some output -> loop state (f output acc)
      | None -> acc
    in
    loop state init

  let[@inline] iter f state = fold (fun keys () -> f keys) state ()
end
