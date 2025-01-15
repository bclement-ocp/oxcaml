open Heterogenous_list

type outcome =
  | Accept
  | Skip

module Make (Iterator : Leapfrog.Iterator) = struct
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

  type ('i, 'x, 'y, 's) stack =
    | Stack_nil : ('i, 'x, 'y, nil) stack
    | Stack_cons :
        'a
        * 'a Iterator.t
        * ('i, 'x, 'y, 'a -> 's) compiled
        * ('i, 'x, 'y, 's) stack
        -> ('i, 'x, 'y, 'a -> 's) stack

  and ('i, 'x, 'y) suspension =
    | Suspension :
        { stack : ('i, 'x, 'y, 's) stack;
          state : 'i;
          instruction : ('i, 'x, 'y, 's) compiled
        }
        -> ('i, 'x, 'y) suspension

  and ('i, 'x, 'y, 's) compiled =
    'i -> ('i, 'x, 'y, 's) stack -> ('i, 'x, 'y) suspension * 'y option

  type ('i, 'a, 'y) state = ('i, 'a, 'y) suspension ref

  module Make (A : sig
    type action

    type input

    val evaluate : action -> input -> outcome
  end) =
  struct
    let rec exhausted :
        type x y. _ -> (_, x, y, nil) stack -> (_, x, y) suspension * y option =
     fun state Stack_nil ->
      Suspension { state; stack = Stack_nil; instruction = exhausted }, None

    let rec advance :
        type x y s.
        A.input -> (_, x, y, s) stack -> (_, x, y) suspension * y option =
     fun input stack ->
      match stack with
      | Stack_nil -> exhausted input stack
      | Stack_cons (_, iterator, level, stack) -> (
        Iterator.advance iterator;
        match Iterator.current iterator with
        | Some current_key ->
          Iterator.accept iterator;
          level input (Stack_cons (current_key, iterator, level, stack))
        | None -> advance input stack)

    let pop :
        type i a x y s. (i, x, y, s) compiled -> (i, x, y, a -> s) compiled =
     fun k input (Stack_cons (_, _, _, stack)) -> k input stack

    let open_ :
        type a x y s.
        a Iterator.t -> (_, x, y, a -> s) compiled -> (_, x, y, s) compiled =
     fun iterator k input stack ->
      Iterator.init iterator;
      match Iterator.current iterator with
      | Some current_key ->
        Iterator.accept iterator;
        k input (Stack_cons (current_key, iterator, k, stack))
      | None -> advance input stack

    let action op k input stack =
      match (A.evaluate [@inlined hint]) op input with
      | Accept -> k input stack
      | Skip -> advance input stack

    let yield rs k : (_, _, _, _) compiled =
     fun state stack ->
      Suspension { state; stack; instruction = k }, Some (Option_ref.get rs)

    let set_output r k input (Stack_cons (v, _, _, _) as stack) =
      r := Some v;
      k input stack

    let rec compile :
        type y s.
        (A.action, y, s) instruction -> (A.input, A.action, y, s) compiled =
      function
      | Advance -> advance
      | Pop k -> pop (compile k)
      | Open (iterator, k) -> open_ iterator (compile k)
      | Action (a, k) -> action a (compile k)
      | Yield (rs, k) -> yield rs (compile k)
      | Set_output (r, k) -> set_output r (compile k)
  end
  [@@inline]

  let step : type y. (_, _, y) state -> y option =
   fun state ->
    let (Suspension { stack; state = input; instruction }) = !state in
    let suspension, outcome = instruction input stack in
    state := suspension;
    outcome

  type 'y t = State : ('i, 'a, 'y) state -> 'y t [@@unboxed]

  let create input instruction =
    State (ref (Suspension { state = input; stack = Stack_nil; instruction }))

  let compile (type a i) ~(evaluate : a -> i -> outcome) instruction :
      (_, _, _, _) compiled =
    let module M = Make (struct
      type action = a

      type input = i

      let evaluate = evaluate
    end) in
    M.compile instruction

  type void = |

  let iterator iterators =
    let evaluate : void -> unit -> outcome = function _ -> . in
    create () (compile ~evaluate (iterate iterators))

  let[@inline] fold f (State state) init =
    let rec loop state acc =
      match step state with
      | Some output -> loop state (f output acc)
      | None -> acc
    in
    loop state init

  let[@inline] iter f state = fold (fun keys () -> f keys) state ()
end
