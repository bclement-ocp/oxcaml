# Encyclopædia of Optimizations

This page is a reference of the optimizations and transformations performed by
the flambda2 middle-end. **It does not cover classic mode (`-Oclassic`)**.

Note that, while we intentionally try to describe the optimizations performed
by flambda2 as more-or-less atomic transformations on OCaml source code
(because we believe that is the form in which they are the most useful to OCaml
programmers), they in practice happen all at the same time in a lower-level
intermediate representation. This can sometime (hopefully rarely!) cause
discrepancies between what would be expected based on this document and what
actually happens when running the compiler -- if you notice such discrepancies,
this is still a bug (either of the code or the documentation); please report
them.

Most of the following optimizations are enabled by default in `-O2` mode; some
require `-O3` or specific flags which are documented below.

**Note:** This is currently a work-in-progress; not all optimizations are
covered yet.

## Canonicalization

Canonicalization is a pervasive optimization that identifies all the names of a
given expression, and replaces all their usages with the first such name that
was defined (or a constant, if applicable).

This is the most basic of the optimizations performed by flambda2, and is
generally critical to cleaning up the code after other optimizations.

```ocaml
(* Before Canonicalization *)
let f x =
  let y = x in
  let z = (y, y) in
  let w, _ = z in
  Some w

(* After Canonicalization *)
let f x =
  let y = x in
  let z = (x, x) in
  let w = x in
  Some x
```

Canonicalization also takes into account equalities with constants learned in a
specific branch of a `match`.

```ocaml
(* Before Canonicalization *)
let f x =
  match x with
  | 0 -> x + 1
  | _ -> x

(* After Canonicalization *)
let f x =
  match x with
  | 0 ->
    (* x = 0 is known *)
    1
  | _ -> x
```

## Match optimizations

The following optimizations are applied to `match` and `match`-like constructs.
The examples below are always given using `match`, but also apply to `if`.

### Match Elimination

Match Elimination is an optimization that triggers when the scrutinee of a
match is a constructor (or literal), and replaces the entire match with the
corresponding branch.

Match Elimination is a *standard* optimisation, it is always enabled.

When Match Elimination happens on a constructor with arguments, Canonicalization
simplifications allow to eliminate the allocation.

```ocaml
(* Before Match Elimination *)
let main ~is_none ~is_some a =
  let some_a = Some a in
  match some_a with
  | None -> is_none ()
  | Some x -> is_some x

(* After Match Elimination *)
let main ~is_none ~is_some a =
  let some_a = Some a in
  let Some x = some_a in (* irrefutable *)
  is_some x

(* After Match Elimination and Canonicalization *)
let main ~is_none ~is_some a =
  let some_a = Some a in
  is_some a
```

```ocaml
(* Before Match Elimination *)
let return x = Some x

let bind f x =
  match x with
  | None -> None
  | Some y -> f y

let main f v =
  bind f (return v)

(* After inlining, Match Elimination, and Canonicalization *)
let main f v =
  f v
```

In the following situation, Match Elimination does **not** trigger: the
scrutinee of the `match` is the result of an `if` statement, not a constructor.
To optimize this code, more powerful optimisations (Match Simplification or
Match Forwarding) are necessary.

```ocaml
(* No Match Elimination: always_some is not a constructor *)
let main ~is_none ~is_some b x y =
  let always_some = if b then Some x else Some y in
  match always_some with
  | None -> is_none ()
  | Some z -> is_some z
```

### Match Simplification

Match Simplification is an optimization that triggers when some branches of a
match are unreachable, and removes the unreachable branches. If there is only
one branch remaining, the entire match is removed and replaced with that branch.

Match Simplification provides fairly small runtime benefits compared to Match
Elimination, as the more complex control flow involved typically prevents
additional simplifications from being performed. Its primary use is for dead
code elimination.

```ocaml
(* Before Match Simplification *)
let main b =
  let c = if b then 0 else 1 in
  match c with
  | 0 -> "zero"
  | 1 -> "one"
  | 2 -> "two"
  | 3 -> "three"
  | _ -> failwith "does not fit on four bits"

(* After Match Simplification *)
let main b =
  let c = if b then 0 else 1 in
  match c with
  | 0 -> "zero"
  | 1 -> "one"
```

### Match Forwarding (match-in-match)

**This optimization is currently experimental, and requires the
`--match-in-match` flag.**

Match Forwarding (colloquially known as ``match-in-match'') is an optimization
where a `match` following a control flow construct is duplicated inside of that
control flow construct. This optimization only triggers if Match Elimination is
able to simplify the duplicated `match`, effectively eliminating the `match`.

**Note:** Unlike other match optimizations described in this document, Match
Forwarding is a *control flow* optimization. It only triggers if the two
control flow constructs directly follow each other; the presence of any
non-trivial code in between will prevent the optimization here. This is
indicated in the examples by a comment marker.

In its simplest incarnation, the scrutinee itself is the result of the previous
control flow construct.

```ocaml
(* Before Match Forwarding *)
let main ~is_none ~is_some b x =
  let y = if b then None else Some x in
  (* any code here prevents optimization *)
  match y with
  | None -> is_none ()
  | Some z -> is_some z

(* After Match Forwarding *)
let main ~is_none ~is_some b x =
  (* NB: branches are extracted to continuations and shared between the
     duplicate copies, limiting code duplication. *)
  let branch_none () = is_none () in
  let branch_some z () = is_some z () in
  if b then
    match None with
    | None -> branch_none ()
    | Some z -> branch_some z ()
  else
    match Some x with
    | None -> branch_none ()
    | Some z -> branch_some z ()

(* After Match Forwarding and Match Elimination *)
let main ~is_none ~is_some b x =
  (* [branch_none] and [branch_some] are inlined again here *)
  if b then is_none () else is_some x
```

Match Forwarding also triggers on consecutive matches on the same variable. In
this case, Canonicalization is used to learn the value of `b` in each branch,
allowing Match Elimination to trigger.

```ocaml
(* Before Match Forwarding *)
let main b x y =
  let z = if b then None else Some x in
  (* any code here prevents optimization *)
  if b then (Some y, z) else (z, Some y)

(* After Match Forwarding *)
let main b x y =
  let branch_true z () = (Some y, z) in
  let branch_false z () = (z, Some y) in
  if b then
    (* b = true is known *)
    let z = None in
    if b then branch_true z ()
    else branch_false z ()
  else
    (* b = false is known *)
    let z = Some x in
    if b then branch_true z ()
    else branch_false z ()

(* After Match Forwarding, Canonicalization, and Match Elimination *)
let main b x y =
  if b then
    (Some y, None)
  else
    (Some x, Some y)
```
