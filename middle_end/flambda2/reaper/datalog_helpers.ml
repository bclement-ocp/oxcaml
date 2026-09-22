(******************************************************************************
 *                                  OxCaml                                    *
 *       Nathanaëlle Courant, Pierre Chambart, Basile Clément, OCamlPro       *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2025 OCamlPro                                                *
 * Copyright (c) 2025 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

module Syntax = struct
  include Datalog

  (* CR-someday bclement: the datalog engine itself should provide a similar
     functionality and hide the concrete type of the tables. *)

  type (_, _) iso =
    | Bool : (bool, unit) iso
    | Column : ('t, 'k, 'v) Datalog.Column.id -> ('t, 't) iso

  let inj : type t s. (t, s) iso -> t -> s Or_null.t = function
    | Bool -> fun b -> if b then Or_null.this () else Or_null.null
    | Column head ->
      fun t -> if Column.is_empty head t then Or_null.null else Or_null.this t

  let proj : type t s. (t, s) iso -> s Or_null.t -> t = function
    | Bool -> Or_null.is_this
    | Column head -> (
      fun t -> match t with Null -> Column.empty head | This t -> t)

  type (!_, !_) rel =
    | Rel : ('s, 'k, unit) table * ('t, 's) iso -> ('t, 'k) rel

  let get_rel (Rel (table, iso)) db =
    Datalog.get_table_or_null table db |> proj iso

  let set_rel (Rel (table, iso)) value db =
    Datalog.set_table_or_null table (inj iso value) db

  let query q = q

  let ( let$ ) xs f = compile xs f

  let ( let^$ ) (ps, xs) f =
    compile_with_parameters ps xs (fun ps xs -> f (ps, xs))

  let rec flatten_hypotheses l =
    match l with
    | [] -> []
    | `And l1 :: l2 -> flatten_hypotheses l1 @ flatten_hypotheses l2
    | `Only_if (l1, x) :: l2 ->
      (x :: flatten_hypotheses l1) @ flatten_hypotheses l2
    | (#hypothesis as x) :: l -> x :: flatten_hypotheses l

  let ( ==> ) h c =
    match c with
    | #deduction as c -> where (flatten_hypotheses h) (deduce c)
    | `Only_if (l, c) -> where (l @ flatten_hypotheses h) (deduce c)

  let ( =>? ) h l = where (flatten_hypotheses h) (yield l)

  let ( !! ) = Term.constant

  let saturate_in_order = List.map (fun r -> Schedule.saturate [r])

  let ( ~~ ) = not

  (* Prevent shadowing [not] *)
  let not = Stdlib.not

  let ( % ) (type t k) (rel : (t, k) rel) (args : k Term.hlist) =
    match rel with Rel (table, _) -> atom table args

  let when1 f x = filter (fun [x] -> f x) [x]

  let unless1 f x = when1 (fun x -> not (f x)) x

  let ( let^? ) (params, existentials) f =
    let q =
      query
        (let^$ params, existentials = params, existentials in
         f (params, existentials) =>? [])
    in
    fun params db ->
      Cursor.fold_with_parameters q params db ~init:false ~f:(fun [] _ -> true)
end

module Cols = struct
  let n = Code_id_or_name.datalog_column_id

  let f = Field.datalog_column_id

  let cf = Cofield.datalog_column_id
end

open! Syntax

let bool_ name = Rel (Datalog.create_relation ~provenance:false ~name [], Bool)

let nrel (type t k) name (schema : (t, k, unit) Column.hlist) : (t, k) rel =
  match schema with
  | [] -> Misc.fatal_error "Cannot create nullary table (hint: use bool_)"
  | head :: _ ->
    Rel (Datalog.create_relation ~provenance:false ~name schema, Column head)

let rel1 name schema =
  let tbl = nrel name schema in
  fun x -> tbl % [x]

let rel2 name schema =
  let tbl = nrel name schema in
  fun x y -> tbl % [x; y]

let rel3 name schema =
  let tbl = nrel name schema in
  fun x y z -> tbl % [x; y; z]

module Fixit : sig
  type (_, _, _) stmt

  val ( let+ ) : ('a, 'b, 'c) stmt -> ('a -> 'd) -> ('d, 'b, 'c) stmt

  val ( and+ ) :
    ('a, 'b, 'b) stmt -> ('c, 'b, 'b) stmt -> ('a * 'c, 'b, 'b) stmt

  val run : ('a, 'a, 'b) stmt -> Datalog.database -> 'b

  (* Don't try to write to this one ;) *)
  val empty : ('t, 'k, unit) Datalog.Column.hlist -> ('t, 'k) rel

  (* Or to this one! *)
  val false_ : (bool, nil) rel

  val param :
    string ->
    ('a, 'b, unit) Datalog.Column.hlist ->
    (('a, 'b) rel -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, 'a -> 'd) stmt

  val paramc :
    string ->
    ('a, 'b, unit) Datalog.Column.hlist ->
    ('e -> 'a) ->
    (('a, 'b) rel -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, 'e -> 'd) stmt

  val paramb :
    string ->
    ((bool, Syntax.nil) rel -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, bool -> 'd) stmt

  val param1s :
    string ->
    ('a, 'b, unit) Datalog.Column.id ->
    (('a, 'b -> nil) rel -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, 'b -> 'd) stmt

  val param0 :
    ('a -> 'b) ->
    (('b, 'c, 'c) stmt -> ('d, 'e, 'f) stmt) ->
    ('d, 'e, 'a -> 'f) stmt

  val local0 :
    ('a, 'b, unit) Datalog.Column.hlist ->
    ('a, 'c, 'c) stmt ->
    (('a, 'b) rel -> ('d, 'c, 'c) stmt) ->
    ('d, 'c, 'c) stmt

  module Table : sig
    type (_, _) hlist =
      | [] : (Datalog.nil, Datalog.nil) hlist
      | ( :: ) :
          ('t, 'k) rel * ('ts, 'xs) hlist
          -> ('t -> 'ts, ('t, 'k) rel -> 'xs) hlist
  end

  val return : ('a, 'b) rel -> ('a, 'c, 'c) stmt

  val fix :
    ('a, 'b) Table.hlist ->
    (('a, 'b) Table.hlist -> Datalog.rule list) ->
    (('a, 'b) Table.hlist -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, 'd) stmt

  val seq :
    ('a, 'b) Table.hlist ->
    (('a, 'b) Table.hlist -> Datalog.rule list) ->
    (('a, 'b) Table.hlist -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, 'd) stmt

  val fix1 :
    ('t, 'k) rel ->
    (('t, 'k) rel -> Datalog.rule list) ->
    (('t, 'k) rel -> ('x, 'y, 'd) stmt) ->
    ('x, 'y, 'd) stmt

  val fix' :
    ('a, 'b) Table.hlist ->
    (('a, 'b) Table.hlist -> Datalog.rule list) ->
    ('a Datalog.Constant.hlist, 'c, 'c) stmt

  val seq' :
    ('a, 'b) Table.hlist ->
    (('a, 'b) Table.hlist -> Datalog.rule list) ->
    ('a Datalog.Constant.hlist, 'c, 'c) stmt

  val fix1' :
    ('t, 'k) rel -> (('t, 'k) rel -> Datalog.rule list) -> ('t, 'c, 'c) stmt

  val ( let@ ) : ('a -> 'b) -> 'a -> 'b
end = struct
  let empty columns = nrel "empty" columns

  let false_ = bool_ "false"

  let local name (Rel (table, iso)) =
    Rel (Datalog.create_relation ~name (Datalog.columns table), iso)

  module Table = struct
    type (_, _) hlist =
      | [] : (Datalog.nil, Datalog.nil) hlist
      | ( :: ) :
          ('t, 'k) rel * ('ts, 'xs) hlist
          -> ('t -> 'ts, ('t, 'k) rel -> 'xs) hlist

    let rec locals : type a b. (a, b) hlist -> (a, b) hlist = function
      | [] -> []
      | table :: tables -> local "fix" table :: locals tables

    let rec copy : type a b.
        (a, b) hlist -> (a, b) hlist -> Datalog.database -> Datalog.database =
     fun from_tables to_tables db ->
      match from_tables, to_tables with
      | [], [] -> db
      | from_table :: from_tables, to_table :: to_tables ->
        let db = set_rel to_table (get_rel from_table db) db in
        copy from_tables to_tables db

    let rec get : type a b.
        (a, b) hlist -> Datalog.database -> a Datalog.Constant.hlist =
     fun tables db ->
      match tables with
      | [] -> []
      | table :: tables -> get_rel table db :: get tables db
  end

  (* In [('s, 'r, 'f) stmt] the type variables have the following meaning:

     - ['s] is the value associated with the statement (i.e. the value that can
     be inspected using [let+]).

     - ['r] is the global return type of the program this statement is a part
     of. For instance, in [s = let+ x = s1 and+ y = s2 in (x, y)], all of [s1],
     [s2] and [s] have the same value of ['r = 'x * 'y], but have different
     values for ['s] (['x], ['y] and ['x * 'y] respectively).

     - ['f] is the global parametric type of the program this istatement is a
     part of. It is a n-ary function type ultimately returning values of type
     ['r], but with the parameters introduced by the [param*] family of
     functions. *)
  type (_, _, _) stmt =
    | Return : ('t, 'k) rel -> ('t, 'c, 'c) stmt
    | Value : 'a option ref -> ('a, 'c, 'c) stmt
    | Run : Datalog.Schedule.t -> (unit, 'c, 'c) stmt
    | Seq : (unit, 'c, 'c) stmt * ('a, 'b, 'c) stmt -> ('a, 'b, 'c) stmt
    | Call : ('b, 'c, 'a -> 'c) stmt * ('a, 'c, 'c) stmt -> ('b, 'c, 'c) stmt
    | Map :
        ('a, 'c, 'j) stmt * (Datalog.database -> 'a -> 'b)
        -> ('b, 'c, 'j) stmt
    | Inspect :
        ('a, 'c, 'j) stmt * (Datalog.database -> 'a -> unit)
        -> ('a, 'c, 'j) stmt
    | Conj : ('a, 'c, 'c) stmt * ('b, 'c, 'c) stmt -> ('a * 'b, 'c, 'c) stmt
    | Now :
        ('a, 'b, 'j) stmt * (Datalog.database -> Datalog.database)
        -> ('a, 'b, 'j) stmt
    | Input :
        ('x, 'y, 'j) stmt * (Datalog.database -> 'a -> Datalog.database)
        -> ('x, 'y, 'a -> 'j) stmt

  let rec run : type d f e.
      (d, f, e) stmt -> (Datalog.database -> d -> f) -> Datalog.database -> e =
   fun stmt k db ->
    match stmt with
    | Return table -> k db (get_rel table db)
    | Value v -> k db (Option.get !v)
    | Call (stmt_f, stmt_arg) ->
      run stmt_arg (fun db arg -> run stmt_f k db arg) db
    | Run schedule -> k (Datalog.Schedule.run schedule db) ()
    | Seq (stmt1, stmt2) -> run stmt1 (fun db () -> run stmt2 k db) db
    | Map (stmt, later) -> run stmt (fun db value -> k db (later db value)) db
    | Inspect (stmt, f) ->
      run stmt
        (fun db value ->
          f db value;
          k db value)
        db
    | Conj (stmt1, stmt2) ->
      run stmt1
        (fun db value1 -> run stmt2 (fun db value2 -> k db (value1, value2)) db)
        db
    | Now (stmt, f) -> run stmt k (f db)
    | Input (stmt, set_input) ->
      fun arg ->
        let db = set_input db arg in
        run stmt k db

  let run stmt db = run stmt (fun _ out -> out) db

  let return table = Return table

  let ( let+ ) stmt f = Map (stmt, fun _ value -> f value)

  let ( and+ ) stmt1 stmt2 = Conj (stmt1, stmt2)

  let param0 g f =
    let cell = ref None in
    Inspect
      ( Input
          ( f (Value cell),
            fun db x ->
              cell := Some (g x);
              db ),
        fun _db _value -> cell := None )

  let param name columns f =
    let table = nrel name columns in
    Input (f table, fun db x -> set_rel table x db)

  let paramc name columns g f =
    let table = nrel name columns in
    Input (f table, fun db x -> set_rel table (g x) db)

  let paramb name f =
    let table = bool_ name in
    Input (f table, fun db b -> set_rel table b db)

  let param1s name column f =
    paramc name [column] (fun key -> Column.singleton column key ()) f

  let local0 columns body f =
    let table = nrel "local" columns in
    Call (Input (f table, fun db x -> set_rel table x db), body)

  let fix x f g =
    let y = Table.locals x in
    let schedule = Datalog.Schedule.saturate (f y) in
    let body = g y in
    Now (Seq (Run schedule, body), fun db -> Table.copy x y db)

  let seq x f g =
    let y = Table.locals x in
    let rules = f y in
    let body = g y in
    let go =
      List.fold_right
        (fun r acc -> Seq (Run (Datalog.Schedule.saturate [r]), acc))
        rules body
    in
    Now (go, fun db -> Table.copy x y db)

  let fix1 x f g =
    let y = local "fix" x in
    let schedule = Datalog.Schedule.saturate (f y) in
    let body = g y in
    Now (Seq (Run schedule, body), fun db -> set_rel y (get_rel x db) db)

  let fix' x f =
    let y = Table.locals x in
    let schedule = Datalog.Schedule.saturate (f y) in
    Now
      ( Map (Run schedule, fun db () -> Table.get y db),
        fun db -> Table.copy x y db )

  let seq' x f =
    let y = Table.locals x in
    let rules = f y in
    let go =
      Option.get
        (List.fold_right
           (fun r acc ->
             let r = Run (Datalog.Schedule.saturate [r]) in
             match acc with None -> Some r | Some acc -> Some (Seq (r, acc)))
           rules None)
    in
    Now (Map (go, fun db () -> Table.get y db), fun db -> Table.copy x y db)

  let fix1' x f =
    let y = local "fix" x in
    let schedule = Datalog.Schedule.saturate (f y) in
    Now
      ( Map (Run schedule, fun db () -> get_rel y db),
        fun db -> set_rel y (get_rel x db) db )

  let ( let@ ) f x = f x
end
