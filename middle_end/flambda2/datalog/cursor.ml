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

open Heterogenous_list

type action =
  | Bind_iterator : 'a option ref * 'a Trie.Iterator.t -> action
  | Unless : ('t, 'k, 'v) Table.Id.t * 'k Option_ref.hlist -> action

let bind_iterator var iterator = Bind_iterator (var, iterator)

let unless id args = Unless (id, args)

type binder = Bind_table : ('t, 'k, 'v) Table.Id.t * 't ref -> binder

type actions = { mutable rev_actions : action list }

let create_actions () = { rev_actions = [] }

let add_action actions action =
  actions.rev_actions <- action :: actions.rev_actions

module Order : sig
  type t

  val print : Format.formatter -> t -> unit

  val compare : t -> t -> int

  val parameters : t

  val succ : t -> t
end = struct
  type t = int

  let print = Format.pp_print_int

  let compare = Int.compare

  let parameters = -1

  let succ o = o + 1
end

module Level = struct
  type 'a t =
    { name : string;
      order : Order.t;
      actions : actions;
      mutable iterators : 'a Trie.Iterator.t list;
      mutable output : 'a option ref option
    }

  let print ppf { name; order; _ } =
    Format.fprintf ppf "%s (with order %a)" name Order.print order

  let create ~order name =
    { name; order; output = None; iterators = []; actions = create_actions () }

  let use_output level =
    match level.output with
    | None ->
      let output = ref None in
      level.output <- Some output;
      output
    | Some output -> output

  let actions { actions; _ } = actions

  let add_iterator level iterator =
    level.iterators <- iterator :: level.iterators

  let order { order; _ } = order

  include Heterogenous_list.Make (struct
    type nonrec 'a t = 'a t
  end)
end

type level_list = Level_list : 'a Level.hlist -> level_list [@@unboxed]

type levels =
  { mutable rev_levels : level_list;
    mutable last_order : Order.t
  }

let create_levels () =
  { rev_levels = Level_list []; last_order = Order.parameters }

let add_new_level levels name =
  let order = Order.succ levels.last_order in
  let level = Level.create ~order name in
  let (Level_list rev_levels) = levels.rev_levels in
  levels.rev_levels <- Level_list (level :: rev_levels);
  levels.last_order <- order;
  level

module Join_iterator = Leapfrog.Join (Trie.Iterator)
module Cursor = Virtual_machine.Make (Join_iterator)

type binders = { mutable rev_binders : binder list }

let create_binders () = { rev_binders = [] }

let add_binder binders binder =
  binders.rev_binders <- binder :: binders.rev_binders

type context =
  { levels : levels;
    actions : actions;
    binders : binders
  }

let create_context () =
  { levels = create_levels ();
    actions = create_actions ();
    binders = create_binders ()
  }

let add_new_level context name = add_new_level context.levels name

let add_iterator context id =
  let handler, iterators, _ = Table.Id.create_iterator id in
  add_binder context.binders (Bind_table (id, handler));
  iterators

let initial_actions { actions; _ } = actions

type 'v t =
  { cursor_binders : binder list;
    instruction : (action, 'v Constant.hlist, nil) Cursor.instruction
  }

type 'a cursor = 'a t

let print ppf { cursor_binders; _ } =
  Format.fprintf ppf "@[<hov 1>(%a)@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space
       (fun ppf (Bind_table (table_id, _)) -> Table.Id.print ppf table_id))
    cursor_binders

let apply_actions actions instruction =
  (* Note: we must preserve the order of [Bind_iterator] actions in order to
     initialize iterators in the correct order. Otherwise, we would miscompile
     [P (x, x, x)] (we would initialize the 3rd argument before the 2nd). *)
  List.fold_left
    (fun instruction action -> Cursor.action action instruction)
    instruction actions.rev_actions

(* NB: the variables must be passed in reverse order, i.e. deepest variable
   first. *)
let rec open_rev_vars :
    type s y.
    s Level.hlist ->
    (action, y, s) Cursor.instruction ->
    (action, y, nil) Cursor.instruction =
 fun vars instruction ->
  match vars with
  | [] -> instruction
  | var :: vars -> (
    match var.iterators with
    | [] ->
      if true
      then assert false
      else
        Misc.fatal_errorf
          "@[<v>@[Variable '%a' is never used in a binding position.@]@ \
           @[Hint: A position is binding if it respects the provided variable \
           ordering.@]@]"
          Level.print var
    | _ ->
      let instruction = apply_actions var.actions instruction in
      let instruction =
        match var.output with
        | Some output -> Cursor.set_output output instruction
        | None -> instruction
      in
      open_rev_vars vars
        (Cursor.open_ (Join_iterator.create var.iterators) instruction))

(* Optimisation: if we do not use the output from the last variable, we only
   need the first matching value of that variable.

   NB: the variables must be passed in reverse order, i.e. deepest variable
   first. *)
let rec pop_rev_vars :
    type s. s Level.hlist -> (action, 'y, s) Cursor.instruction = function
  | [] -> Cursor.advance
  | var :: vars -> (
    match var.output with
    | None -> Cursor.pop (pop_rev_vars vars)
    | _ -> Cursor.advance)

let create context output =
  let { levels; actions; binders } = context in
  let (Level_list rev_levels) = levels.rev_levels in
  let instruction =
    open_rev_vars rev_levels @@ Cursor.yield output @@ pop_rev_vars rev_levels
  in
  let instruction = apply_actions actions instruction in
  { cursor_binders = binders.rev_binders; instruction }

let bind_table (Bind_table (id, handler)) database =
  let table = Table.Map.get id database in
  if Trie.is_empty (Table.Id.is_trie id) table
  then false
  else (
    handler := Table.Map.get id database;
    true)

let bind_table_list binders database =
  List.iter (fun binder -> ignore @@ bind_table binder database) binders

let evaluate op input =
  match op with
  | Bind_iterator (value, it) -> (
    let value = Option.get !value in
    Trie.Iterator.init it;
    Trie.Iterator.seek it value;
    match Trie.Iterator.current it with
    | Some found when Trie.Iterator.equal_key it found value ->
      Trie.Iterator.accept it;
      Virtual_machine.Accept
    | None | Some _ -> Virtual_machine.Skip)
  | Unless (id, args) ->
    if Option.is_some
         (Trie.find_opt (Table.Id.is_trie id) (Option_ref.get args)
            (Table.Map.get id input))
    then Virtual_machine.Skip
    else Virtual_machine.Accept

let naive_fold cursor db f acc =
  bind_table_list cursor.cursor_binders db;
  Cursor.fold f
    (Cursor.create db (Cursor.compile ~evaluate cursor.instruction))
    acc

let naive_iter cursor db f =
  bind_table_list cursor.cursor_binders db;
  Cursor.iter f (Cursor.create db (Cursor.compile ~evaluate cursor.instruction))

(* Seminaive evaluation iterates over all the {b new} tuples in the [diff]
   database that are not in the [previous] database.

   [current] must be equal to [concat ~earlier:previous ~later:diff]. *)
let[@inline] seminaive_fold cursor ~previous ~diff ~current f acc =
  let compiled = Cursor.compile ~evaluate cursor.instruction in
  bind_table_list cursor.cursor_binders current;
  let rec loop binders acc =
    match binders with
    | [] -> acc
    | binder :: binders ->
      let acc =
        if bind_table binder diff
        then Cursor.fold f (Cursor.create current compiled) acc
        else acc
      in
      if bind_table binder previous then loop binders acc else acc
  in
  loop cursor.cursor_binders acc

module With_parameters = struct
  type nonrec ('p, 'v) t =
    { parameters : 'p Option_ref.hlist;
      cursor : 'v t
    }

  let without_parameters { parameters = []; cursor } = cursor

  let create ~parameters context output =
    { cursor = create context output; parameters }

  let naive_fold { parameters; cursor } ps db f acc =
    Option_ref.set parameters ps;
    naive_fold cursor db f acc

  let naive_iter { parameters; cursor } ps db f =
    Option_ref.set parameters ps;
    naive_iter cursor db f

  let seminaive_fold { parameters; cursor } ps ~previous ~diff ~current f acc =
    Option_ref.set parameters ps;
    seminaive_fold ~previous ~diff ~current cursor f acc
end
