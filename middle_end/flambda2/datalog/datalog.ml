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

module String = struct
  include String

  include Heterogenous_list.Make (struct
    type 'a t = string
  end)
end

module Variable = struct
  include Lang.Variable

  let rec list : type a. a String.hlist -> a hlist = function
    | [] -> []
    | name :: names -> create name :: list names
end

module Parameter = Variable

module Term = struct
  include Lang.Term

  let parameter = Lang.var

  let rec parameters : type a. a Parameter.hlist -> a hlist = function
    | [] -> []
    | param :: params -> parameter param :: parameters params

  let variables = parameters

  let constant = Lang.lit
end

type (_, _) head =
  | Yield : 'v Term.hlist -> ('p, ('p, 'v) Cursor.With_parameters.t) head
  | Deduce : Lang.atom list -> (Heterogenous_list.nil, Schedule.rule) head

type levels = Levels : 'a Variable.hlist -> levels

let rec prepend_vars : type a. a Variable.hlist -> levels -> levels =
 fun vars levels ->
  match vars with
  | [] -> levels
  | var :: vars ->
    let (Levels vars') = prepend_vars vars levels in
    Levels (var :: vars')

type ('p, 'a) program =
  { body : Lang.atom list;
    head : ('p, 'a) head;
    levels : levels
  }

let where_atom atom program = { program with body = atom :: program.body }

let yield args = { body = []; head = Yield args; levels = Levels [] }

let deduce head = { body = []; head = Deduce head; levels = Levels [] }

let foreach : type a p b.
    a String.hlist -> (a Term.hlist -> (p, b) program) -> (p, b) program =
 fun names f ->
  let vars = Variable.list names in
  let prog = f (Term.variables vars) in
  { prog with levels = prepend_vars vars prog.levels }

let compile_rule : type p a.
    parameters:p Lang.Variable.hlist ->
    variables:_ ->
    body:_ ->
    (p, a) head ->
    a =
 fun ~parameters ~variables ~body -> function
  | Yield args ->
    let callback = ref ignore in
    let yield =
      Lang.callback_with_bindings ~name:"yield"
        (fun _ args -> !callback args)
        args
    in
    let variables = Lang.Variable.hlist_to_list variables in
    Cursor.With_parameters.create_from_rule ~callback parameters variables
      (Lang.rule ~head:[yield] ~body)
  | Deduce head ->
    let [] = parameters in
    Schedule.create_rule
      (Lang.Variable.hlist_to_list variables)
      (Lang.rule ~head ~body)

let compile_program parameters { body; head; levels } =
  let (Levels variables) = levels in
  compile_rule ~parameters ~variables ~body head

let compile_with_parameters0 ps f =
  let ps = Parameter.list ps in
  let prog = f (Term.parameters ps) in
  compile_program ps prog

let compile_with_parameters ps xs f =
  compile_with_parameters0 ps (fun ps -> foreach xs (fun xs -> f ps xs))

let compile xs f = compile_with_parameters [] xs (fun [] xs -> f xs)
