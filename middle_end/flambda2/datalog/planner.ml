(******************************************************************************
 *                                  OxCaml                                    *
 *                        Basile Clément, OCamlPro                            *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2024 Jane Street Group LLC                                   *
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

open Datalog_imports
open Lang

type 'k column_iterator =
  | Column_iterator :
      ('t, 'k, 'v) Column.id * 't variable * 'v variable
      -> 'k column_iterator

type stage =
  | Join_stage : 'k variable * 'k column_iterator list -> stage
  | Seek_stage : 'k term * 'k column_iterator list -> stage
  | Check_stage : atom -> stage

type bound_table =
  | Bound_table : ('t, 'k, 'v) Table.Id.t * 't variable -> bound_table

type head_atom =
  | Union :
      ('t, _, _) Table.Id.t
      * ('t, 'k, 's) Column.hlist
      * 'k Term.hlist
      * 's term
      * ('s, _, 'v) Column.hlist
      * 'v Table.result_repr
      -> head_atom
  | Callback_with_bindings :
      (Bytecode.bindings_ref -> 'k Constant.hlist -> unit) with_name
      * 'k Term.hlist
      -> head_atom

type plan =
  { tables : bound_table iarray;
    input_stages : stage iarray;
    num_existentials : int;
    output_atoms : head_atom iarray
  }

let print_head_atom ppf head_atom =
  match head_atom with
  | Union (tid, columns, args, value, _, _) ->
    Format.fprintf ppf "@[<1>@[%a@](@,@[%a@]) += %a@]" Table.Id.print tid
      (Term.print_columns
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
         columns)
      args
      (fun ppf value ->
        match value with
        | Literal _ -> Format.fprintf ppf "()"
        | Variable var -> Format.fprintf ppf "%a" Variable.print var)
      value
  | Callback_with_bindings (fn, args) ->
    Format.fprintf ppf "%s@[<1>(%a)@]" fn.name
      (Term.print_hlist ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ "))
      args

let print_stage ppf stage =
  match stage with
  | Join_stage (var, join_columns) ->
    Format.fprintf ppf "for %a in @[%a@]:" Variable.print var
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ⨝@ ")
         (fun ppf (Column_iterator (_, tbl, _)) -> Variable.print ppf tbl))
      join_columns
  | Seek_stage (term, join_columns) ->
    let print_lit =
      match join_columns with
      | [] -> fun ppf _ -> Format.fprintf ppf "<cst>"
      | Column_iterator (col, _, _) :: _ -> Column.print_key col
    in
    Format.fprintf ppf "@[<2>@[if %a not in %a:@]@ continue@]"
      (print_term print_lit) term
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ⨝@ ")
         (fun ppf (Column_iterator (_, tbl, _)) -> Variable.print ppf tbl))
      join_columns
  | Check_stage atom ->
    Format.fprintf ppf "@[<2>@[if %a:@]@ continue@]" print_neg_atom atom

let print_stages print ppf stages =
  let depth = ref 0 in
  for i = 0 to Iarray.length stages - 1 do
    let stage = Iarray.get stages i in
    let extra_indent =
      match stage with Join_stage _ -> 2 | Seek_stage _ | Check_stage _ -> 0
    in
    if extra_indent > 0
    then (
      Format.fprintf ppf "@[<v %d>" extra_indent;
      incr depth);
    print_stage ppf stage;
    Format.fprintf ppf "@ "
  done;
  print ppf ();
  while !depth > 0 do
    Format.fprintf ppf "@]";
    decr depth
  done

let print_plan ppf { input_stages; output_atoms; num_existentials; _ } =
  let print_output ppf () =
    (* Note: we need to eta-expand `Iarray.iter` because of `local` mode
       restrictions. *)
    Format.pp_print_iter ~pp_sep:Format.pp_print_space
      (fun f arr -> Iarray.iter f arr)
      print_head_atom ppf output_atoms;
    if num_existentials > 0
    then Format.fprintf ppf "@ break %d" num_existentials
  in
  print_stages print_output ppf input_stages

(* Represent occurrences of variables in table atoms.

   An occurrence in a body atom is binding and will participate in the join
   defining the variable if:

   - It is the first (outermost) occurrence of the variable in the atom, and

   - There is no previous (outer) occurrences of a variable that must be bound
   earlier according to the global variable ordering.

   For instance, the first occurrence of [X] in [P(X, Y, X)] is always binding,
   but the occurrence of [Y] is only binding if [Y] is after [X] in the global
   variable ordering.

   An occurrence in a head atom is binding iff it is the first outermost
   occurrence of the variable in the atom (the global variable ordering is
   ignored, because it is not used for the output). *)
type 'a arg =
  | Bind of 'a variable
  | Check of 'a term

let arg_to_term = function Bind var -> Variable var | Check term -> term

type index_layer =
  | Index_layer :
      ('t, 'k, 'v) Column.id * 't variable * 'k arg * 'v variable
      -> index_layer

type table_layers =
  | Table_layers :
      { table : 't variable;
        columns : index_layer iarray;
        result : 'v variable;
        (* Updated during planning. *)
        mutable bound_prefix : int
      }
      -> table_layers

type atom_layout =
  { table_layers : table_layers option;
    atom : atom
  }

(* Lays out a table atom as a trie of nested tables, represented by an
   [index_layer] array.

   If [binding_times] are provided, the binding occurrences are restricted to be
   compatible with the provided global order (see documentation of the [arg]
   types). *)
let layout_body_table : type t k v.
    binding_times:_ ->
    (t, k, v) Column.hlist ->
    t variable ->
    k Term.hlist ->
    index_layer iarray * v variable =
 fun ~binding_times columns table args ->
  let rec loop : type t k.
      min_binding_time:_ ->
      _ ->
      (t, k, v) Column.hlist ->
      t variable ->
      k Term.hlist ->
      _ * v variable =
   fun ~min_binding_time rev_plan columns outer_var args ->
    match columns, args with
    | [], [] -> Iarray.of_list (List.rev rev_plan), outer_var
    | column :: columns, arg :: args ->
      let inner_var =
        Variable.create
          (Format.asprintf "%a[%a]" Variable.print outer_var
             (print_term (Column.print_key column))
             arg)
      in
      let arg, min_binding_time =
        match arg with
        | Variable var -> (
          match Variable.Id.Map.find (Variable.uid var) binding_times with
          | var_binding_time when var_binding_time >= min_binding_time ->
            Bind var, var_binding_time + 1
          | _ | (exception Not_found) -> Check (Variable var), min_binding_time)
        | Literal _ -> Check arg, min_binding_time
      in
      loop ~min_binding_time
        (Index_layer (column, outer_var, arg, inner_var) :: rev_plan)
        columns inner_var args
  in
  loop ~min_binding_time:0 [] columns table args

let layout_head_table : type t k v.
    binding_times:_ ->
    (t, k, v) Column.hlist ->
    t variable ->
    k Term.hlist ->
    index_layer iarray * v variable =
 fun ~binding_times columns table args ->
  let rec loop : type t k.
      binding_times:_ ->
      _ ->
      (t, k, v) Column.hlist ->
      t variable ->
      k Term.hlist ->
      _ * v variable =
   fun ~binding_times rev_plan columns outer_var args ->
    match columns, args with
    | [], [] -> Iarray.of_list (List.rev rev_plan), outer_var
    | column :: columns, arg :: args ->
      let inner_var =
        Variable.create
          (Format.asprintf "%a[%a]" Variable.print outer_var
             (print_term (Column.print_key column))
             arg)
      in
      let arg, binding_times =
        match arg with
        | Variable var when Variable.Id.Map.mem (Variable.uid var) binding_times
          ->
          Bind var, Variable.Id.Map.remove (Variable.uid var) binding_times
        | Variable _ | Literal _ -> Check arg, binding_times
      in
      loop ~binding_times
        (Index_layer (column, outer_var, arg, inner_var) :: rev_plan)
        columns inner_var args
  in
  loop ~binding_times [] columns table args

let rec free_vars_term_hlist : type a. a Term.hlist -> Variable.Id.Set.t =
 fun terms ->
  match terms with
  | [] -> Variable.Id.Set.empty
  | Literal _ :: terms -> free_vars_term_hlist terms
  | Variable v :: terms ->
    Variable.Id.Set.add (Variable.uid v) (free_vars_term_hlist terms)

let rec table_head_atom : type k t s v.
    bound_table ->
    len:int ->
    index_layer iarray ->
    t variable ->
    (t, k, s) Column.hlist ->
    k Term.hlist ->
    s term ->
    (s, _, v) Column.hlist ->
    v Table.result_repr ->
    head_atom =
 fun (Bound_table (tid, table)) ~len head_columns current columns args value
     inner_cols repr ->
  if len = 0
  then
    let Equal = Variable.must_be_equal table current in
    Union (tid, columns, args, value, inner_cols, repr)
  else
    let (Index_layer (column, outer_var, arg, inner_var)) =
      Iarray.get head_columns (len - 1)
    in
    let Equal = Variable.must_be_equal inner_var current in
    table_head_atom
      (Bound_table (tid, table))
      ~len:(len - 1) head_columns outer_var (column :: columns)
      (arg_to_term arg :: args) value inner_cols repr

let add_join_stage stages var columns =
  Dynarray.add_last stages (Join_stage (var, columns))

let add_seek_stage stages term columns =
  Dynarray.add_last stages (Seek_stage (term, columns))

let add_check_stage stages atom = Dynarray.add_last stages (Check_stage atom)

let add_stages_involving_no_free_vars ~free_vars stages atom_decomposition =
  match atom_decomposition.table_layers with
  | Some (Table_layers ({ columns; bound_prefix; _ } as plan_table)) ->
    let rec loop bound_prefix =
      let[@local] stop_iteration () = plan_table.bound_prefix <- bound_prefix in
      if bound_prefix = Iarray.length columns
      then stop_iteration ()
      else
        let index_layer = Iarray.get columns bound_prefix in
        let (Index_layer (col, outer, arg, inner)) = index_layer in
        match arg with
        | Bind var ->
          if not (Variable.Id.Set.mem (Variable.uid var) free_vars)
          then
            Misc.fatal_errorf
              "*BUG*: Planner found binding position for variable %a, but it \
               was already bound."
              Variable.print var;
          stop_iteration ()
        | Check ((Variable _ | Literal _) as arg) ->
          add_seek_stage stages arg [Column_iterator (col, outer, inner)];
          loop (bound_prefix + 1)
    in
    loop bound_prefix
  | None ->
    if Variable.Id.Set.is_empty free_vars
    then add_check_stage stages atom_decomposition.atom

let advance_prefix_and_extract_iterator_on_variable (type a) table_layers
    (var : a variable) (iterators : a column_iterator list) :
    a column_iterator list =
  match table_layers with
  | Table_layers ({ columns; bound_prefix; _ } as layers) -> (
    let (Index_layer (column, outer_var, arg, inner_var)) =
      Iarray.get columns bound_prefix
    in
    match arg with
    | Check _ -> iterators
    | Bind arg_var -> (
      match Variable.provably_equal var arg_var with
      | None -> iterators
      | Some Equal ->
        layers.bound_prefix <- bound_prefix + 1;
        Column_iterator (column, outer_var, inner_var) :: iterators))

let free_vars_atoms ~binding_times atoms =
  let var_to_atoms = Variable.Id.Tbl.create 0 in
  let free_vars_of_atoms =
    Array.make (Iarray.length atoms) Variable.Id.Set.empty
  in
  Iarray.iteri
    (fun aid (Atom (_, args)) ->
      let free_vars_of_atom = free_vars_term_hlist args in
      let free_vars_of_atom =
        Variable.Id.Set.filter
          (fun var -> Variable.Id.Map.mem var binding_times)
          free_vars_of_atom
      in
      free_vars_of_atoms.(aid) <- free_vars_of_atom;
      Variable.Id.Set.iter
        (fun vid ->
          match Variable.Id.Tbl.find_opt var_to_atoms vid with
          | None -> Variable.Id.Tbl.replace var_to_atoms vid [aid]
          | Some atoms -> Variable.Id.Tbl.replace var_to_atoms vid (aid :: atoms))
        free_vars_of_atom)
    atoms;
  free_vars_of_atoms, var_to_atoms

(* Record dependencies introduced by column bindings.

   A dependency from variable [x] to variable [y] means that [y] must be bound
   strictly before [x].

   When decomposing a body atom [P0(x1, ..., xn)] as:

   [P1 = P0(x1), P2 = P1(x2), ..., Pn = P{n-1}(xn)]

   we record a dependency from [Pi] to [P{i-1}], and also, if [xi] is in binding
   position, a dependency from [xi] to [Pi] (if [xi] is not in binding position,
   that dependency is implied transitively). *)
let record_dependencies ~dependent_vars columns =
  Iarray.iter
    (fun (Index_layer (_, outer_var, arg, inner_var)) ->
      Variable.Id.Tbl.add dependent_vars (Variable.uid outer_var)
        (Variable.uid inner_var);
      match arg with
      | Bind arg ->
        Variable.Id.Tbl.add dependent_vars (Variable.uid arg)
          (Variable.uid inner_var)
      | Check _ -> ())
    columns

type 'v may_have_implicit_copies =
  | May_have_implicit_copies :
      ('t, 'k, 'v) Column.id * 't variable * 'k variable
      -> 'v may_have_implicit_copies
  | Cannot_have_implicit_copies

(* Check whether a body atom may be used to detect implicit copies in the head.

   More precisely, this assumes that [body_scalar] is the atom restricted to its
   first [pos] columns, that is, the atom [P(X1, ..., Xn)] can be decomposed as
   (taking [p = pos]):

   [P(X1, ..., X_p, ..., Xn) = body_scalar(X1, ..., X_p)(X_{p+1}, ..., Xn)]

   and all [X_i] for [i > p] are in binding position.

   If [X_{pos}] is also in binding position and it has no other occurrence in
   the body, then any output atom in the head of the form:

   [Q(Y1, ..., Yn, X_p) += body_scalar]

   can be rewritten to use a fused union as:

   [Q(Y1, ..., Yn) += body_table]

   where [body_table] represents the trie [{ X_p -> body_scalar }].

   This function returns the pair [(X_p, body_table)] if the conditions above
   hold. *)
let may_have_implicit_copies (type v) ~var_to_body_atoms ~pos ~body_atom_id
    body_columns (body_scalar : v variable) : v may_have_implicit_copies =
  if pos < 0 || pos >= Iarray.length body_columns
  then Cannot_have_implicit_copies
  else
    let (Index_layer (body_column, body_table, body_arg, body_scalar')) =
      Iarray.get body_columns pos
    in
    match body_arg with
    | Check _ -> Cannot_have_implicit_copies
    | Bind body_var -> (
      match Variable.Id.Tbl.find var_to_body_atoms (Variable.uid body_var) with
      | (exception Not_found) | [] -> assert false
      | _ :: _ :: _ -> Cannot_have_implicit_copies
      | [bid'] ->
        assert (bid' = body_atom_id);
        let Equal = Variable.must_be_equal body_scalar body_scalar' in
        May_have_implicit_copies (body_column, body_table, body_var))

(* Check if the column at position [pos] is a copy column for argument
   [body_arg].

   Assuming that the head atom can be written as (taking [p = pos]):

   [Q(X1, ..., X_p) += head_scalar]

   we check if [X_p] is equal to [body_arg] and is the single occurrence of
   [body_arg] in the head.

   If this holds, we return a variable [head_table] representing the trie:

   [head_table = { body_arg -> head_scalar }]

   so that the atom can be rewritten as:

   [Q(X1, ..., X_{p-1}) += head_table]. *)
let is_implicit_copy (type t k v) ~var_to_head_atoms ~pos ~head_atom_id
    head_columns (body_column : (t, k, v) Column.id) (body_arg : k variable)
    (head_scalar : v variable) : t variable option =
  if pos < 0 || pos >= Iarray.length head_columns
  then None
  else
    let (Index_layer (head_column, head_table, head_arg, head_scalar')) =
      Iarray.get head_columns pos
    in
    match head_arg with
    | Check _ -> None
    | Bind head_arg -> (
      match Variable.provably_equal body_arg head_arg with
      | None -> None
      | Some Equal -> (
        match
          Variable.Id.Tbl.find var_to_head_atoms (Variable.uid head_arg)
        with
        | (exception Not_found) | [] -> assert false
        | _ :: _ :: _ -> None
        | [head_atom_id'] ->
          assert (head_atom_id' = head_atom_id);
          let Equal = Variable.must_be_equal head_scalar' head_scalar in
          let Equal = Column.provably_equal_table body_column head_column in
          Some head_table))

(* Check if the provided [head_atom] is an implicit copy from an atom of the
   form [body_scalar := P(..., arg) ], where [arg] is a binding occurrence.

   This is the case in one of the two following conditions:

   - The head atom is already of the form [Q(..., arg) += body_scalar] where
   [arg] is a binding occurrence (i.e. it is the only occurrence of [arg] in the
   [head_atom]);

   - Or the head atom is of the form [Q(..., arg) += ()] where [arg] is a
   binding occurrence and [body_scalar] is of type [unit] -- in which case, we
   can rewrite it to [Q(..., arg) += body_scalar]. *)
let detect_implicit_copy (type s k v) ~binding_times ~var_to_head_atoms
    ~head_atom_id head_atom (body_column : (s, k, v) Column.id)
    (body_arg : k variable) (body_scalar : v variable)
    (result_repr : v Table.result_repr) :
    (bound_table * index_layer iarray * s variable) option =
  match head_atom with
  | Callback_with_bindings _ -> None
  | Union (tid, columns, args, head_scalar, inner_cols, head_repr) -> (
    let[@local] return (columns : (_, _, v) Column.hlist) =
      let table = Variable.create (Table.Id.name tid) in
      let head_columns, head_scalar =
        layout_head_table ~binding_times columns table args
      in
      match
        is_implicit_copy head_columns body_column body_arg head_scalar
          ~pos:(Iarray.length head_columns - 1)
          ~var_to_head_atoms ~head_atom_id
      with
      | None -> None
      | Some head_table ->
        Some (Bound_table (tid, table), head_columns, head_table)
    in
    match
      ( inner_cols,
        Table.result_repr_is_unit result_repr,
        Table.result_repr_is_unit head_repr )
    with
    | [], Some Equal, Some Equal -> return columns
    | ([] | _ :: _), (None | Some Equal), _ -> (
      match head_scalar with
      | Literal _ -> None
      | Variable head_scalar -> (
        match Variable.provably_equal head_scalar body_scalar with
        | None -> None
        | Some Equal -> return columns)))

let add_var_to_atom free_vars_of_atoms var_to_atoms var atom =
  if not (Variable.Id.Set.mem (Variable.uid var) free_vars_of_atoms.(atom))
  then (
    free_vars_of_atoms.(atom)
      <- Variable.Id.Set.add (Variable.uid var) free_vars_of_atoms.(atom);
    let atoms =
      try Variable.Id.Tbl.find var_to_atoms (Variable.uid var)
      with Not_found -> []
    in
    Variable.Id.Tbl.replace var_to_atoms (Variable.uid var) (atom :: atoms))

let remove_var_from_atom free_vars_of_atoms var_to_atoms var atom_id =
  free_vars_of_atoms.(atom_id)
    <- Variable.Id.Set.remove (Variable.uid var) free_vars_of_atoms.(atom_id);
  match Variable.Id.Tbl.find var_to_atoms (Variable.uid var) with
  | exception Not_found -> Misc.fatal_error "Inconsistent var_to_atoms"
  | atom_ids ->
    let atom_ids = List.filter (fun atom' -> atom' <> atom_id) atom_ids in
    if List.is_empty atom_ids
    then Variable.Id.Tbl.remove var_to_atoms (Variable.uid var)
    else Variable.Id.Tbl.replace var_to_atoms (Variable.uid var) atom_ids

let rewrite_head_atom_into_explicit_copy ~free_vars_of_body_atoms
    ~var_to_body_atoms ~free_vars_of_head_atoms ~var_to_head_atoms ~body_atom_id
    body_table body_columns body_scalar ~head_atom_id head_table head_columns
    head_scalar inner_column result_repr =
  let rec loop : type s k.
      offset_from_end:int ->
      s variable ->
      s variable ->
      (s, k, _) Column.hlist ->
      _ =
   fun ~offset_from_end body_scalar head_scalar inner_columns ->
    let[@local] cannot_introduce_copy () =
      assert (offset_from_end <= Iarray.length body_columns);
      assert (offset_from_end <= Iarray.length head_columns);
      add_var_to_atom free_vars_of_head_atoms var_to_head_atoms body_scalar
        head_atom_id;
      let body_columns =
        Iarray.sub body_columns ~pos:0
          ~len:(Iarray.length body_columns - offset_from_end)
      in
      let body_atom =
        Table_layers
          { table = body_table;
            columns = body_columns;
            result = body_scalar;
            bound_prefix = 0
          }
      in
      let head_atom =
        table_head_atom head_table
          ~len:(Iarray.length head_columns - offset_from_end)
          head_columns head_scalar [] [] (Variable body_scalar) inner_columns
          result_repr
      in
      body_atom, head_atom
    in
    match
      may_have_implicit_copies ~var_to_body_atoms
        ~pos:(Iarray.length body_columns - offset_from_end - 1)
        ~body_atom_id body_columns body_scalar
    with
    | Cannot_have_implicit_copies -> cannot_introduce_copy ()
    | May_have_implicit_copies (body_column, body_table, body_var) -> (
      match
        is_implicit_copy head_columns body_column body_var head_scalar
          ~pos:(Iarray.length head_columns - offset_from_end - 1)
          ~var_to_head_atoms ~head_atom_id
      with
      | None -> cannot_introduce_copy ()
      | Some head_table ->
        remove_var_from_atom free_vars_of_body_atoms var_to_body_atoms body_var
          body_atom_id;
        remove_var_from_atom free_vars_of_head_atoms var_to_head_atoms body_var
          head_atom_id;
        loop ~offset_from_end:(offset_from_end + 1) body_table head_table
          (body_column :: inner_columns))
  in
  loop ~offset_from_end:1 body_scalar head_scalar [inner_column]

let plan_rule ({ variables = vars; head; body } as rule) =
  let _, binding_times =
    List.fold_left
      (fun (next_binding_time, bindable_vars) (Variable.Any var) ->
        ( next_binding_time + 1,
          Variable.Id.Map.add (Variable.uid var) next_binding_time bindable_vars
        ))
      (0, Variable.Id.Map.empty) vars
  in
  let free_vars_of_body_atoms, var_to_body_atoms =
    free_vars_atoms ~binding_times body
  in
  let free_vars_of_head_atoms, var_to_head_atoms =
    free_vars_atoms ~binding_times head
  in
  let head_atoms =
    Array.init (Iarray.length head) (fun head_atom_id ->
        let (Atom (relation, args)) = Iarray.get head head_atom_id in
        match relation with
        | Unless _ | Distinct _ | Filter _ ->
          Misc.fatal_error "not supported in the head"
        | Table tid ->
          Union
            ( tid,
              Table.Id.columns tid,
              args,
              lit (Table.Id.default_value tid),
              [],
              Table.Id.result_repr tid )
        | Callback_with_bindings (fn, name) ->
          Callback_with_bindings ({ value = fn; name }, args))
  in
  let dependent_vars = Variable.Id.Tbl.create 0 in
  let rev_tables = ref [] in
  let body_layout =
    Iarray.mapi
      (fun body_atom_id (Atom (relation, args) as body_atom) ->
        let other_body_atom () = { table_layers = None; atom = body_atom } in
        let table_body_atom table_layers =
          { table_layers = Some table_layers; atom = body_atom }
        in
        match relation with
        | Unless _ | Distinct _ | Filter _ | Callback_with_bindings _ ->
          other_body_atom ()
        | Table tid -> (
          let body_table = Variable.create (Table.Id.name tid) in
          rev_tables := Bound_table (tid, body_table) :: !rev_tables;
          let body_columns, body_scalar =
            layout_body_table ~binding_times (Table.Id.columns tid) body_table
              args
          in
          record_dependencies ~dependent_vars body_columns;
          let[@local] no_implicit_copies () =
            Table_layers
              { table = body_table;
                columns = body_columns;
                result = body_scalar;
                bound_prefix = 0
              }
            |> table_body_atom
          in
          match
            may_have_implicit_copies ~var_to_body_atoms
              ~pos:(Iarray.length body_columns - 1)
              ~body_atom_id body_columns body_scalar
          with
          | Cannot_have_implicit_copies -> no_implicit_copies ()
          | May_have_implicit_copies
              (last_body_column, last_body_table, last_body_arg) -> (
            match
              Variable.Id.Tbl.find var_to_head_atoms
                (Variable.uid last_body_arg)
            with
            | (exception Not_found) | [] | _ :: _ :: _ -> no_implicit_copies ()
            | [head_atom_id] -> (
              match
                detect_implicit_copy head_atoms.(head_atom_id) last_body_column
                  last_body_arg body_scalar (Table.Id.result_repr tid)
                  ~var_to_head_atoms ~head_atom_id ~binding_times
              with
              | None -> no_implicit_copies ()
              | Some (bound_head, head_columns, last_head_table) ->
                remove_var_from_atom free_vars_of_body_atoms var_to_body_atoms
                  last_body_arg body_atom_id;
                remove_var_from_atom free_vars_of_head_atoms var_to_head_atoms
                  last_body_arg head_atom_id;
                let body_atom, head_atom =
                  rewrite_head_atom_into_explicit_copy ~free_vars_of_body_atoms
                    ~var_to_body_atoms ~free_vars_of_head_atoms
                    ~var_to_head_atoms ~body_atom_id body_table body_columns
                    last_body_table ~head_atom_id bound_head head_columns
                    last_head_table last_body_column (Table.Id.result_repr tid)
                in
                head_atoms.(head_atom_id) <- head_atom;
                table_body_atom body_atom))))
      body
  in
  let tables = Iarray.of_list (List.rev !rev_tables) in
  let vars =
    (* Drop variables that do not occur in either the body or the head (this is
       the case for variables that have been eliminated due to copy
       optimization). *)
    vars
    |> List.filter (fun (Variable.Any var) ->
        Variable.Id.Tbl.mem var_to_body_atoms (Variable.uid var)
        || Variable.Id.Tbl.mem var_to_head_atoms (Variable.uid var))
    |> Iarray.of_list
  in
  (* Extract existential variables -- innermost variables that don't appear in
     the head. Once we found once instance of the rule with any value of the
     existentials, finding another with the same values for the non-existential
     variables is not useful.

     Note that we need to take into account dependencies: consider the rule

     Q(y) :- P(x, y)

     which we rewrite into:

     (Q += Px) :- (Px := P(x))

     Even though [x] does not occur in the head, [Px], which depends on [x],
     does and so we can't must iterate on all the values of [x].

     On the other hand, if we have:

     R(z) :- P(x, z), Q(x, y)

     which gets rewritten into:

     (R += Px) :- (Px := P(x)), (Qx := Q(x)), Qx(y)

     neither [y] nor its (transitive) dependencies occur in the head, and so it
     is fine to treat it as an existential (note that [z] has disappeared from
     the rule entirely). *)
  let ~vars, ~existentials =
    let rec does_not_occur_in_head_atoms vid =
      (not (Variable.Id.Tbl.mem var_to_head_atoms vid))
      && List.for_all does_not_occur_in_head_atoms
           (Variable.Id.Tbl.find_all dependent_vars vid)
    in
    let num_vars =
      let rec loop n =
        if n <= 0
        then n
        else
          let var = Iarray.get vars (n - 1) in
          let (Variable.Any var) = var in
          if does_not_occur_in_head_atoms (Variable.uid var)
          then loop (n - 1)
          else n
      in
      loop (Iarray.length vars)
    in
    let existentials =
      Iarray.sub vars ~pos:num_vars ~len:(Iarray.length vars - num_vars)
    in
    let vars = Iarray.sub vars ~pos:0 ~len:num_vars in
    ~vars, ~existentials
  in
  let stages = Dynarray.create () in
  (* Initial stage: place any stage that does not involve variables (only
     constants and parameters). *)
  Iarray.iteri
    (fun aid atom_layout ->
      add_stages_involving_no_free_vars
        ~free_vars:free_vars_of_body_atoms.(aid)
        stages atom_layout)
    body_layout;
  let place_stages_involving_var var atom_ids =
    List.iter
      (fun aid ->
        let atom_layout = Iarray.get body_layout aid in
        free_vars_of_body_atoms.(aid)
          <- Variable.Id.Set.remove (Variable.uid var)
               free_vars_of_body_atoms.(aid);
        add_stages_involving_no_free_vars
          ~free_vars:free_vars_of_body_atoms.(aid)
          stages atom_layout)
      atom_ids
  in
  (* Variable stage: this is where we start introducing join stages in a
     top-down way, following the provided ordering. *)
  let variable_stage (Variable.Any var) =
    match Variable.Id.Tbl.find var_to_body_atoms (Variable.uid var) with
    | exception Not_found ->
      Misc.fatal_errorf "Variable %a is either unused or bound twice"
        Variable.print var
    | atom_ids ->
      Variable.Id.Tbl.remove var_to_body_atoms (Variable.uid var);
      let column_iterators =
        List.fold_left
          (fun column_iterators aid ->
            match Iarray.get body_layout aid with
            | { table_layers = None; _ } -> column_iterators
            | { table_layers = Some table_layers; _ } ->
              advance_prefix_and_extract_iterator_on_variable table_layers var
                column_iterators)
          [] atom_ids
      in
      add_join_stage stages var column_iterators;
      place_stages_involving_var var atom_ids
  in
  Iarray.iter variable_stage vars;
  Iarray.iter variable_stage existentials;
  let input_stages = Dynarray.to_array stages |> Iarray.of_array in
  (* At this point, all the involved variables must have been bound, and all the
     input stages are fixed -- perform some safety checks. *)
  if Variable.Id.Tbl.length var_to_body_atoms <> 0
  then (
    Format.eprintf "%a@." print_plan
      { tables;
        input_stages;
        output_atoms = Iarray.of_array head_atoms;
        num_existentials = Iarray.length existentials
      };
    Format.eprintf "%a@." print_rule rule;
    Variable.Id.Tbl.iter
      (fun vid _ -> Format.eprintf "%a@ " Variable.Id.print vid)
      var_to_head_atoms;
    Format.eprintf "@.";
    Misc.fatal_errorf "Free vars (body: %b, head: %b) in datalog rule"
      (Variable.Id.Tbl.length var_to_body_atoms <> 0)
      (Variable.Id.Tbl.length var_to_head_atoms <> 0));
  Iarray.iteri
    (fun aid { table_layers; atom } ->
      if
        not
          (Variable.Id.Set.is_empty free_vars_of_body_atoms.(aid)
          &&
          match table_layers with
          | None -> true
          | Some (Table_layers { columns; bound_prefix; _ }) ->
            bound_prefix = Iarray.length columns)
      then
        Misc.fatal_errorf "*BUG*: Atom was not fully laid out:@ %a" print_atom
          atom)
    body_layout;
  { tables;
    input_stages;
    output_atoms = Iarray.of_array head_atoms;
    num_existentials = Iarray.length existentials
  }
