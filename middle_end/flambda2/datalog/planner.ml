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

type _ defining_expr =
  | Term : 'v term -> 'v defining_expr
  | Join : 'v term * 'v term -> 'v defining_expr

type stage =
  | Join_stage : 'k variable * 'k column_iterator list -> stage
  | Seek_stage : 'k term * 'k column_iterator list -> stage
  | Check_stage : atom -> stage
  | Let_value_stage :
      'v Table.result_repr * 'v variable * 'v defining_expr
      -> stage

type bound_table =
  | Bound_table : ('t, 'k, 'v) Table.Id.t * 't variable -> bound_table

type ('p, 'v) plan =
  { tables : bound_table iarray;
    parameters : 'p Variable.hlist;
    input_stages : stage iarray;
    num_existentials : int;
    output_atoms : atom iarray;
    callback : ('v Constant.hlist -> unit) ref
  }

let print_defining_expr repr ppf expr =
  match expr with
  | Term t -> print_term (Table.result_repr_print repr) ppf t
  | Join (t1, t2) ->
    Format.fprintf ppf "%a ∨ %a"
      (print_term (Table.result_repr_print repr))
      t1
      (print_term (Table.result_repr_print repr))
      t2

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
  | Let_value_stage (repr, dst, defining_expr) ->
    Format.fprintf ppf "@[<h>if let %a = %a@]" Variable.print dst
      (print_defining_expr repr) defining_expr

let print_stages print ppf stages =
  let depth = ref 0 in
  for i = 0 to Iarray.length stages - 1 do
    let stage = Iarray.get stages i in
    let extra_indent =
      match stage with
      | Join_stage _ -> 2
      | Seek_stage _ | Check_stage _ | Let_value_stage _ -> 0
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
      print_atom ppf output_atoms;
    if num_existentials > 0
    then Format.fprintf ppf "@ break %d" num_existentials
  in
  print_stages print_output ppf input_stages

type index_layer =
  | Index_layer :
      ('t, 'k, 'v) Column.id * 't variable * 'k term * 'v variable
      -> index_layer

type table_layers =
  | Table_layers :
      { table : 't variable;
        columns : index_layer iarray;
        result_repr : 'v Table.result_repr;
        result : 'v variable;
            (* This is the variable bound by the layers, i.e. the value of the
               last column. *)
        atom_value : 'v variable option;
        (* This is the (optional) value for the atom. If it is a variable, it
           must be copied from the [result] variable. *)
        (* Mutable fields below are updated during planning. *)
        mutable bound_prefix : int
      }
      -> table_layers

type atom_layout =
  { table_layers : table_layers option;
    atom : atom;
    late_bound_vars : Variable.Id.Set.t;
    (* Variables that are bound at the time the atom is computed (e.g. value of
       a table). *)
    mutable free_vars : Variable.Id.Set.t
        (* Variables are removed from this list as they are bound during
           planning. *)
  }

let layout_table_atom : type t k v.
    (t, k, v) Column.hlist ->
    t variable ->
    k Term.hlist ->
    v Table.result_repr ->
    v variable option ->
    table_layers =
 fun columns table args result_repr atom_value ->
  let columns, result =
    let rec loop : type t k.
        _ ->
        (t, k, v) Column.hlist ->
        t variable ->
        k Term.hlist ->
        _ * v variable =
     fun rev_plan columns outer_var args ->
      match columns, args with
      | [], [] -> Iarray.of_list (List.rev rev_plan), outer_var
      | column :: columns, arg :: args ->
        let inner_var =
          Variable.create
            (Format.asprintf "%a[%a]" Variable.print outer_var
               (print_term (Column.print_key column))
               arg)
        in
        loop
          (Index_layer (column, outer_var, arg, inner_var) :: rev_plan)
          columns inner_var args
    in
    loop [] columns table args
  in
  Table_layers
    { columns; table; result; atom_value; result_repr; bound_prefix = 0 }

let rec free_vars_term_hlist : type a. a Term.hlist -> Variable.Id.Set.t =
 fun terms ->
  match terms with
  | [] -> Variable.Id.Set.empty
  | Literal _ :: terms -> free_vars_term_hlist terms
  | Variable v :: terms ->
    Variable.Id.Set.add (Variable.uid v) (free_vars_term_hlist terms)

let layout_atom bound_tables atom =
  let (Atom (relation, terms, atom_value)) = atom in
  let bound_tables, table_layers =
    match relation with
    | Table tid ->
      let var = Variable.create (Table.Id.name tid) in
      let seminaive_tables = Bound_table (tid, var) :: bound_tables in
      let table_layers =
        layout_table_atom (Table.Id.columns tid) var terms
          (Table.Id.result_repr tid) atom_value
      in
      seminaive_tables, Some table_layers
    | Unless _ | Distinct _ | Filter _ | Callback_with_bindings _ ->
      bound_tables, None
  in
  let free_vars = free_vars_term_hlist terms in
  let late_bound_vars =
    match atom_value with
    | None -> Variable.Id.Set.empty
    | Some atom_var -> Variable.Id.Set.singleton (Variable.uid atom_var)
  in
  bound_tables, { table_layers; atom; late_bound_vars; free_vars }

let add_join_stage stages var columns =
  Dynarray.add_last stages (Join_stage (var, columns))

let add_seek_stage stages term columns =
  Dynarray.add_last stages (Seek_stage (term, columns))

let add_check_stage stages atom = Dynarray.add_last stages (Check_stage atom)

let add_join_values_stage stages repr dst src1 src2 =
  Dynarray.add_last stages (Let_value_stage (repr, dst, Join (src1, src2)))

let add_let_value_stage stages repr var term =
  Dynarray.add_last stages (Let_value_stage (repr, var, Term term))

type late_binding = Late_binding : 'v variable * 'v term -> late_binding

let add_stages_involving_no_free_vars stages atom_decomposition =
  let free_vars = atom_decomposition.free_vars in
  match atom_decomposition.table_layers with
  | Some (Table_layers ({ columns; bound_prefix; _ } as plan_table)) ->
    let rec loop bound_prefix =
      let[@local] stop_iteration bound_vars =
        plan_table.bound_prefix <- bound_prefix;
        bound_vars
      in
      if bound_prefix = Iarray.length columns
      then
        match plan_table.atom_value with
        | None -> stop_iteration []
        | Some value_var ->
          stop_iteration [Late_binding (value_var, Lang.var plan_table.result)]
      else
        let index_layer = Iarray.get columns bound_prefix in
        let (Index_layer (col, outer, arg, inner)) = index_layer in
        match arg with
        | Variable var when Variable.Id.Set.mem (Variable.uid var) free_vars ->
          stop_iteration []
        | Variable _ | Literal _ ->
          add_seek_stage stages arg [Column_iterator (col, outer, inner)];
          loop (bound_prefix + 1)
    in
    loop bound_prefix
  | None ->
    if Variable.Id.Set.is_empty free_vars
    then (
      add_check_stage stages atom_decomposition.atom;
      let (Atom (_, _, value_opt)) = atom_decomposition.atom in
      match value_opt with
      | None -> []
      | Some _value_var ->
        Misc.fatal_error
          "Datalog: value binding is only supported for table atoms")
    else []

let advance_prefix_and_extract_iterator_on_variable (type a) table_layers
    (var : a variable) (iterators : a column_iterator list) :
    a column_iterator list =
  match table_layers with
  | Table_layers ({ columns; bound_prefix; _ } as layers) -> (
    let (Index_layer (column, outer_var, arg, inner_var)) =
      Iarray.get columns bound_prefix
    in
    match arg with
    | Literal _ -> iterators
    | Variable arg_var -> (
      match Variable.provably_equal var arg_var with
      | None -> iterators
      | Some Equal ->
        layers.bound_prefix <- bound_prefix + 1;
        Column_iterator (column, outer_var, inner_var) :: iterators))

type late_bound_var =
  | Late_bound_var :
      { late_bound_var : 'v variable;
        result_repr : 'v Table.result_repr;
        yet_to_be_bound : (int, unit) Hashtbl.t;
        mutable current_term : 'v term option
      }
      -> late_bound_var

let late_binding_for repr var =
  Late_bound_var
    { late_bound_var = var;
      result_repr = repr;
      yet_to_be_bound = Hashtbl.create 0;
      current_term = None
    }

let add_atom_for_late_bound_var (Late_bound_var { yet_to_be_bound; _ }) aid =
  if Hashtbl.mem yet_to_be_bound aid
  then Misc.fatal_error "Datalog: duplicate atom for late-bound var";
  Hashtbl.add yet_to_be_bound aid ()

let plan_rule ?(callback = ref ignore) parameters vars { head; body } =
  let tables, body_layout = Iarray.fold_left_map layout_atom [] body in
  let tables = Iarray.of_list (List.rev tables) in
  let var_to_atoms = Variable.Id.Tbl.create 0 in
  let late_bound_vars_to_atoms = Variable.Id.Tbl.create 0 in
  Iarray.iteri
    (fun aid atom_layout ->
      Variable.Id.Set.iter
        (fun vid ->
          match Variable.Id.Tbl.find_opt var_to_atoms vid with
          | None -> Variable.Id.Tbl.replace var_to_atoms vid [aid]
          | Some atoms -> Variable.Id.Tbl.replace var_to_atoms vid (aid :: atoms))
        atom_layout.free_vars;
      let (Atom (relation, _, value_opt)) = atom_layout.atom in
      match value_opt with
      | None -> ()
      | Some var ->
        let late_binding =
          let vid = Variable.uid var in
          try Variable.Id.Tbl.find late_bound_vars_to_atoms vid
          with Not_found -> (
            match relation with
            | Table tid ->
              let late_binding =
                late_binding_for (Table.Id.result_repr tid) var
              in
              Variable.Id.Tbl.replace late_bound_vars_to_atoms vid late_binding;
              late_binding
            | Unless _ | Distinct _ | Filter _ | Callback_with_bindings _ ->
              Misc.fatal_errorf
                "Datalog: value binding is only supported for table atoms")
        in
        add_atom_for_late_bound_var late_binding aid)
    body_layout;
  (* Drop late-bound variables from the iteration order -- only value positions
     of late-bound variables are binding. *)
  let vars =
    List.filter
      (fun (Variable.Any var) ->
        not (Variable.Id.Tbl.mem late_bound_vars_to_atoms (Variable.uid var)))
      vars
  in
  let stages = Dynarray.create () in
  let rec place_stages_involving_var vid atom_ids =
    let extra_late_bound_vars =
      List.fold_left
        (fun extra_vars aid ->
          let atom_layout = Iarray.get body_layout aid in
          atom_layout.free_vars
            <- Variable.Id.Set.remove vid atom_layout.free_vars;
          List.fold_left (place_late_binding aid) extra_vars
            (add_stages_involving_no_free_vars stages atom_layout))
        Variable.Id.Set.empty atom_ids
    in
    place_stages_involving_vars extra_late_bound_vars
  and place_late_binding aid acc (Late_binding (var, term)) =
    let vid = Variable.uid var in
    match Variable.Id.Tbl.find late_bound_vars_to_atoms vid with
    | exception Not_found -> assert false
    | Late_bound_var ({ late_bound_var; yet_to_be_bound; _ } as binding) ->
      let Equal = Variable.must_be_equal var late_bound_var in
      if not (Hashtbl.mem yet_to_be_bound aid)
      then
        Misc.fatal_errorf "late-bound var %a is not bound by atom %d"
          Variable.print var aid;
      Hashtbl.remove yet_to_be_bound aid;
      let current_term =
        match binding.current_term with
        | None -> term
        | Some current_term ->
          let var = Variable.create (Variable.name var) in
          add_join_values_stage stages binding.result_repr var term current_term;
          Lang.var var
      in
      binding.current_term <- Some current_term;
      if Hashtbl.length yet_to_be_bound = 0
      then (
        Variable.Id.Tbl.remove late_bound_vars_to_atoms vid;
        add_let_value_stage stages binding.result_repr var current_term;
        Variable.Id.Set.add vid acc)
      else acc
  and place_stages_involving_vars vars =
    Variable.Id.Set.iter
      (fun vid ->
        match Variable.Id.Tbl.find var_to_atoms vid with
        | exception Not_found -> ()
        | atom_ids ->
          Variable.Id.Tbl.remove var_to_atoms vid;
          place_stages_involving_var vid atom_ids)
      vars
  in
  (* Constant stage: place any stage that does not involve variables. *)
  let _, extra_constants =
    Iarray.fold_left
      (fun (aid, extra_constants) atom_layout ->
        ( aid + 1,
          List.fold_left (place_late_binding aid) extra_constants
            (add_stages_involving_no_free_vars stages atom_layout) ))
      (0, Variable.Id.Set.empty) body_layout
  in
  place_stages_involving_vars extra_constants;
  (* Parameter stage: place any stage only involving parameters. *)
  Variable.iter_hlist
    (fun (Any param) ->
      match Variable.Id.Tbl.find var_to_atoms (Variable.uid param) with
      | exception Not_found ->
        Misc.fatal_errorf "Parameter %a is either unused or bound twice"
          Variable.print param
      | atom_ids ->
        Variable.Id.Tbl.remove var_to_atoms (Variable.uid param);
        place_stages_involving_var (Variable.uid param) atom_ids)
    parameters;
  (* Variable stage: this is where we start introducing join stages in a
     top-down way, following the provided ordering. *)
  List.iter
    (fun (Variable.Any var) ->
      match Variable.Id.Tbl.find var_to_atoms (Variable.uid var) with
      | exception Not_found ->
        Misc.fatal_errorf "Variable %a is either unused or bound twice"
          Variable.print var
      | atom_ids ->
        Variable.Id.Tbl.remove var_to_atoms (Variable.uid var);
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
        place_stages_involving_var (Variable.uid var) atom_ids)
    vars;
  (* At this point, all the involved variables must have been bound, and all the
     input stages are fixed -- perform some safety checks. *)
  if Variable.Id.Tbl.length var_to_atoms <> 0
  then Misc.fatal_error "Free vars in datalog rule";
  if Variable.Id.Tbl.length late_bound_vars_to_atoms <> 0
  then Misc.fatal_error "Free late vars in datalog rule";
  Iarray.iter
    (fun { table_layers; free_vars; late_bound_vars = _; atom } ->
      if
        not
          (Variable.Id.Set.is_empty free_vars
          &&
          match table_layers with
          | None -> true
          | Some (Table_layers { columns; bound_prefix; _ }) ->
            bound_prefix = Iarray.length columns)
      then
        Misc.fatal_errorf "*BUG*: Atom was not fully laid out:@ %a" print_atom
          atom)
    body_layout;
  let input_stages = Dynarray.to_array stages |> Iarray.of_array in
  (* Compute the existentials: innermost variables that don't appear in the
     head. *)
  let num_existentials =
    let vars = Iarray.of_list vars in
    let free_vars_head =
      Iarray.fold_left
        (fun free_vars (Atom (_, terms, value_opt)) ->
          let free_vars =
            Variable.Id.Set.union free_vars (free_vars_term_hlist terms)
          in
          match value_opt with
          | None -> free_vars
          | Some result_var ->
            Variable.Id.Set.add (Variable.uid result_var) free_vars)
        Variable.Id.Set.empty head
    in
    let rec loop n =
      if n >= Iarray.length vars
      then n
      else
        let var = Iarray.get vars (Iarray.length vars - n - 1) in
        let (Variable.Any var) = var in
        if Variable.Id.Set.mem (Variable.uid var) free_vars_head
        then n
        else loop (n + 1)
    in
    loop 0
  in
  { tables;
    parameters;
    input_stages;
    output_atoms = head;
    num_existentials;
    callback
  }
