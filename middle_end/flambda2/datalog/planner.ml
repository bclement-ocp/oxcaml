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

type _ output_relation =
  | Union :
      't variable
      * ('t, 'k, 's) Column.hlist
      * ('s, _, 'v) Column.hlist
      * 'v Table.result_repr
      * 's variable
      -> 'k output_relation
  | Callback_with_bindings :
      (Bytecode.bindings_ref -> 'k Constant.hlist -> unit) * string
      -> 'k output_relation

type output_atom =
  | Output_atom : 'k output_relation * 'k Term.hlist -> output_atom

let print_with_columns columns ppf terms =
  let rec loop : type t k v.
      first:bool ->
      (t, k, v) Column.hlist ->
      Format.formatter ->
      k Term.hlist ->
      unit =
   fun ~first columns ppf terms ->
    match columns, terms with
    | [], [] -> ()
    | column :: columns, term :: terms ->
      if not first then Format.fprintf ppf ",@ ";
      print_term (Column.print_key column) ppf term;
      loop ~first:false columns ppf terms
  in
  loop ~first:true columns ppf terms

let print_output_atom ppf (Output_atom (relation, args)) =
  match relation with
  | Union (table, cols, _, _, v) ->
    Format.fprintf ppf "%a += {[%a] -> %a}" Variable.print table
      (print_with_columns cols) args Variable.print v
  | Callback_with_bindings (fn, name) ->
    print_atom ppf (Lang.callback_with_bindings ~name fn args)

type ('p, 'v) plan =
  { tables : bound_table iarray;
    parameters : 'p Variable.hlist;
    input_stages : stage iarray;
    num_existentials : int;
    output_atoms : output_atom iarray;
    output_tables : bound_table iarray;
    callback : ('v Constant.hlist -> unit) ref
  }

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
      print_output_atom ppf output_atoms;
    if num_existentials > 0
    then Format.fprintf ppf "@ break %d" num_existentials
  in
  print_stages print_output ppf input_stages

type index_layer =
  | Index_layer :
      ('t, 'k, 'v) Column.id * 't variable * 'k term * 'v variable
      -> index_layer

type table_value =
  | Table_value :
      't variable * ('t, 'k, 'v) Column.hlist * 'v Table.result_repr
      -> table_value

type table_layers =
  | Table_layers :
      { table : 't variable;
        columns : index_layer iarray;
        result_repr : 'v Table.result_repr;
        mutable value : table_value;
        (* Updated during planning. *)
        mutable bound_prefix : int;
        mutable erased_suffix : int
      }
      -> table_layers

type _ columns =
  | Columns :
      ('t, 'k, 'v) Column.hlist * 'k Term.hlist * 'v variable
      -> 't columns

let rec table_columns : type t.
    t variable -> index_layer iarray -> pos:int -> len:int -> t columns =
 fun table layers ~pos ~len ->
  if pos >= len
  then Columns ([], [], table)
  else
    let (Index_layer (column, outer_var, arg, inner_var)) =
      Iarray.get layers pos
    in
    let Equal = Variable.must_be_equal table outer_var in
    let (Columns (inner_columns, args, inner_var)) =
      table_columns inner_var layers ~pos:(pos + 1) ~len
    in
    Columns (column :: inner_columns, arg :: args, inner_var)

let is_layer_index_key (type k) (Index_layer (_, _, key, _)) (var : k variable)
    : bool =
  match key with
  | Literal _ -> false
  | Variable key -> Variable.Id.equal (Variable.uid key) (Variable.uid var)

let length (Table_layers { erased_suffix; _ }) = erased_suffix

let get_layer (Table_layers { columns; erased_suffix; _ }) idx =
  if idx >= erased_suffix
  then invalid_arg "get_layer"
  else Iarray.get columns idx

let last_layer (Table_layers { columns; bound_prefix; erased_suffix; _ }) =
  if bound_prefix >= erased_suffix
  then None
  else Some (Iarray.get columns (erased_suffix - 1))

type rewrite = Rewrite : 't variable * 't variable -> rewrite

let apply_rewrite env (type v) (v : v variable) : v variable =
  match Variable.Id.Tbl.find env (Variable.uid v) with
  | exception Not_found -> v
  | Rewrite (v', w) ->
    let Equal = Variable.must_be_equal v v' in
    w

let add_rewrite env (type v) (v : v variable) (v' : v variable) =
  Variable.Id.Tbl.replace env (Variable.uid v) (Rewrite (v, v'))

let slurp0 (Index_layer (col, table, _, value)) (Table_value (var, cols, repr))
    =
  let Equal = Variable.must_be_equal var value in
  Table_value (table, col :: cols, repr)

let consilidate_one_atom env (Index_layer (col1, table1, key1, value1))
    (Table_value (var1, cols1, repr1))
    (Index_layer (col2, table2, key2, value2))
    (Table_value (var2, cols2, repr2)) =
  match key1, key2 with
  | Literal _, _ | _, Literal _ -> None
  | Variable key1, Variable key2 -> (
    let Equal = Variable.must_be_equal var1 value1 in
    let Equal = Variable.must_be_equal var2 value2 in
    match Variable.provably_equal key1 key2 with
    | None -> None
    | Some Equal -> (
      let value1 = apply_rewrite env value1 in
      match Variable.provably_equal value1 value2 with
      | Some Equal ->
        let Equal = Column.provably_equal col1 col2 in
        Some
          (Rewrite (table1, table2), Table_value (table1, col1 :: cols1, repr1))
      | None -> (
        let is_unit1 = Table.provably_unit_repr repr1 in
        let is_unit2 = Table.provably_unit_repr repr2 in
        match is_unit1, is_unit2, cols1, cols2 with
        | Some Equal, Some Equal, [], [] ->
          let Equal = Column.provably_equal col1 col2 in
          Some
            ( Rewrite (table1, table2),
              Table_value (table1, col1 :: cols1, repr1) )
        | (None | Some Equal), _, ([] | _ :: _), _ -> None)))

(* Returns the variable associated with the value of the last layer if it is the
   only layer indexed by [var]. *)
let last_layer_if_unique_key (type v) layers (var : v variable) =
  match last_layer layers with
  | Some last_layer when is_layer_index_key last_layer var ->
    let rec is_not_key_of_earlier_layer idx =
      let idx = idx - 1 in
      if idx < 0
      then true
      else if is_layer_index_key (get_layer layers idx) var
      then false
      else is_not_key_of_earlier_layer idx
    in
    if is_not_key_of_earlier_layer (length layers - 1)
    then Some (layers, last_layer)
    else None
  | _ -> None

type atom_layout =
  { table_layers : table_layers option;
    atom : atom;
    (* Variables are removed from this list as they are bound during
       planning. *)
    mutable free_vars : Variable.Id.Set.t
  }

let last_layer_of_atom_if_unique_key var { table_layers; _ } =
  match table_layers with
  | Some table_layers -> last_layer_if_unique_key table_layers var
  | None -> None

let layout_table_atom : type t k v.
    (t, k, v) Column.hlist ->
    v Table.result_repr ->
    t variable ->
    k Term.hlist ->
    table_layers =
 fun columns value_repr table args ->
  let columns, value, result_repr =
    let rec loop : type t k.
        _ ->
        (t, k, v) Column.hlist ->
        t variable ->
        k Term.hlist ->
        _ * _ * v Table.result_repr =
     fun rev_plan columns outer_var args ->
      match columns, args with
      | [], [] ->
        ( Iarray.of_list (List.rev rev_plan),
          Table_value (outer_var, [], value_repr),
          value_repr )
      | column :: columns, arg :: args ->
        let is_last_var : type t k v.
            (t, k, v) Column.hlist -> v Table.result_repr -> string =
         fun columns repr ->
          match columns, Table.provably_unit_repr repr with
          | [], Some Equal -> "()"
          | ([] | _ :: _), (None | Some Equal) ->
            Format.asprintf "%a[%a]" Variable.print outer_var
              (print_term (Column.print_key column))
              arg
        in
        let inner_var = Variable.create (is_last_var columns value_repr) in
        loop
          (Index_layer (column, outer_var, arg, inner_var) :: rev_plan)
          columns inner_var args
    in
    loop [] columns table args
  in
  Table_layers
    { table;
      columns;
      result_repr;
      value;
      bound_prefix = 0;
      erased_suffix = Iarray.length columns
    }

let rec free_vars_term_hlist : type a. a Term.hlist -> Variable.Id.Set.t =
 fun terms ->
  match terms with
  | [] -> Variable.Id.Set.empty
  | Literal _ :: terms -> free_vars_term_hlist terms
  | Variable v :: terms ->
    Variable.Id.Set.add (Variable.uid v) (free_vars_term_hlist terms)

let layout_body_atom bound_tables atom =
  let (Atom (relation, terms)) = atom in
  let bound_tables, table_layers =
    match relation with
    | Table tid ->
      let var = Variable.create (Table.Id.name tid) in
      let seminaive_tables = Bound_table (tid, var) :: bound_tables in
      let table_layers =
        layout_table_atom (Table.Id.columns tid) (Table.Id.result_repr tid) var
          terms
      in
      seminaive_tables, Some table_layers
    | Unless _ | Distinct _ | Filter _ | Callback_with_bindings _ ->
      bound_tables, None
  in
  bound_tables, { table_layers; atom; free_vars = free_vars_term_hlist terms }

let layout_head_atom output_tables atom =
  let (Atom (relation, args)) = atom in
  let output_tables, table_layers =
    match relation with
    | Table tid ->
      let var = Variable.create (Table.Id.name tid) in
      let output_tables = Bound_table (tid, var) :: output_tables in
      let table_layers =
        layout_table_atom (Table.Id.columns tid) (Table.Id.result_repr tid) var
          args
      in
      output_tables, Some table_layers
    | Unless _ | Distinct _ | Filter _ | Callback_with_bindings _ ->
      output_tables, None
  in
  output_tables, { table_layers; atom; free_vars = free_vars_term_hlist args }

let add_join_stage stages var columns =
  Dynarray.add_last stages (Join_stage (var, columns))

let add_seek_stage stages term columns =
  Dynarray.add_last stages (Seek_stage (term, columns))

let add_check_stage stages atom = Dynarray.add_last stages (Check_stage atom)

let add_stages_involving_no_free_vars stages atom_decomposition =
  let free_vars = atom_decomposition.free_vars in
  match atom_decomposition.table_layers with
  | Some
      (Table_layers ({ columns; bound_prefix; erased_suffix; _ } as plan_table))
    ->
    let rec loop bound_prefix =
      let[@local] stop_iteration () = plan_table.bound_prefix <- bound_prefix in
      if bound_prefix = erased_suffix
      then stop_iteration ()
      else
        let index_layer = Iarray.get columns bound_prefix in
        let (Index_layer (col, outer, arg, inner)) = index_layer in
        match arg with
        | Variable var when Variable.Id.Set.mem (Variable.uid var) free_vars ->
          stop_iteration ()
        | Variable _ | Literal _ ->
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
  | Table_layers ({ columns; bound_prefix; erased_suffix; _ } as layers) -> (
    let (Index_layer (column, outer_var, arg, inner_var)) =
      Iarray.get columns bound_prefix
    in
    match arg with
    | Literal _ -> iterators
    | Variable arg_var -> (
      match Variable.provably_equal var arg_var with
      | None -> iterators
      | Some Equal ->
        if bound_prefix >= erased_suffix then Misc.fatal_error "inconsistent";
        layers.bound_prefix <- bound_prefix + 1;
        Column_iterator (column, outer_var, inner_var) :: iterators))

let var_to_atoms atoms =
  let var_to_atoms = Variable.Id.Tbl.create 0 in
  Iarray.iteri
    (fun aid atom_layout ->
      let free_vars = atom_layout.free_vars in
      Variable.Id.Set.iter
        (fun vid ->
          match Variable.Id.Tbl.find_opt var_to_atoms vid with
          | None -> Variable.Id.Tbl.replace var_to_atoms vid [aid]
          | Some atoms -> Variable.Id.Tbl.replace var_to_atoms vid (aid :: atoms))
        free_vars)
    atoms;
  var_to_atoms

let plan_rule ?(callback = ref ignore) parameters vars { head; body } =
  let vars = Iarray.of_list vars in
  let tables, body_layout = Iarray.fold_left_map layout_body_atom [] body in
  let tables = Iarray.of_list (List.rev tables) in
  let var_to_body_atoms = var_to_atoms body_layout in
  let output_tables, head_atoms =
    Iarray.fold_left_map layout_head_atom [] head
  in
  let output_tables = Iarray.of_list (List.rev output_tables) in
  let var_to_head_atoms = var_to_atoms head_atoms in
  let compute_existentials ~num_existentials index =
    let rec loop ~num_existentials index =
      if index < 0
      then num_existentials
      else
        let (Any last_var : Variable.t_) = Iarray.get vars index in
        let last_vid = Variable.uid last_var in
        if Variable.Id.Tbl.mem var_to_head_atoms last_vid
        then num_existentials
        else loop ~num_existentials:(num_existentials + 1) (index - 1)
    in
    loop ~num_existentials index
  in
  let env = Variable.Id.Tbl.create 0 in
  let rec consolidate_copies index =
    if index < 0
    then 0
    else
      let (Any last_var : Variable.t_) = Iarray.get vars index in
      let last_vid = Variable.uid last_var in
      match Variable.Id.Tbl.find_opt var_to_head_atoms last_vid with
      | None -> index + 1
      | Some output_atoms -> (
        match Variable.Id.Tbl.find_opt var_to_body_atoms last_vid with
        | Some [input_atom_id] -> (
          let input_atom = Iarray.get body_layout input_atom_id in
          match last_layer_of_atom_if_unique_key last_var input_atom with
          | None -> index + 1
          | Some (Table_layers input_layers, last_layer_of_input_atom) ->
            let new_output_values =
              List.filter_map
                (fun output_id ->
                  let output_atom = Iarray.get head_atoms output_id in
                  match output_atom.table_layers with
                  | None -> None
                  | Some (Table_layers output_layers as tlayers) -> (
                    match last_layer_if_unique_key tlayers last_var with
                    | None -> None
                    | Some (_, last_layer_of_output_atom) ->
                      consilidate_one_atom env last_layer_of_output_atom
                        output_layers.value last_layer_of_input_atom
                        input_layers.value))
                output_atoms
            in
            if List.compare_lengths output_atoms new_output_values = 0
            then (
              let update_atom atom table_value =
                atom.free_vars
                  <- Variable.Id.Set.remove (Variable.uid last_var)
                       atom.free_vars;
                let (Table_layers layers) = Option.get atom.table_layers in
                layers.value <- table_value;
                layers.erased_suffix <- layers.erased_suffix - 1
              in
              update_atom input_atom
                (slurp0 last_layer_of_input_atom input_layers.value);
              Variable.Id.Tbl.remove var_to_body_atoms last_vid;
              Variable.Id.Tbl.remove var_to_head_atoms last_vid;
              List.iter2
                (fun output_id (Rewrite (table1, table2), table_value) ->
                  add_rewrite env table1 table2;
                  update_atom (Iarray.get head_atoms output_id) table_value)
                output_atoms new_output_values;
              consolidate_copies (index - 1))
            else index + 1)
        | _ -> index + 1)
  in
  let num_existentials =
    compute_existentials ~num_existentials:0 (Iarray.length vars - 1)
  in
  let len = consolidate_copies (Iarray.length vars - 1 - num_existentials) in
  let vars =
    Iarray.append
      (Iarray.sub vars ~pos:0 ~len)
      (Iarray.sub vars
         ~pos:(Iarray.length vars - num_existentials)
         ~len:num_existentials)
  in
  let stages = Dynarray.create () in
  (* Constant stage: place any stage that does not involve variables. *)
  Iarray.iter
    (fun atom_layout -> add_stages_involving_no_free_vars stages atom_layout)
    body_layout;
  let place_stages_involving_var var atom_ids =
    List.iter
      (fun aid ->
        let atom_layout = Iarray.get body_layout aid in
        atom_layout.free_vars
          <- Variable.Id.Set.remove (Variable.uid var) atom_layout.free_vars;
        add_stages_involving_no_free_vars stages atom_layout)
      atom_ids
  in
  (* Parameter stage: place any stage only involving parameters. *)
  Variable.iter_hlist
    (fun (Any param) ->
      match Variable.Id.Tbl.find var_to_body_atoms (Variable.uid param) with
      | exception Not_found ->
        Misc.fatal_errorf "Parameter %a is either unused or bound twice"
          Variable.print param
      | atom_ids ->
        Variable.Id.Tbl.remove var_to_body_atoms (Variable.uid param);
        place_stages_involving_var param atom_ids)
    parameters;
  (* Variable stage: this is where we start introducing join stages in a
     top-down way, following the provided ordering. *)
  Iarray.iter
    (fun (Variable.Any var) ->
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
        place_stages_involving_var var atom_ids)
    vars;
  (* At this point, all the involved variables must have been bound, and all the
     input stages are fixed -- perform some safety checks. *)
  if Variable.Id.Tbl.length var_to_body_atoms <> 0
  then Misc.fatal_errorf "Free vars in datalog rule";
  Iarray.iter
    (fun { table_layers; free_vars; atom } ->
      if
        not
          (Variable.Id.Set.is_empty free_vars
          &&
          match table_layers with
          | None -> true
          | Some (Table_layers { bound_prefix; erased_suffix; _ }) ->
            bound_prefix = erased_suffix)
      then
        Misc.fatal_errorf "*BUG*: Atom was not fully laid out:@ %a" print_atom
          atom)
    body_layout;
  let input_stages = Dynarray.to_array stages |> Iarray.of_array in
  let output_atoms =
    Iarray.map
      (fun { table_layers; atom = Atom (relation, args); _ } ->
        match table_layers with
        | Some (Table_layers { table; columns; value; erased_suffix; _ }) ->
          let (Table_value (inner_var, inner_cols, value_repr)) = value in
          let (Columns (outer_cols, args, inner_var')) =
            table_columns table columns ~pos:0 ~len:erased_suffix
          in
          let Equal = Variable.must_be_equal inner_var inner_var' in
          let inner_var = apply_rewrite env inner_var in
          Output_atom
            (Union (table, outer_cols, inner_cols, value_repr, inner_var), args)
        | None -> (
          match relation with
          | Callback_with_bindings (fn, name) ->
            Output_atom (Callback_with_bindings (fn, name), args)
          | Table _ | Unless _ | Distinct _ | Filter _ ->
            Misc.fatal_error "nope"))
      head_atoms
  in
  { tables;
    parameters;
    input_stages;
    output_atoms;
    num_existentials;
    output_tables;
    callback
  }
