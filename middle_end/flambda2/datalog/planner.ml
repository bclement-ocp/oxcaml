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
    Format.fprintf ppf "@[<1>@[%a@](@,@[%a@])%a@]" Table.Id.print tid
      (Term.print_columns
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
         columns)
      args
      (fun ppf value ->
        match value with
        | Literal _ -> ()
        | Variable var -> Format.fprintf ppf " <= %a" Variable.print var)
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

   An occurrence is binding and will participate in the join defining the
   variable if:

   - It is the first (outermost) occurrence of the variable in the atom, and

   - There is no previous (outer) occurrences of a variable that must be bound
   earlier ccording to the global variable ordering.

   For instance, the first occurrence of [X] in [P(X, Y, X)] is always binding,
   but the occurrence of [Y] is only binding if [Y] is after [X] in the global
   variable ordering. *)
type 'a arg =
  | Bind of 'a variable
  | Check of 'a term

type index_layer =
  | Index_layer :
      ('t, 'k, 'v) Column.id * 't variable * 'k arg * 'v variable
      -> index_layer

type table_layers =
  | Table_layers :
      { table : 't variable;
        columns : index_layer iarray;
        result : 'v variable;
        result_repr : 'v Table.result_repr;
        (* Updated during planning. *)
        mutable bound_prefix : int
      }
      -> table_layers

type atom_layout =
  { table_layers : table_layers option;
    atom : atom
  }

type head_column =
  | Head_column :
      ('t, 'k, 'v) Column.id * 't variable * 'k term * 'v variable
      -> head_column

type table_head_atom =
  | Table_head_atom :
      { table_id : ('t, _, _) Table.Id.t;
        table : 't variable;
        columns : head_column iarray
      }
      -> table_head_atom

let innermost_arg_is_binding columns =
  if Iarray.length columns = 0
  then None
  else
    let (Index_layer (_, _, arg, _)) =
      Iarray.get columns (Iarray.length columns - 1)
    in
    match arg with Check _ -> None | Bind arg -> Some (Variable.Any arg)

let layout_table_atom : type t k v.
    binding_times:_ ->
    dependent_vars:_ ->
    (t, k, v) Column.hlist ->
    t variable ->
    k Term.hlist ->
    _ * v variable =
 fun ~binding_times ~dependent_vars columns table args ->
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
      Variable.Id.Tbl.add dependent_vars (Variable.uid outer_var)
        (Variable.uid inner_var);
      (* Only the first (outermost) position of a variable is binding and can
         participate in a join defining that variable. *)
      let arg, min_binding_time =
        match arg with
        | Variable var -> (
          Variable.Id.Tbl.add dependent_vars (Variable.uid var)
            (Variable.uid inner_var);
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

let rec free_vars_term_hlist : type a. a Term.hlist -> Variable.Id.Set.t =
 fun terms ->
  match terms with
  | [] -> Variable.Id.Set.empty
  | Literal _ :: terms -> free_vars_term_hlist terms
  | Variable v :: terms ->
    Variable.Id.Set.add (Variable.uid v) (free_vars_term_hlist terms)

let layout_table_head_atom : type s.
    _ -> _ -> (_, _, s) Column.hlist -> _ -> table_head_atom * s variable =
 fun table_id table columns args ->
  let rec loop : type t k.
      _ ->
      (t, k, s) Column.hlist ->
      t variable ->
      k Term.hlist ->
      table_head_atom * s variable =
   fun rev_plan columns scalar args ->
    match columns, args with
    | [], [] ->
      let columns = Iarray.of_list (List.rev rev_plan) in
      Table_head_atom { table_id; columns; table }, scalar
    | column :: columns, arg :: args ->
      let inner_scalar =
        Variable.create
          (Format.asprintf "%a[%a]" Variable.print scalar
             (print_term (Column.print_key column))
             arg)
      in
      loop
        (Head_column (column, scalar, arg, inner_scalar) :: rev_plan)
        columns inner_scalar args
  in
  loop [] columns table args

let layout_head_atom (Atom (relation, args)) =
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
    Callback_with_bindings ({ value = fn; name }, args)

let rec table_head_atom : type a k t s v.
    (a, _, _) Table.Id.t ->
    a variable ->
    len:int ->
    head_column iarray ->
    t variable ->
    (t, k, s) Column.hlist ->
    k Term.hlist ->
    s term ->
    (s, _, v) Column.hlist ->
    v Table.result_repr ->
    head_atom =
 fun tid table ~len head_columns current columns args value inner_cols repr ->
  if len = 0
  then
    let Equal = Variable.must_be_equal table current in
    Union (tid, columns, args, value, inner_cols, repr)
  else
    let (Head_column (column, outer_var, arg, inner_var)) =
      Iarray.get head_columns (len - 1)
    in
    let Equal = Variable.must_be_equal inner_var current in
    table_head_atom tid table ~len:(len - 1) head_columns outer_var
      (column :: columns) (arg :: args) value inner_cols repr

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

let can_do_the_thing (type v k) (arg : k variable) (body_scalar : v variable)
    (result_repr : v Table.result_repr) head_atom =
  let[@local] check_last_arg tid table columns args : (_ * v variable) option =
    let (Table_head_atom { columns; _ } as result), head_scalar =
      layout_table_head_atom tid table columns args
    in
    if Iarray.length columns = 0
    then None
    else
      let (Head_column (_, _, head_arg, _)) =
        Iarray.get columns (Iarray.length columns - 1)
      in
      match head_arg with
      | Variable head_arg
        when Variable.Id.equal (Variable.uid head_arg) (Variable.uid arg) ->
        Some (result, head_scalar)
      | Literal _ | Variable _ -> None
  in
  match head_atom with
  | Callback_with_bindings _ -> None
  | Union (tid, columns, args, head_scalar, inner_cols, head_repr) -> (
    match
      ( inner_cols,
        Table.result_repr_is_unit result_repr,
        Table.result_repr_is_unit head_repr )
    with
    | [], Some Equal, Some Equal ->
      let table = Variable.create (Table.Id.name tid) in
      check_last_arg tid table columns args
    | ([] | _ :: _), (None | Some Equal), _ -> (
      match head_scalar with
      | Literal _ -> None
      | Variable head_scalar -> (
        match Variable.provably_equal head_scalar body_scalar with
        | None -> None
        | Some Equal ->
          let table = Variable.create (Table.Id.name tid) in
          check_last_arg tid table columns args)))

exception Cannot_introduce_copy

let introduce_copy_into_head_atoms ~var_to_body_atoms ~var_to_head_atoms
    ~body_atom_id body_columns body_scalar head_atoms head_scalars inner_columns
    result_repr =
  let rec loop : type s k.
      int -> s variable -> s variable list -> (s, k, _) Column.hlist -> _ =
   fun offset_from_end body_scalar head_scalars inner_columns ->
    let[@local] cannot_introduce_copy () =
      assert (
        not (Variable.Id.Tbl.mem var_to_head_atoms (Variable.uid body_scalar)));
      Variable.Id.Tbl.replace var_to_head_atoms (Variable.uid body_scalar)
        (List.map fst head_atoms);
      let head_results =
        List.map2
          (fun (_, Table_head_atom { table_id; table; columns }) head_scalar ->
            assert (offset_from_end <= Iarray.length columns);
            table_head_atom table_id table
              ~len:(Iarray.length columns - offset_from_end)
              columns head_scalar [] [] (Variable body_scalar) inner_columns
              result_repr)
          head_atoms head_scalars
      in
      head_results
    in
    if offset_from_end >= Iarray.length body_columns
    then cannot_introduce_copy ()
    else
      let (Index_layer (body_column, body_table, body_arg, body_scalar')) =
        Iarray.get body_columns
          (Iarray.length body_columns - offset_from_end - 1)
      in
      let Equal = Variable.must_be_equal body_scalar body_scalar' in
      match body_arg with
      | Check _ -> cannot_introduce_copy ()
      | Bind body_var -> (
        let vid = Variable.uid body_var in
        if
          not
            (List.equal Int.equal [body_atom_id]
               (try Variable.Id.Tbl.find var_to_body_atoms vid
                with Not_found -> []))
        then cannot_introduce_copy ()
        else
          let copy_one_column (type t k) (body_column : (t, k, s) Column.id)
              (body_var : k variable) =
            List.map2
              (fun (_, Table_head_atom { columns; _ })
                   (head_scalar : s variable) : t variable ->
                if offset_from_end >= Iarray.length columns
                then raise_notrace Cannot_introduce_copy;
                let (Head_column
                       (head_column, head_table, head_arg, head_scalar')) =
                  Iarray.get columns
                    (Iarray.length columns - offset_from_end - 1)
                in
                match head_arg with
                | Literal _ -> raise_notrace Cannot_introduce_copy
                | Variable head_var -> (
                  match Variable.provably_equal body_var head_var with
                  | None -> raise_notrace Cannot_introduce_copy
                  | Some Equal ->
                    let Equal =
                      Variable.must_be_equal head_scalar head_scalar'
                    in
                    let Equal =
                      Column.provably_equal_table body_column head_column
                    in
                    head_table))
              head_atoms head_scalars
          in
          match copy_one_column body_column body_var with
          | exception Cannot_introduce_copy -> cannot_introduce_copy ()
          | head_tables ->
            let truc =
              try Variable.Id.Tbl.find var_to_head_atoms vid
              with Not_found ->
                assert (List.is_empty head_atoms);
                []
            in
            let truc =
              List.filter (fun aid -> not (List.mem_assoc aid head_atoms)) truc
            in
            if List.is_empty truc
            then Variable.Id.Tbl.remove var_to_head_atoms vid
            else Variable.Id.Tbl.replace var_to_head_atoms vid truc;
            loop (offset_from_end + 1) body_table head_tables
              (body_column :: inner_columns))
  in
  loop 0 body_scalar head_scalars inner_columns

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
  let _free_vars_of_head_atoms, var_to_head_atoms =
    free_vars_atoms ~binding_times head
  in
  (* Extract existential variables: innermost variables that don't appear in the
     head. *)
  let ~vars, ~existentials =
    let vars = Iarray.of_list vars in
    let num_vars =
      let rec loop n =
        if n <= 0
        then n
        else
          let var = Iarray.get vars (n - 1) in
          let (Variable.Any var) = var in
          if Variable.Id.Tbl.mem var_to_head_atoms (Variable.uid var)
          then n
          else loop (n - 1)
      in
      loop (Iarray.length vars)
    in
    let existentials =
      Iarray.sub vars ~pos:num_vars ~len:(Iarray.length vars - num_vars)
    in
    let vars = Iarray.sub vars ~pos:0 ~len:num_vars in
    ~vars, ~existentials
  in
  let head_atoms = Iarray.map layout_head_atom head |> Iarray.to_array in
  let dependent_vars = Variable.Id.Tbl.create 0 in
  let rev_tables = ref [] in
  let body_layout =
    Iarray.mapi
      (fun bid (Atom (relation, args) as body_atom) ->
        match relation with
        | Unless _ | Distinct _ | Filter _ | Callback_with_bindings _ ->
          { table_layers = None; atom = body_atom }
        | Table tid ->
          let body_table = Variable.create (Table.Id.name tid) in
          rev_tables := Bound_table (tid, body_table) :: !rev_tables;
          let body_columns, body_scalar =
            layout_table_atom ~binding_times ~dependent_vars
              (Table.Id.columns tid) body_table args
          in
          (match innermost_arg_is_binding body_columns with
          | None -> ()
          | Some (Any arg) -> (
            match Variable.Id.Tbl.find var_to_body_atoms (Variable.uid arg) with
            | (exception Not_found) | [] | _ :: _ :: _ -> ()
            | [bid'] -> (
              assert (bid = bid');
              let head_atom_ids =
                try Variable.Id.Tbl.find var_to_head_atoms (Variable.uid arg)
                with Not_found -> []
              in
              match
                List.map
                  (fun aid ->
                    match
                      can_do_the_thing arg body_scalar
                        (Table.Id.result_repr tid) head_atoms.(aid)
                    with
                    | None -> raise_notrace Cannot_introduce_copy
                    | Some (a, b) -> (aid, a), b)
                  head_atom_ids
              with
              | exception Cannot_introduce_copy -> ()
              | table_head_atoms ->
                let table_head_atoms, head_scalars =
                  List.split table_head_atoms
                in
                let copy_head_atoms =
                  introduce_copy_into_head_atoms ~var_to_body_atoms
                    ~var_to_head_atoms ~body_atom_id:bid body_columns
                    body_scalar table_head_atoms head_scalars []
                    (Table.Id.result_repr tid)
                in
                List.iter2
                  (fun aid head_atom -> head_atoms.(aid) <- head_atom)
                  head_atom_ids copy_head_atoms)));
          (* Do not drop the columns from the body atoms: they might still
             appear in other head atoms. *)
          let table_layers =
            Table_layers
              { table = body_table;
                columns = body_columns;
                result = body_scalar;
                result_repr = Table.Id.result_repr tid;
                bound_prefix = 0
              }
          in
          { table_layers = Some table_layers; atom = body_atom })
      body
  in
  let tables = Iarray.of_list (List.rev !rev_tables) in
  (* Second round of existentials *)
  let rec does_not_occur_in_head_atoms vid =
    (not (Variable.Id.Tbl.mem var_to_head_atoms vid))
    && List.for_all does_not_occur_in_head_atoms
         (Variable.Id.Tbl.find_all dependent_vars vid)
  in
  let ~vars, ~existentials =
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
      Iarray.append
        (Iarray.sub vars ~pos:num_vars ~len:(Iarray.length vars - num_vars))
        existentials
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
  (* At this point, all the involved variables must have been bound, and all the
     input stages are fixed -- perform some safety checks. *)
  if Variable.Id.Tbl.length var_to_body_atoms <> 0
  then Misc.fatal_error "Free vars in datalog rule";
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
  let input_stages = Dynarray.to_array stages |> Iarray.of_array in
  let plan =
    { tables;
      input_stages;
      output_atoms = Iarray.of_array head_atoms;
      num_existentials = Iarray.length existentials
    }
  in
  if Flambda_features.debug_flambda2 ()
  then (
    Format.eprintf
      "================================================================================@.";
    Format.eprintf "%a@." print_rule rule;
    Format.eprintf "%a@." print_plan plan;
    Format.eprintf
      "================================================================================@.");
  plan
