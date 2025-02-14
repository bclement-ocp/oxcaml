(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Nathanaëlle Courant, Pierre Chambart, OCamlPro               *)
(*                                                                        *)
(*   Copyright 2024 OCamlPro SAS                                          *)
(*   Copyright 2024 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open! Flambda.Import
open! Rev_expr
module Float = Numeric_types.Float_by_bit_pattern
module Float32 = Numeric_types.Float32_by_bit_pattern
module RE = Rebuilt_expr
module Field = Global_flow_graph.Field

type rev_expr = Rev_expr.t

let all_slot_offsets = ref Slot_offsets.empty

let all_code = ref Code_id.Map.empty

type param_decision =
  | Keep of Variable.t * Flambda_kind.With_subkind.t
  | Delete
  | Unbox of Variable.t Dep_solver.unboxed_fields Field.Map.t

type env =
  { uses : Dep_solver.result;
    code_deps : Traverse_acc.code_dep Code_id.Map.t;
    get_code_metadata : Code_id.t -> Code_metadata.t;
    (* TODO change names *)
    cont_params_to_keep : param_decision list Continuation.Map.t;
    should_keep_param :
      Continuation.t ->
      Variable.t ->
      Flambda_kind.With_subkind.t ->
      param_decision;
    (* TODO same here *)
    function_params_to_keep : param_decision list Code_id.Map.t;
    should_keep_function_param :
      Code_id.t -> Variable.t -> Flambda_kind.With_subkind.t -> param_decision;
    function_return_decision : param_decision list Code_id.Map.t
  }

let freshen_decisions = function
  | Delete -> Delete
  | Keep (v, kind) -> Keep (Variable.rename v, kind)
  | Unbox fields -> Unbox (
      Field.Map.map (
        Dep_solver.map_unboxed_fields (fun v -> Variable.rename v))
        fields)

let is_used (env : env) cn = Dep_solver.has_use env.uses cn

let is_code_id_used (env : env) code_id =
  is_used env (Code_id_or_name.code_id code_id)
  || not (Compilation_unit.is_current (Code_id.get_compilation_unit code_id))

let is_name_used (env : env) name = is_used env (Code_id_or_name.name name)

let is_var_used (env : env) var = is_used env (Code_id_or_name.var var)

let is_symbol_used (env : env) symbol =
  is_used env (Code_id_or_name.symbol symbol)

let poison_value = 0 (* 123456789 *)

let poison kind = Simple.const_int_of_kind kind poison_value

let rewrite_simple kinds (env : env) simple =
  Simple.pattern_match simple
    ~name:(fun name ~coercion:_ ->
      assert (
        Option.is_none
          (Dep_solver.get_unboxed_fields env.uses
             (Code_id_or_name.name name)));
      if is_name_used env name
      then simple
      else
        let kind =
          match Name.Map.find_opt name kinds with
          | Some k -> k
          | None ->
            if Name.is_symbol name
            then Flambda_kind.value
            else Misc.fatal_errorf "Unbound name %a" Name.print name
        in
        poison kind)
    ~const:(fun _ -> simple)

let rewrite_simple_opt (env : env) = function
  | None -> None
  | Some simple as simpl ->
    Simple.pattern_match simple
      ~name:(fun name ~coercion:_ ->
        if is_name_used env name then simpl else None)
      ~const:(fun _ -> simpl)

let rewrite_or_variable default env (or_variable : _ Or_variable.t) =
  match or_variable with
  | Const _ -> or_variable
  | Var (v, _) ->
    if is_var_used env v then or_variable else Or_variable.Const default

let rewrite_simple_with_debuginfo kinds env (simple : Simple.With_debuginfo.t) =
  Simple.With_debuginfo.create
    (rewrite_simple kinds env (Simple.With_debuginfo.simple simple))
    (Simple.With_debuginfo.dbg simple)

let rewrite_static_const kinds (env : env) (sc : Static_const.t) =
  match sc with
  | Set_of_closures sc ->
    let function_decls = Set_of_closures.function_decls sc in
    let function_decls =
      let module FD = Function_declarations in
      FD.create
        (Function_slot.Lmap.mapi
           (fun _slot (code_id : FD.code_id_in_function_declaration) :
                FD.code_id_in_function_declaration ->
             match code_id with
             | Deleted _ -> code_id
             | Code_id code_id ->
               if is_code_id_used env code_id
               then Code_id code_id
               else
                 let code_metadata = env.get_code_metadata code_id in
                 Deleted
                   { function_slot_size =
                       Code_metadata.function_slot_size code_metadata;
                     dbg = Code_metadata.dbg code_metadata
                   })
           (FD.funs_in_order function_decls))
    in
    let set_of_closures =
      Set_of_closures.create
        ~value_slots:
          (Value_slot.Map.map (rewrite_simple kinds env)
             (Set_of_closures.value_slots sc))
        (Set_of_closures.alloc_mode sc)
        function_decls
    in
    all_slot_offsets
      := Slot_offsets.add_set_of_closures !all_slot_offsets ~is_phantom:false
           set_of_closures;
    Static_const.set_of_closures set_of_closures
  | Block (tag, mut, shape, fields) ->
    let fields = List.map (rewrite_simple_with_debuginfo kinds env) fields in
    Static_const.block tag mut shape fields
  | Boxed_float f ->
    Static_const.boxed_float (rewrite_or_variable Float.zero env f)
  | Boxed_float32 f ->
    Static_const.boxed_float32 (rewrite_or_variable Float32.zero env f)
  | Boxed_int32 n ->
    Static_const.boxed_int32 (rewrite_or_variable Int32.zero env n)
  | Boxed_int64 n ->
    Static_const.boxed_int64 (rewrite_or_variable Int64.zero env n)
  | Boxed_nativeint n ->
    Static_const.boxed_nativeint
      (rewrite_or_variable Targetint_32_64.zero env n)
  | Boxed_vec128 n ->
    Static_const.boxed_vec128
      (rewrite_or_variable Vector_types.Vec128.Bit_pattern.zero env n)
  | Immutable_float_block fields ->
    let fields = List.map (rewrite_or_variable Float.zero env) fields in
    Static_const.immutable_float_block fields
  | Immutable_float_array fields ->
    let fields = List.map (rewrite_or_variable Float.zero env) fields in
    Static_const.immutable_float_array fields
  | Immutable_float32_array fields ->
    let fields = List.map (rewrite_or_variable Float32.zero env) fields in
    Static_const.immutable_float32_array fields
  | Immutable_value_array fields ->
    let fields = List.map (rewrite_simple_with_debuginfo kinds env) fields in
    Static_const.immutable_value_array fields
  | Immutable_int32_array fields ->
    let fields = List.map (rewrite_or_variable Int32.zero env) fields in
    Static_const.immutable_int32_array fields
  | Immutable_int64_array fields ->
    let fields = List.map (rewrite_or_variable Int64.zero env) fields in
    Static_const.immutable_int64_array fields
  | Immutable_nativeint_array fields ->
    let fields =
      List.map (rewrite_or_variable Targetint_32_64.zero env) fields
    in
    Static_const.immutable_nativeint_array fields
  | Immutable_vec128_array fields ->
    let fields =
      List.map
        (rewrite_or_variable Vector_types.Vec128.Bit_pattern.zero env)
        fields
    in
    Static_const.immutable_vec128_array fields
  | Empty_array _ | Mutable_string _ | Immutable_string _ -> sc

let rewrite_static_const_or_code kinds env (sc : Static_const_or_code.t) =
  match sc with
  | Code _ -> sc
  | Deleted_code -> sc
  | Static_const sc ->
    Static_const_or_code.create_static_const (rewrite_static_const kinds env sc)

let rewrite_static_const_group kinds env (group : Static_const_group.t) =
  Static_const_group.map ~f:(rewrite_static_const_or_code kinds env) group

let rewrite_set_of_closures bound (env : env) value_slots alloc_mode
    function_decls =
  let slot_is_used slot =
    List.exists
      (fun bv ->
        Dep_solver.field_used env.uses
          (Code_id_or_name.var (Bound_var.var bv))
          slot)
      bound
  in
  let code_is_used bv =
    Dep_solver.field_used env.uses
      (Code_id_or_name.var (Bound_var.var bv))
      Code_of_closure
  in
  let value_slots =
    Value_slot.Map.filter
      (fun slot _ -> slot_is_used (Value_slot slot))
      value_slots
  in
  let open Function_declarations in
  let function_decls =
    List.map2
      (fun bound_var (slot, code_id) ->
        let code_id =
          match code_id with
          | Deleted _ -> code_id
          | Code_id code_id ->
            if code_is_used bound_var
            then Code_id code_id
            else
              let code_metadata = env.get_code_metadata code_id in
              Deleted
                { function_slot_size =
                    Code_metadata.function_slot_size code_metadata;
                  dbg = Code_metadata.dbg code_metadata
                }
        in
        slot, code_id)
      bound
      (Function_slot.Lmap.bindings
         (Function_declarations.funs_in_order function_decls))
  in
  let function_decls =
    Function_declarations.create (Function_slot.Lmap.of_list function_decls)
  in
  Set_of_closures.create ~value_slots alloc_mode function_decls

let simple_is_unboxable env simple =
  Simple.pattern_match
    ~const:(fun _ -> false)
    ~name:(fun name ~coercion:_ ->
      Option.is_some (Dep_solver.get_unboxed_fields env.uses
        (Code_id_or_name.name name)))
    simple

let get_simple_unboxable env simple =
  Simple.pattern_match
    ~const:(fun _ -> assert false)
    ~name:(fun name ~coercion:_ ->
      Option.get (Dep_solver.get_unboxed_fields env.uses
        (Code_id_or_name.name name)))
    simple

let field_kind : Field.t -> _ = function
  | Block (_, kind) -> kind
  | Value_slot vs -> Flambda_kind.With_subkind.kind (Value_slot.kind vs)
  | Function_slot _ | Is_int | Get_tag -> Flambda_kind.value
  | (Code_of_closure | Apply _) as field ->
    Misc.fatal_errorf "[field_kind] for %a" Field.print field

let rec fold_unboxed_with_kind (f : Flambda_kind.t -> 'a -> 'b -> 'b)
    (fields : 'a Dep_solver.unboxed_fields Field.Map.t) acc =
  Field.Map.fold
    (fun field elt acc ->
      match (elt : _ Dep_solver.unboxed_fields) with
      | Not_unboxed elt -> f (field_kind field) elt acc
      | Unboxed fields -> fold_unboxed_with_kind f fields acc)
    fields acc

(* This is not symmetrical!! [fields1] must define a subset of [fields2], but
   does not have to define all of them. *)
let rec fold2_unboxed_subset (f : 'a -> 'b -> 'c -> 'c)
    (fields1 : 'a Dep_solver.unboxed_fields)
    (fields2 : 'b Dep_solver.unboxed_fields) acc =
  match fields1, fields2 with
  | Not_unboxed x1, Not_unboxed x2 -> f x1 x2 acc
  | Not_unboxed _, Unboxed _ | Unboxed _, Not_unboxed _ ->
    Misc.fatal_errorf "[fold2_unboxed_subset]"
  | Unboxed fields1, Unboxed fields2 ->
    Field.Map.fold
      (fun field f1 acc ->
        let f2 = Field.Map.find field fields2 in
        fold2_unboxed_subset f f1 f2 acc)
      fields1 acc

let rec fold2_unboxed_subset_with_kind
    (f : Flambda_kind.t -> 'a -> 'b -> 'c -> 'c)
    (fields1 : 'a Dep_solver.unboxed_fields Field.Map.t)
    (fields2 : 'b Dep_solver.unboxed_fields Field.Map.t) acc =
  Field.Map.fold
    (fun field f1 acc ->
      let f2 = Field.Map.find field fields2 in
      match
        (f1, f2 : _ Dep_solver.unboxed_fields * _ Dep_solver.unboxed_fields)
      with
      | Not_unboxed x1, Not_unboxed x2 -> f (field_kind field) x1 x2 acc
      | Not_unboxed _, Unboxed _ | Unboxed _, Not_unboxed _ ->
        Misc.fatal_errorf "[fold2_unboxed_subset]"
      | Unboxed fields1, Unboxed fields2 ->
        fold2_unboxed_subset_with_kind f fields1 fields2 acc)
    fields1 acc

let get_parameters params_decisions =
  List.fold_left
    (fun acc param_decision ->
      match param_decision with
      | Delete -> acc
      | Keep (var, kind) -> Bound_parameter.create var kind :: acc
      | Unbox fields ->
        fold_unboxed_with_kind
          (fun kind v acc ->
            Bound_parameter.create v (Flambda_kind.With_subkind.anything kind)
            :: acc)
          fields acc)
    [] params_decisions
  |> List.rev

let get_args kinds env params_decisions args =
  List.fold_left2
    (fun acc arg param_decision ->
      match param_decision with
      | Delete -> acc
      | Keep _ -> rewrite_simple kinds env arg :: acc
      | Unbox fields ->
        let arg_fields = get_simple_unboxable env arg in
        fold2_unboxed_subset_with_kind
          (fun _kind _param arg_field acc -> Simple.var arg_field :: acc)
          fields arg_fields acc)
    [] args params_decisions
  |> List.rev

let get_args_with_kinds kinds env params_decisions args =
  List.fold_left2
    (fun acc arg param_decision ->
      match param_decision with
      | Delete -> acc
      | Keep (_, kind) -> (rewrite_simple kinds env arg, kind) :: acc
      | Unbox fields ->
        let arg_fields = get_simple_unboxable env arg in
        fold2_unboxed_subset_with_kind
          (fun kind _param arg_field acc ->
            (Simple.var arg_field, Flambda_kind.With_subkind.anything kind)
            :: acc)
          fields arg_fields acc)
    [] args params_decisions
  |> List.rev

let get_arity params_decisions =
  let arity =
    List.fold_left
      (fun acc param_decision ->
        match param_decision with
        | Delete -> acc
        | Keep (_, kind) -> kind :: acc
        | Unbox fields ->
          fold_unboxed_with_kind
            (fun kind _ acc -> Flambda_kind.With_subkind.anything kind :: acc)
            fields acc)
      [] params_decisions
    |> List.rev
  in
  Flambda_arity.(
    create
      [ Unboxed_product
          (List.map (fun k -> Component_for_creation.Singleton k) arity) ])

let rewrite_named kinds env (named : Named.t) =
  let[@local] rewrite_field_access arg field =
    let arg = get_simple_unboxable env arg in
    let var = Field.Map.find field arg in
    let var =
      match var with
      | Dep_solver.Not_unboxed var -> var
      | Dep_solver.Unboxed _ ->
        Misc.fatal_errorf "Trying to bind non-unboxed to unboxed"
    in
    Named.create_simple (Simple.var var)
  in
  match[@ocaml.warning "-4"] named with
  | Simple simple -> Named.create_simple (rewrite_simple kinds env simple)
  | Prim (Unary (Block_load { kind; field; _ }, arg), _dbg)
    when simple_is_unboxable env arg ->
    let kind = Flambda_primitive.Block_access_kind.element_kind_for_load kind in
    let field =
      Global_flow_graph.Field.Block (Targetint_31_63.to_int field, kind)
    in
    rewrite_field_access arg field
  | Prim (Unary (Project_value_slot { value_slot; _ }, arg), _dbg)
    when simple_is_unboxable env arg ->
    rewrite_field_access arg (Global_flow_graph.Field.Value_slot value_slot)
  | Prim (prim, dbg) ->
    let prim = Flambda_primitive.map_args (rewrite_simple kinds env) prim in
    Named.create_prim prim dbg
  | Set_of_closures s -> Named.create_set_of_closures s (* Already rewritten *)
  | Static_consts sc ->
    Named.create_static_consts (rewrite_static_const_group kinds env sc)
  | Rec_info r -> Named.create_rec_info r

let rewrite_apply_cont_expr kinds env ac =
  let cont = Apply_cont_expr.continuation ac in
  let args = Apply_cont_expr.args ac in
  let args =
    let args_to_keep = Continuation.Map.find cont env.cont_params_to_keep in
    get_args kinds env args_to_keep args
  in
  Apply_cont_expr.with_continuation_and_args ac cont ~args

type change_calling_convention =
  | Not_changing_calling_convention
  | Changing_calling_convention of Code_id.t

let rec rebuild_expr (kinds : Flambda_kind.t Name.Map.t) (env : env)
    (rev_expr : rev_expr) : RE.t =
  let { expr; holed_expr } = rev_expr in
  let expr =
    match expr with
    | Invalid { message } ->
      RE.from_expr ~expr:
        (Expr.create_invalid (Message message))
        ~free_names:Name_occurrences.empty
    | Apply_cont ac ->
      let ac = rewrite_apply_cont_expr kinds env ac in
      let expr = Expr.create_apply_cont ac in
      let free_names = Apply_cont_expr.free_names ac in
      RE.from_expr ~expr ~free_names
    | Switch switch ->
      let switch =
        Switch_expr.create
          ~condition_dbg:(Switch_expr.condition_dbg switch)
            (* Scrutinee should never need rewriting, do it anyway for
               completeness *)
          ~scrutinee:(rewrite_simple kinds env (Switch_expr.scrutinee switch))
          ~arms:
            (Targetint_31_63.Map.map
               (rewrite_apply_cont_expr kinds env)
               (Switch_expr.arms switch))
      in
      let expr = Expr.create_switch switch in
      let free_names = Switch_expr.free_names switch in
      RE.from_expr ~expr ~free_names
    | Apply apply -> (
      (* CR ncourant: we never rewrite alloc_mode. This is currently ok because
         we never remove begin- or end-region primitives, but might be needed
         later if we chose to handle them. *)
      let call_kind =
        let rewrite_simple = rewrite_simple kinds env in
        match Apply.call_kind apply with
        | Function _ as ck -> ck
        | Method { kind; obj; alloc_mode } ->
          Call_kind.method_call kind ~obj:(rewrite_simple obj) alloc_mode
        | C_call _ as ck -> ck
        | Effect (Perform { eff }) ->
          Call_kind.effect (Call_kind.Effect.perform ~eff:(rewrite_simple eff))
        | Effect (Reperform { eff; cont; last_fiber }) ->
          Call_kind.effect
            (Call_kind.Effect.reperform ~eff:(rewrite_simple eff)
               ~cont:(rewrite_simple cont)
               ~last_fiber:(rewrite_simple last_fiber))
        | Effect (Run_stack { stack; f; arg }) ->
          Call_kind.effect
            (Call_kind.Effect.run_stack ~stack:(rewrite_simple stack)
               ~f:(rewrite_simple f) ~arg:(rewrite_simple arg))
        | Effect (Resume { stack; f; arg; last_fiber }) ->
          Call_kind.effect
            (Call_kind.Effect.resume ~stack:(rewrite_simple stack)
               ~f:(rewrite_simple f) ~arg:(rewrite_simple arg)
               ~last_fiber:(rewrite_simple last_fiber))
      in
      let updating_calling_convention =
        match[@ocaml.warning "-4"] call_kind with
        | Function { function_call = Direct code_id; _ } -> (
          match Code_id.Map.find_opt code_id env.code_deps with
          | None -> Not_changing_calling_convention
          | Some code_dep ->
            let can_be_called_indirectly = Dep_solver.has_use env.uses code_dep.indirect_call_witness
            in
            if can_be_called_indirectly
            then Not_changing_calling_convention
            else Changing_calling_convention code_id)
        | _ -> Not_changing_calling_convention
      in
      let exn_continuation = Apply.exn_continuation apply in
      let exn_continuation =
        let exn_handler = Exn_continuation.exn_handler exn_continuation in
        let extra_args =
          let selected_extra_args =
            let extra_args = Exn_continuation.extra_args exn_continuation in
            (* try *)
            let args_to_keep =
              Continuation.Map.find exn_handler env.cont_params_to_keep
              |> List.tl
              (* This contains the exn argument that is not part of the extra
                 args *)
            in
            get_args_with_kinds kinds env args_to_keep (List.map fst extra_args)
            (* with Not_found -> (* Not defined in cont_params_to_keep *)
               extra_args *)
          in
          (* List.map (fun (simple, kind) -> rewrite_simple kinds env simple,
             kind) *)
          selected_extra_args
        in
        Exn_continuation.create ~exn_handler ~extra_args
      in
      let make_apply_wrapper (make_apply : continuation:Apply_expr.Result_continuation.t -> Apply_expr.t) apply_continuation return_decisions =
                  match (apply_continuation : Apply_expr.Result_continuation.t) with
          | Never_returns ->
              let apply = make_apply ~continuation:Never_returns in
              RE.from_expr ~expr:(Expr.create_apply apply) ~free_names:(Apply.free_names apply)
          | Return return_cont ->
              let return_decisions =
                List.map freshen_decisions return_decisions
              in
              let apply_decisions =
                Continuation.Map.find return_cont env.cont_params_to_keep
              in
              let return_cont_wrapper =
                Continuation.rename return_cont
              in
              let apply =
                make_apply ~continuation:(Return return_cont_wrapper)
              in
              let apply_expr = Expr.create_apply apply in
              let cont_handler =
                let return_parameters =
                  get_parameters return_decisions
                in
                let handler =
              let rev_args =
                  (* TODO if the decisions are equal, don't introduce the wrapper.
                     Not really important but this will be simpler for debugging *)
                    List.fold_left2 (fun rev_args apply_decision func_decision ->
                        match apply_decision, func_decision with
                        | Unbox _, (Keep _ | Delete) | (Keep _ | Delete), Unbox _ ->
                            assert false
                        | Delete, _ ->
                            rev_args
                        | Keep (_, _), Keep (v, _) ->
                            Simple.var v :: rev_args
                        | Keep (_, kind), Delete ->
                            poison (Flambda_kind.With_subkind.kind kind) :: rev_args
                        | Unbox fields_apply, Unbox fields_func ->
                            fold2_unboxed_subset_with_kind (fun _kind _var_apply var_func rev_args ->
                                Simple.var var_func :: rev_args
                              ) fields_apply fields_func rev_args
                      ) []
                      apply_decisions
                      return_decisions
                  in
                  let args = List.rev rev_args in
                  let apply_cont =
                    Apply_cont_expr.create return_cont ~args ~dbg:Debuginfo.none
                  in
                  RE.from_expr ~expr:(Expr.create_apply_cont apply_cont) ~free_names:(Apply_cont_expr.free_names apply_cont)
                in

                RE.create_continuation_handler
                  (Bound_parameters.create return_parameters)
                  ~handler ~is_exn_handler:false
                  ~is_cold:false (* TODO: take the one from the original return cont *)
              in
              let body = RE.from_expr ~expr:apply_expr ~free_names:(Apply.free_names apply) in
              RE.create_non_recursive_let_cont return_cont_wrapper cont_handler ~body
      in
      (* TODO rewrite return arity *)
      match updating_calling_convention with
      | Not_changing_calling_convention ->
        let args = List.map (rewrite_simple kinds env) (Apply.args apply) in
        let args_arity = Apply.args_arity apply in
        let return_arity = Apply.return_arity apply in
        let make_apply =
          Apply.create
          (* Note here that callee is rewritten with [rewrite_simple_opt], which
             will put [None] as the callee instead of a dummy value, as a dummy
             value would then be further used in a later simplify pass to refine
             the call kind and produce an invalid. *)
            ~callee:(rewrite_simple_opt env (Apply.callee apply))
            exn_continuation ~args
            ~args_arity ~return_arity ~call_kind (Apply.dbg apply)
            ~inlined:(Apply.inlined apply)
            ~inlining_state:(Apply.inlining_state apply)
            ~probe:(Apply.probe apply) ~position:(Apply.position apply)
            ~relative_history:(Apply.relative_history apply)
        in
        let func_decisions = List.map (fun kind ->
            Keep (Variable.create "function_return", kind))
            (Flambda_arity.unarized_components return_arity)
        in
        make_apply_wrapper make_apply (Apply.continuation apply) func_decisions
      | Changing_calling_convention code_id ->
        let args_from_unboxed_callee, callee =
          match Apply.callee apply with
          | Some callee when simple_is_unboxable env callee ->
            let fields = get_simple_unboxable env callee in
            let new_args =
              fold_unboxed_with_kind
                (fun kind v acc ->
                  (Simple.var v, Flambda_kind.With_subkind.anything kind) :: acc)
                fields []
            in
            new_args, None
          | (None | Some _) as callee ->
            ( [],
              (* Note here that callee is rewritten with [rewrite_simple_opt],
                 which will put [None] as the callee instead of a dummy value,
                 as a dummy value would then be further used in a later simplify
                 pass to refine the call kind and produce an invalid. *)
              rewrite_simple_opt env callee )
        in
        let params_decisions =
          match Code_id.Map.find_opt code_id env.function_params_to_keep with
          | None -> assert false
          | Some p -> p
        in
        let args =
          get_args_with_kinds kinds env params_decisions (Apply.args apply)
        in
        let args = args @ args_from_unboxed_callee in
        let args_arity =
          let components =
            List.map
              (fun (_, k) -> Flambda_arity.Component_for_creation.Singleton k)
              args
          in
          Flambda_arity.create [Unboxed_product components]
        in
        let return_decisions =
          (Code_id.Map.find code_id env.function_return_decision)
        in
        let return_arity =
          Flambda_arity.unarize_t
            (get_arity return_decisions)
        in
        let args = List.map fst args in
        let make_apply ~continuation =
          Apply.create ~callee ~continuation
            exn_continuation ~args ~args_arity ~return_arity ~call_kind
            (Apply.dbg apply) ~inlined:(Apply.inlined apply)
            ~inlining_state:(Apply.inlining_state apply)
            ~probe:(Apply.probe apply) ~position:(Apply.position apply)
            ~relative_history:(Apply.relative_history apply)
        in
        make_apply_wrapper make_apply (Apply.continuation apply) return_decisions)
  in
  rebuild_holed kinds env holed_expr expr

and rebuild_function_params_and_body (kinds : Flambda_kind.t Name.Map.t)
    (env : env) code_metadata (params_and_body : rev_params_and_body) =
  let { return_continuation;
        exn_continuation;
        params;
        body;
        my_closure;
        my_region;
        my_ghost_region;
        my_depth
      } =
    params_and_body
  in
  let code_id = Code_metadata.code_id code_metadata in
  let updating_calling_convention =
    match Code_id.Map.find_opt code_id env.code_deps with
    | None -> assert false
    | Some code_dep ->
        let can_be_called_indirectly =
          Dep_solver.has_use env.uses code_dep.indirect_call_witness
        in
        if can_be_called_indirectly
        then Not_changing_calling_convention
        else Changing_calling_convention code_id
  in
  match updating_calling_convention with
  | Not_changing_calling_convention ->
    let body = rebuild_expr kinds env body in
    ( Function_params_and_body.create ~return_continuation ~exn_continuation
        params ~body:body.expr ~free_names_of_body:(Known body.free_names)
        ~my_closure ~my_region ~my_ghost_region ~my_depth,
      code_metadata )
  | Changing_calling_convention code_id ->

    let return_decisions =
      Code_id.Map.find code_id env.function_return_decision
    in
    let params_decision =
      Code_id.Map.find code_id env.function_params_to_keep
    in
    let result_arity =
      Flambda_arity.unarize_t
        (get_arity return_decisions)
    in
    let code_metadata =
      Code_metadata.with_result_arity result_arity code_metadata
    in
    let params_decision =
      List.map2 (fun decision param ->
          match decision with
          | Delete | Unbox _ -> decision
          | Keep (_, kind) -> Keep (Bound_parameter.var param, kind)
        ) params_decision (Bound_parameters.to_list params)
    in
    let params = Bound_parameters.create (get_parameters params_decision) in
    let params_from_closure, code_metadata =
      match
        (* TODO move that in the decisions
           There should be a single record field with all the decisions
           for return params and closure
        *)
        Dep_solver.get_unboxed_fields env.uses
          (Code_id_or_name.var my_closure)
      with
      | None -> Bound_parameters.empty, code_metadata
      | Some fields ->
        (fold_unboxed_with_kind
          (fun kind v acc ->
            Bound_parameter.create v (Flambda_kind.With_subkind.anything kind)
            :: acc)
          fields [] |>
        Bound_parameters.create),
        Code_metadata.with_is_my_closure_used false code_metadata
    in
    let params = Bound_parameters.append params params_from_closure in
    let params_arity =
      let components =
        List.map (fun bp -> Flambda_arity.Component_for_creation.Singleton (Bound_parameter.kind bp))
          (Bound_parameters.to_list params)
      in
      Flambda_arity.create [Unboxed_product components]
    in
    let code_metadata =
      Code_metadata.with_is_tupled false (Code_metadata.with_params_arity params_arity code_metadata)
    in
    let body = rebuild_expr kinds env body in
    (* assert (List.exists Fun.id (Continuation.Map.find return_continuation
       env.cont_params_to_keep)); *)
    ( Function_params_and_body.create ~return_continuation ~exn_continuation
        params ~body:body.expr ~free_names_of_body:(Known body.free_names)
        ~my_closure ~my_region ~my_ghost_region ~my_depth,
      code_metadata )

and bind_fields fields arg_fields hole =
  fold2_unboxed_subset
    (fun var arg hole ->
      let bp =
        Bound_pattern.singleton (Bound_var.create var Name_mode.normal)
      in
      RE.create_let bp (Named.create_simple (Simple.var arg)) ~body:hole)
    fields arg_fields hole

and rebuild_holed (kinds : Flambda_kind.t Name.Map.t) (env : env)
    (rev_expr : rev_expr_holed) (hole : RE.t) : RE.t =
  match rev_expr with
  | Up -> hole
  | Let let_ -> (
    let[@local] erase () = rebuild_holed kinds env let_.parent hole in
    let[@local] default () =
      let subexpr =
        let bp, defining_expr =
          match let_.defining_expr with
          | Named defining_expr -> let_.bound_pattern, defining_expr
          | Static_consts group ->
            let bound_static =
              match let_.bound_pattern with
              | Static l -> l
              | Set_of_closures _ | Singleton _ ->
                (* Bound pattern is static consts, so can't bind something
                   else *)
                assert false
            in
            let bound_and_group =
              List.filter_map
                (fun ((p, e) as arg : Bound_static.Pattern.t * _) ->
                  match p with
                  | Code code_id ->
                    if is_code_id_used env code_id
                    then Some arg
                    else (
                      (match e with
                      | Code _ -> ()
                      | Deleted_code -> ()
                      | Static_const _ ->
                        (* Pattern is [Code _], so can't bind static const *)
                        assert false);
                      Some (p, Deleted_code))
                  | Block_like sym ->
                    if is_symbol_used env sym then Some arg else None
                  | Set_of_closures m ->
                    if Function_slot.Lmap.exists
                         (fun _ sym -> is_symbol_used env sym)
                         m
                    then Some arg
                    else None)
                (List.combine (Bound_static.to_list bound_static) group)
            in
            let bound_static, group = List.split bound_and_group in
            let static_const_or_code = function
              | Deleted_code -> Static_const_or_code.deleted_code
              | Code
                  { params_and_body;
                    code_metadata;
                    free_names_of_params_and_body
                  } ->
                let is_my_closure_used =
                  is_var_used env params_and_body.my_closure
                in
                let code_metadata =
                  if Bool.equal is_my_closure_used
                       (Code_metadata.is_my_closure_used code_metadata)
                  then code_metadata
                  else (
                    assert (not is_my_closure_used);
                    Code_metadata.with_is_my_closure_used is_my_closure_used
                      code_metadata)
                in
                let params_and_body, code_metadata =
                  rebuild_function_params_and_body kinds env code_metadata
                    params_and_body
                in
                let code =
                  Code.create_with_metadata ~params_and_body ~code_metadata
                    ~free_names_of_params_and_body
                in
                all_code := Code_id.Map.add (Code.code_id code) code !all_code;
                Static_const_or_code.create_code code
              | Static_const static_const ->
                Static_const_or_code.create_static_const static_const
            in
            let group =
              Static_const_group.create (List.map static_const_or_code group)
            in
            ( Bound_pattern.static (Bound_static.create bound_static),
              Named.create_static_consts group )
          | Set_of_closures { value_slots; alloc_mode; function_decls } ->
            let bound =
              match let_.bound_pattern with
              | Set_of_closures s -> s
              | Static _ | Singleton _ ->
                (* Pattern is a set of closures *)
                assert false
            in
            let set_of_closures =
              rewrite_set_of_closures bound env value_slots alloc_mode
                function_decls
            in
            let is_phantom =
              Name_mode.is_phantom @@ Bound_pattern.name_mode let_.bound_pattern
            in
            all_slot_offsets
              := Slot_offsets.add_set_of_closures !all_slot_offsets ~is_phantom
                   set_of_closures;
            let_.bound_pattern, Named.create_set_of_closures set_of_closures
        in
        begin
          match let_.bound_pattern with
          | Bound_pattern.Set_of_closures bvs
            when List.exists
                   (fun bv ->
                     Option.is_some (Dep_solver.get_unboxed_fields env.uses
                       (Code_id_or_name.var (Bound_var.var bv))))
                   bvs ->
            assert (
              List.for_all
                (fun bv ->
                     Option.is_some (Dep_solver.get_unboxed_fields env.uses
                       (Code_id_or_name.var (Bound_var.var bv))))
                bvs);
            List.fold_left
              (fun hole bv ->
                let to_bind =
                  Option.get (Dep_solver.get_unboxed_fields env.uses 
                    (Code_id_or_name.var (Bound_var.var bv)))
                in
                let value_slots =
                  match let_.defining_expr with
                  | Named (Set_of_closures _set) ->
                    (* Possible ? *)
                    assert false
                    (* Set_of_closures.value_slots set *)
                  | Set_of_closures set -> set.value_slots
                  | _ -> assert false
                in
                Field.Map.fold
                  (fun (field : Global_flow_graph.Field.t) var hole ->
                    match field with
                    | Value_slot value_slot ->
                      let arg = Value_slot.Map.find value_slot value_slots in
                      if simple_is_unboxable env arg
                      then
                        bind_fields var
                          (Dep_solver.Unboxed (get_simple_unboxable env arg))
                          hole
                      else
                        let var =
                          match var with
                          | Dep_solver.Not_unboxed var -> var
                          | Dep_solver.Unboxed _ ->
                            Misc.fatal_errorf "Trying to unbox non-unboxable"
                        in
                        let bp =
                          Bound_pattern.singleton
                            (Bound_var.create var Name_mode.normal)
                        in
                        RE.create_let bp (Named.create_simple arg) ~body:hole
                    | Block _ | Is_int | Get_tag | Function_slot _
                    | Code_of_closure | Apply _ ->
                      assert false)
                  to_bind hole)
              hole bvs
          | Bound_pattern.Singleton bv
            when Option.is_some (Dep_solver.get_unboxed_fields env.uses
                   (Code_id_or_name.var (Bound_var.var bv)))
                    -> (
            let to_bind =
              Option.get (Dep_solver.get_unboxed_fields env.uses
                (Code_id_or_name.var (Bound_var.var bv))
                )
            in
            let load_field field arg dbg =
              let oarg = arg in
              let arg =
                Simple.pattern_match arg
                  ~const:(fun _ ->
                    Misc.fatal_error "Loading unboxed from constant")
                  ~name:(fun name ~coercion:_ -> name)
              in
              let arg = Code_id_or_name.name arg in
              match
                Dep_solver.get_unboxed_fields env.uses arg
              with
              | Some arg ->
                bind_fields (Dep_solver.Unboxed to_bind)
                  (Field.Map.find field arg) hole
              | None ->
                assert (
                  Option.is_some (Dep_solver.get_changed_representation env.uses arg));
                let arg =
                  Option.get (Dep_solver.get_changed_representation env.uses arg)
                in
                match arg with
                | Block_representation (arg_fields, _size) ->
                let arg = Field.Map.find field arg_fields in
                fold2_unboxed_subset
                  (fun var (field, kind) hole ->
                    let bp =
                      Bound_pattern.singleton
                        (Bound_var.create var Name_mode.normal)
                    in
                    let named =
                        Named.create_prim
                          (Flambda_primitive.Unary
                             ( Block_load
                                 { field = Targetint_31_63.of_int field;
                                   kind;
                                   mut = Immutable
                                 },
                               oarg ))
                          dbg
                    in
                    RE.create_let bp named ~body:hole)
                  (Dep_solver.Unboxed to_bind) arg hole
                | Closure_representation (arg_fields, function_slot) ->
                let arg = Field.Map.find field arg_fields in
                fold2_unboxed_subset
                  (fun var value_slot hole ->
                    let bp =
                      Bound_pattern.singleton
                        (Bound_var.create var Name_mode.normal)
                    in
                    let named =
                          Named.create_prim
                            (Flambda_primitive.Unary (Project_value_slot { value_slot; project_from = function_slot }, oarg)) dbg
                    in
                    RE.create_let bp named ~body:hole)
                  (Dep_solver.Unboxed to_bind) arg hole
            in
            match let_.defining_expr with
            | Named named -> (
              match named with
              | Prim (Variadic (Make_block (_kind, _, _), args), _dbg) ->
                Field.Map.fold
                  (fun (field : Global_flow_graph.Field.t) var hole ->
                    let arg =
                      match field with
                      | Block (nth, _kind) ->
                        let arg = List.nth args nth in
                        if simple_is_unboxable env arg
                        then Either.Right (get_simple_unboxable env arg)
                        else Either.Left arg
                      | Is_int -> Either.Left Simple.untagged_const_false
                      | Get_tag ->
                        (* TODO *)
                        assert false
                      | Value_slot _ | Function_slot _ | Code_of_closure
                      | Apply _ ->
                        assert false
                    in
                    match arg with
                    | Either.Left simple ->
                      let var =
                        match var with
                        | Dep_solver.Not_unboxed var -> var
                        | Dep_solver.Unboxed _ ->
                          Misc.fatal_errorf "Trying to unbox non-unboxable"
                      in
                      let bp =
                        Bound_pattern.singleton
                          (Bound_var.create var Name_mode.normal)
                      in
                      RE.create_let bp (Named.create_simple simple) ~body:hole
                    | Either.Right arg_fields ->
                      bind_fields var (Dep_solver.Unboxed arg_fields) hole)
                  to_bind hole
              | Prim
                  ( Unary (Opaque_identity { middle_end_only = true; _ }, arg),
                    _dbg ) ->
                (* XXX TO REMOVE *)
                bind_fields (Dep_solver.Unboxed to_bind)
                  (Dep_solver.Unboxed (get_simple_unboxable env arg))
                  hole
              | Prim (Unary (Block_load { field; kind; _ }, arg), dbg) ->
                let field =
                  Field.Block
                    ( Targetint_31_63.to_int field,
                      Flambda_primitive.Block_access_kind.element_kind_for_load
                        kind )
                in
                load_field field arg dbg
              | Prim
                  ( Unary
                      (Project_value_slot { value_slot; project_from = _ }, arg),
                    dbg ) ->
                let field = Field.Value_slot value_slot in
                load_field field arg dbg
              | Simple arg ->
                bind_fields (Dep_solver.Unboxed to_bind)
                  (Dep_solver.Unboxed (get_simple_unboxable env arg))
                  hole
              | named ->
                (* TODO project_value_slot *)
                Format.printf "BOUM ? %a@." Named.print named;
                assert false)
            | _ -> assert false)
          | Bound_pattern.Singleton bv
            when Option.is_some (Dep_solver.get_changed_representation env.uses
                   (Code_id_or_name.var (Bound_var.var bv))
                  ) -> (
            (* TODO when this block is stored anywhere else, the subkind is no
               longer correct... we need to fix that somehow *)
            match let_.defining_expr with
            | Named
                (Prim
                  (Variadic (Make_block (_kind, _mut, alloc_mode), args), dbg))
              ->
              let fields =
                Option.get (Dep_solver.get_changed_representation env.uses
                  (Code_id_or_name.var (Bound_var.var bv)))
              in
              let fields, size = match fields with Block_representation (fields, size) -> fields, size | Closure_representation _ -> assert false in
              let mp =
                Field.Map.fold
                  (fun f uf mp ->
                    match (f : Field.t) with
                    | Block (i, _kind) -> (
                      let arg = List.nth args i in
                      if simple_is_unboxable env arg
                      then
                        fold2_unboxed_subset
                          (fun (ff, _) var mp ->
                            Numeric_types.Int.Map.add ff (Simple.var var) mp)
                          uf
                          (Dep_solver.Unboxed (get_simple_unboxable env arg))
                          mp
                      else
                        match uf with
                        | Dep_solver.Not_unboxed (ff, _) ->
                          Numeric_types.Int.Map.add ff (rewrite_simple kinds env arg) mp
                        | Dep_solver.Unboxed _ ->
                          Misc.fatal_errorf "trying to unbox simple")
                    | Get_tag -> failwith "todo"
                    | Is_int -> failwith "todo"
                    | Value_slot _ | Function_slot _ | Code_of_closure | Apply _
                      ->
                      assert false)
                  fields Numeric_types.Int.Map.empty
              in
              let args =
                List.init size (fun i ->
                    match
                      Numeric_types.Int.Map.find_opt i
                        mp
                    with
                    | None -> Simple.const_zero
                    | Some x -> x)
              in
              let named =
                Named.create_prim
                  (Flambda_primitive.Variadic
                     ( Make_block
                         ( Flambda_primitive.Block_kind.Values
                             ( Tag.Scannable.zero,
                               List.map
                                 (fun _ -> Flambda_kind.With_subkind.any_value)
                                 args ),
                           Immutable,
                           alloc_mode ),
                       args ))
                  dbg
              in
              RE.create_let bp named ~body:hole
            | _ ->
              let defining_expr = rewrite_named kinds env defining_expr in
              RE.create_let bp defining_expr ~body:hole)
          | Bound_pattern.Set_of_closures bvs
            when List.exists
                   (fun bv ->
                     Option.is_some (Dep_solver.get_changed_representation env.uses
                       (Code_id_or_name.var (Bound_var.var bv))))
                   bvs ->
            (* TODO: handle the case with more than 1 closure + merge with unbox as we can sometimes unbox some but not all *)
            assert (List.compare_length_with bvs 1 = 0);
            let bv = List.hd bvs in
            let repr = Option.get (Dep_solver.get_changed_representation env.uses (Code_id_or_name.var (Bound_var.var bv))) in
            let fields, function_slot =
              match repr with
              | Block_representation _ -> assert false
              | Closure_representation (fields, function_slot) -> fields, function_slot
            in
                let alloc_mode, value_slots, fundecls =
                  match let_.defining_expr with
                  | Named (Set_of_closures _set) ->
                    (* Possible ? *)
                    assert false
                    (* Set_of_closures.value_slots set *)
                  | Set_of_closures set -> set.alloc_mode, set.value_slots, set.function_decls
                  | _ -> assert false
                in

              let mp =
                Field.Map.fold
                  (fun f uf mp ->
                    match (f : Field.t) with
                      | Is_int | Get_tag | Block _ -> assert false
                      | Code_of_closure | Apply _ -> assert false
                      | Function_slot _ -> failwith "todo"
                      | Value_slot value_slot ->
                      let arg = Value_slot.Map.find value_slot value_slots in
                      if simple_is_unboxable env arg
                      then
                        fold2_unboxed_subset
                          (fun ff var mp ->
                            Value_slot.Map.add ff (Simple.var var) mp)
                          uf
                          (Dep_solver.Unboxed (get_simple_unboxable env arg))
                          mp
                      else
                        match uf with
                        | Dep_solver.Not_unboxed ff ->
                          Value_slot.Map.add ff (rewrite_simple kinds env arg) mp
                        | Dep_solver.Unboxed _ ->
                          Misc.fatal_errorf "trying to unbox simple")
                      
                  fields Value_slot.Map.empty
              in
          let _, code_id = Function_slot.Lmap.get_singleton_exn (Function_declarations.funs_in_order fundecls) in 
              let set_of_closures = (Set_of_closures.create alloc_mode (Function_declarations.create (Function_slot.Lmap.singleton function_slot code_id )) ~value_slots:mp) in
            all_slot_offsets
              := Slot_offsets.add_set_of_closures !all_slot_offsets ~is_phantom:false
                   set_of_closures;
              RE.create_let bp (Named.create_set_of_closures set_of_closures) ~body:hole
          | _ ->
            let defining_expr = rewrite_named kinds env defining_expr in
            RE.create_let bp defining_expr ~body:hole
        end
        [@ocaml.warning "-4"]
      in
      rebuild_holed kinds env let_.parent subexpr
    in
    match let_.bound_pattern with
    | Set_of_closures _ -> default ()
    | Static _ -> default ()
    | Singleton v ->
      let v = Bound_var.var v in
      if is_var_used env v then default () else erase ())
  | Let_cont { cont; parent; handler } ->
    let { bound_parameters = _; expr; is_exn_handler; is_cold } = handler in
    let parameters_to_keep =
      Continuation.Map.find cont env.cont_params_to_keep
    in
    let cont_handler =
      let handler = rebuild_expr kinds env expr in
      let l = get_parameters parameters_to_keep in
      let l =
        List.concat_map
          (fun param ->
            let v = Bound_parameter.var param in
            match
              Dep_solver.get_unboxed_fields env.uses (Code_id_or_name.var v)
            with
            | None -> [param]
            | Some fields ->
              fold_unboxed_with_kind
                (fun kind v acc ->
                  Bound_parameter.create v
                    (Flambda_kind.With_subkind.anything kind)
                  :: acc)
                fields [])
          l
      in
      RE.create_continuation_handler
        (Bound_parameters.create l)
        ~handler ~is_exn_handler ~is_cold
    in
    let let_cont_expr =
      RE.create_non_recursive_let_cont cont cont_handler ~body:hole
    in
    rebuild_holed kinds env parent let_cont_expr
  | Let_cont_rec { parent; handlers; invariant_params } ->
    (* TODO unboxed parameters *)
    let filter_params cont params =
      let params = Bound_parameters.to_list params in
      let params =
        get_parameters
          (List.map
             (fun param ->
               env.should_keep_param cont
                 (Bound_parameter.var param)
                 (Bound_parameter.kind param))
             params)
      in
      Bound_parameters.create params
    in
    let handlers =
      Continuation.Map.mapi
        (fun cont handler ->
          let { bound_parameters; expr; is_exn_handler; is_cold } = handler in
          let bound_parameters = filter_params cont bound_parameters in
          let handler = rebuild_expr kinds env expr in
          RE.create_continuation_handler bound_parameters ~handler
            ~is_exn_handler ~is_cold)
        handlers
    in
    let invariant_params =
      filter_params
        (fst (Continuation.Map.min_binding handlers))
        invariant_params
    in
    let let_cont_expr =
      RE.create_recursive_let_cont ~invariant_params handlers ~body:hole
    in
    rebuild_holed kinds env parent let_cont_expr

type result =
  { body : Expr.t;
    free_names : Name_occurrences.t;
    all_code : Code.t Code_id.Map.t;
    slot_offsets : Slot_offsets.t
  }

let rebuild ~(code_deps : Traverse_acc.code_dep Code_id.Map.t)
    ~(continuation_info : Traverse_acc.continuation_info Continuation.Map.t)
    ~fixed_arity_continuations kinds (solved_dep : Dep_solver.result)
    get_code_metadata holed =
  all_slot_offsets := Slot_offsets.empty;
  all_code := Code_id.Map.empty;
  let should_keep_function_param (code_dep : Traverse_acc.code_dep) =
    let can_be_called_indirectly =
      Dep_solver.has_use solved_dep code_dep.indirect_call_witness
    in
    if can_be_called_indirectly
    then ((fun var kind ->
      assert (
        Option.is_none (Dep_solver.get_unboxed_fields solved_dep (Code_id_or_name.var var)));
      Keep (var, kind)))
    else
      fun param kind ->
      match
        Dep_solver.get_unboxed_fields solved_dep
          (Code_id_or_name.var param)
      with
      | None ->
        let is_var_used =
          Dep_solver.has_use solved_dep (Code_id_or_name.var param)
        in
        if true || is_var_used then Keep (param, kind) else Delete
      | Some fields -> Unbox fields
  in
  let function_params_to_keep =
    Code_id.Map.map
      (fun (code_dep : Traverse_acc.code_dep) ->
        let kinds = Flambda_arity.unarize code_dep.arity in
        List.map2 (should_keep_function_param code_dep) code_dep.params kinds)
      code_deps
  in
  let should_keep_function_param code_id =
    match Code_id.Map.find_opt code_id code_deps with
    | None -> fun var kind -> Keep (var, kind)
    | Some code_dep -> should_keep_function_param code_dep
  in
  let function_return_decision =
    Code_id.Map.mapi
      (fun code_id (code_dep : Traverse_acc.code_dep) ->
        let can_be_called_indirectly =
          Dep_solver.has_use solved_dep code_dep.indirect_call_witness
        in
        let metadata = get_code_metadata code_id in
        let kinds =
          Flambda_arity.unarized_components
            (Code_metadata.result_arity metadata)
        in
        if can_be_called_indirectly
        then List.map2 (fun v kind -> Keep (v, kind)) code_dep.return kinds
        else (Format.eprintf "DIRECT: %a@." Code_id.print code_id; 
          List.map2
            (fun v kind ->
              match
                Dep_solver.get_unboxed_fields solved_dep (Code_id_or_name.var v)
              with
              | None ->
                let is_var_used =
                  Dep_solver.has_use solved_dep (Code_id_or_name.var v)
                in
                (* TODO: fix this, needs the mapping between code ids of functions and their return continuations *)
                if true || is_var_used then Keep (v, kind) else Delete
              | Some fields -> Unbox fields)
            code_dep.return kinds))
      code_deps
  in
  let should_keep_param cont param kind =
    let keep_all_parameters =
      Continuation.Set.mem cont fixed_arity_continuations
    in
    match
      Dep_solver.get_unboxed_fields solved_dep
        (Code_id_or_name.var param)
    with
    | None ->
      if keep_all_parameters
         ||
         let is_var_used =
           Dep_solver.has_use solved_dep (Code_id_or_name.var param)
         in
         is_var_used
         ||
         let info = Continuation.Map.find cont continuation_info in
         info.is_exn_handler && Variable.equal param (List.hd info.params)
      then Keep (param, kind)
      else Delete
    | Some fields -> Unbox fields
  in
  let cont_params_to_keep =
    Continuation.Map.mapi
      (fun cont (info : Traverse_acc.continuation_info) ->
        List.map2 (should_keep_param cont) info.params info.arity)
      continuation_info
  in
  let env =
    { uses = solved_dep;
      code_deps;
      get_code_metadata;
      cont_params_to_keep;
      should_keep_param;
      function_params_to_keep;
      should_keep_function_param;
      function_return_decision
    }
  in
  let rebuilt_expr =
    Profile.record_call ~accumulate:true "up" (fun () ->
        rebuild_expr kinds env holed)
  in
  { body = rebuilt_expr.expr;
    free_names = rebuilt_expr.free_names;
    all_code = !all_code;
    slot_offsets = !all_slot_offsets
  }
