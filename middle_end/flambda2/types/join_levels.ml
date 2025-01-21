(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module K = Flambda_kind
module MTC = More_type_creators
module TE = Typing_env
module TEE = Typing_env_extension
module TEL = Typing_env_level
module TG = Type_grammar
module Join_env_old = TE.Join_env

let mem_name env name = TE.mem ~min_name_mode:Name_mode.in_types env name

let mem_simple env simple =
  TE.mem_simple ~min_name_mode:Name_mode.in_types env simple

let get_canonical_simple_exn env simple =
  TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types env simple

let get_alias_then_canonical_simple_exn env ty =
  TE.get_alias_then_canonical_simple_exn ~min_name_mode:Name_mode.in_types env
    ty

(* Compute differential alias sets implied by a set of equations.

   This function returns a list of alias sets such that:

   - All elements in a single alias set have the same canonical element in
   [env];

   - An element in an alias set is canonical in [target_env];

   - For any names [x], [y] with the same canonical element in [env] that have
   distinct canonical elements in [target_env], they are in the same alias set.

   An equation [x : (= y)] where the right-hand side is an alias type is
   recorded when [x] was previously canonical and is demoted to [y], but [y] is
   not necessarily the current canonical.

   Each equation [x : (= y)] where the right-hand side is an alias type denotes
   a demotion of [x].

   The current canonical element is computed in [env], and the demoted elements
   are canonicalised in the [env_at_fork] as a safeguard in case equations were
   not recorded on the canonical at the time (CR bclement: it could probably be
   an assertion).

   We return alias sets that live in the target environment (they only contain
   simples that are canonical in the target environment) and no longer depend on
   their original environment. *)
let recover_delta_aliases ~env_at_fork env equations =
  Name.Map.fold
    (fun name ty demoted_elements_for_canonicals ->
      (* If [name] is not defined in the [env_at_fork], skip it. We will create
         a new variable to represent it later, if it is reachable from the
         joined types. *)
      if not (mem_name env_at_fork name)
      then demoted_elements_for_canonicals
      else
        match get_alias_then_canonical_simple_exn env ty with
        | canonical ->
          (* [name] was demoted to [canonical] *)
          let bare_canonical = Simple.without_coercion canonical in
          let coercion_from_bare_canonical = Simple.coercion canonical in
          let coercion_to_bare_canonical =
            Coercion.inverse coercion_from_bare_canonical
          in
          let demoted_to_bare_canonical =
            Simple.apply_coercion_exn (Simple.name name)
              coercion_to_bare_canonical
          in
          (* This would mean that we have recorded an equation [x: (= y)] where
             the current canonical for [y] is equal to [x], which is not
             possible since [x] was demoted. *)
          assert (not (Simple.equal bare_canonical demoted_to_bare_canonical));
          Simple.Map.update bare_canonical
            (function
              | None ->
                let alias_set =
                  Aliases.Alias_set.singleton demoted_to_bare_canonical
                in
                if mem_simple env_at_fork bare_canonical
                then Some (Aliases.Alias_set.add bare_canonical alias_set)
                else Some alias_set
              | Some alias_set ->
                Some (Aliases.Alias_set.add demoted_to_bare_canonical alias_set))
            demoted_elements_for_canonicals
        | exception Not_found ->
          (* not an alias *) demoted_elements_for_canonicals)
    equations Simple.Map.empty

let join_aliases ~env_at_fork env_with_levels =
  match env_with_levels with
  | [] -> env_at_fork, []
  | (env_at_first_use, level_at_first_use) :: other_envs_with_levels ->
    let delta_aliases =
      recover_delta_aliases ~env_at_fork env_at_first_use
        (TEL.equations level_at_first_use)
    in
    let delta_aliases =
      Simple.Map.fold
        (fun _ alias_set delta_aliases -> alias_set :: delta_aliases)
        delta_aliases []
    in
    let joined_aliases =
      List.fold_left
        (fun delta_aliases (env_at_other_use, _) ->
          List.fold_left
            (fun new_classes delta_alias_set ->
              (* Partition each equivalence class according to the canonical
                 elements in [env_at_other_use]. *)
              let canonical_delta_alias_set_at_other_use =
                Aliases.Alias_set.fold
                  (fun alias canonical_delta_alias_set_at_other_use ->
                    let canonical_alias_at_other_use =
                      get_canonical_simple_exn env_at_other_use alias
                    in
                    Simple.Map.update canonical_alias_at_other_use
                      (function
                        | None -> Some (Aliases.Alias_set.singleton alias)
                        | Some aliases ->
                          Some (Aliases.Alias_set.add alias aliases))
                      canonical_delta_alias_set_at_other_use)
                  delta_alias_set Simple.Map.empty
              in
              Simple.Map.fold
                (fun _canonical alias_set new_classes ->
                  assert (not (Aliases.Alias_set.is_empty alias_set));
                  match Aliases.Alias_set.get_singleton alias_set with
                  | Some _ -> new_classes
                  | None -> alias_set :: new_classes)
                canonical_delta_alias_set_at_other_use new_classes)
            [] delta_aliases)
        delta_aliases other_envs_with_levels
    in
    let base_env =
      List.fold_left
        (fun base_env alias_set ->
          Aliases.Alias_set.fold_equations
            (fun name simple base_env ->
              let base_ty = TE.find base_env name None in
              let alias_ty = TG.alias_type_of (TG.kind base_ty) simple in
              TE.add_equation base_env name alias_ty
                ~meet_type:(Meet_and_join.meet_type ()))
            alias_set base_env)
        env_at_fork joined_aliases
    in
    base_env, joined_aliases

let join_types ~env_at_fork envs_with_levels =
  (* Recover shared aliases *)
  let fork_scope = TE.current_scope env_at_fork in
  let env_at_fork = TE.increment_scope env_at_fork in
  let base_env, _joined_aliases = join_aliases ~env_at_fork envs_with_levels in
  (* Aggregate the code age relations of the branches. *)
  let base_env, envs_with_equations =
    List.fold_left_map
      (fun base_env (env_at_use, level) ->
        let equations = TEL.equations level in
        let delta_aliases =
          recover_delta_aliases ~env_at_fork:base_env env_at_use equations
        in
        let equations =
          Name.Map.fold
            (fun name ty equations ->
              match TG.get_alias_exn ty with
              | _ ->
                (* We have already computed the shared aliases; we can drop them
                   from the types. *)
                equations
              | exception Not_found -> (
                (* Need to move the type to the canonicals! *)
                let canonical_at_use =
                  TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types
                    env_at_use (Simple.name name)
                in
                let bare_canonical_at_use =
                  Simple.without_coercion canonical_at_use
                in
                let coercion_to_canonical_at_use =
                  Simple.coercion canonical_at_use
                in
                match Simple.Map.find bare_canonical_at_use delta_aliases with
                | exception Not_found ->
                  if TE.mem ~min_name_mode:Name_mode.in_types base_env name
                  then Name.Map.add name ty equations
                  else equations
                | canonicals_at_fork ->
                  let ty_for_canonicals_at_fork =
                    TG.apply_coercion ty
                      (Coercion.inverse coercion_to_canonical_at_use)
                  in
                  Aliases.Alias_set.fold
                    (fun canonical_at_fork equations ->
                      Simple.pattern_match canonical_at_fork
                        ~name:
                          (fun canonical_name_at_fork
                               ~coercion:coercion_to_canonical_at_fork ->
                          let ty_for_canonical_name_at_fork =
                            TG.apply_coercion ty_for_canonicals_at_fork
                              (Coercion.inverse coercion_to_canonical_at_fork)
                          in
                          Name.Map.add canonical_name_at_fork
                            ty_for_canonical_name_at_fork equations)
                        ~const:(fun _ -> equations))
                    canonicals_at_fork equations))
            equations Name.Map.empty
        in
        let _ = TE.add_env_extension_with_extra_variables in
        let code_age_relation =
          Code_age_relation.union
            (TE.code_age_relation base_env)
            (TE.code_age_relation env_at_use)
        in
        ( TE.with_code_age_relation base_env code_age_relation,
          (env_at_use, equations) ))
      base_env envs_with_levels
  in
  (* *)
  let shared_names =
    match envs_with_equations with
    | [] -> assert false
    | (_, first_extension) :: envs_with_equations ->
      List.fold_left
        (fun shared_names (_, extension) ->
          Name.Set.inter shared_names (Name.Map.keys extension))
        (Name.Map.keys first_extension)
        envs_with_equations
  in
  let initial_types =
    Name.Set.fold
      (fun name initial_types ->
        if TE.mem ~min_name_mode:Name_mode.in_types env_at_fork name
        then
          Name.Map.add name
            (MTC.bottom_like (TE.find base_env name None))
            initial_types
        else initial_types)
      shared_names Name.Map.empty
  in
  let joined_types, new_variables =
    (* Now fold over the levels doing the actual join operation on equations. *)
    ListLabels.fold_left envs_with_equations
      ~init:(initial_types, Variable.Set.empty)
      ~f:(fun (joined_types, _new_variables) (env_at_use, equations) ->
        let base_env =
          Name.Map.fold
            (fun name ty base_env ->
              if not (TE.mem ~min_name_mode:Name_mode.in_types base_env name)
              then
                TE.add_definition base_env
                  (Bound_name.create name Name_mode.in_types)
                  (TG.kind ty)
              else base_env)
            joined_types base_env
        in
        let left_env =
          (* CR vlaviron: This is very likely quadratic (number of uses times
             number of variables in all uses). However it's hard to know how we
             could do better. *)
          TE.add_env_extension_maybe_bottom base_env
            (TEE.from_map joined_types)
            ~meet_type:(Meet_and_join.meet_type ())
        in
        let join_env =
          Join_env_old.create base_env ~left_env ~right_env:env_at_use
        in
        let rec loop join_env to_join joined_types =
          match Name.Map.choose to_join with
          | exception Not_found ->
            let to_join, join_env = Join_env_old.at_next_depth join_env in
            if Name.Map.is_empty to_join
            then joined_types
            else loop join_env to_join joined_types
          | name, (left_ty, right_ty) -> (
            let to_join = Name.Map.remove name to_join in
            if Flambda_features.debug_flambda2 ()
            then
              Format.eprintf "%a = join(%a, %a)@." Name.print name TG.print
                left_ty TG.print right_ty;
            match
              (Meet_and_join.join ()) ~bound_name:name join_env left_ty right_ty
            with
            | Unknown ->
              if Flambda_features.debug_flambda2 () then Format.eprintf "unk@.";
              let joined_types =
                Name.Map.add name (MTC.unknown (TG.kind left_ty)) joined_types
              in
              loop join_env to_join joined_types
            | Known ty ->
              if Flambda_features.debug_flambda2 ()
              then Format.eprintf "= %a@." TG.print (TG.recover_some_aliases ty);
              let joined_types =
                Name.Map.add name (TG.recover_some_aliases ty) joined_types
              in
              loop join_env to_join joined_types)
        in
        let to_join =
          Name.Map.merge
            (fun _name joined_ty use_ty ->
              match joined_ty, use_ty with
              | None, None -> assert false
              | Some joined_ty, None ->
                Some (joined_ty, MTC.unknown_like joined_ty)
              | None, Some use_ty -> Some (MTC.unknown_like use_ty, use_ty)
              | Some joined_ty, Some use_ty -> Some (joined_ty, use_ty))
            joined_types equations
        in
        let joined_types = loop join_env to_join Name.Map.empty in
        let new_variables =
          Join_env_old.fold_variables Variable.Set.add join_env
            Variable.Set.empty
        in
        joined_types, new_variables)
  in
  (let nlevels = List.length envs_with_levels in
   if nlevels > 1
   then
     let () =
       if Flambda_features.debug_flambda2 ()
       then
         Format.eprintf "Aliases: @[<v>%a@]@."
           (Format.pp_print_list Aliases.Alias_set.print)
           _joined_aliases
     in
     if Flambda_features.debug_flambda2 ()
     then
       Format.eprintf
         "@[<v>Base env:@;\
          <1 2>@[<v>%a@]@ Join %d levels:@;\
          <1 2>@[<v>%a@]@ Outcome:@;\
          <1 2>@[<v>%a@]@]@." TE.print env_at_fork nlevels
         (Format.pp_print_list (fun ppf (_, level) -> TEL.print ppf level))
         envs_with_levels TEE.print
         (TEE.from_map joined_types));
  let new_variables =
    Name.Map.fold
      (fun name ty new_variables ->
        let new_variables =
          match Name.must_be_var_opt name with
          | Some var -> Variable.Set.add var new_variables
          | None -> new_variables
        in
        let names = TG.free_names ty in
        Name_occurrences.fold_variables names ~init:new_variables
          ~f:(fun vs v -> Variable.Set.add v vs))
      joined_types new_variables
  in
  let final_env =
    Variable.Set.fold
      (fun var final_env ->
        if TE.mem ~min_name_mode:Name_mode.in_types final_env (Name.var var)
        then final_env
        else
          let kind =
            match Name.Map.find (Name.var var) joined_types with
            | ty -> TG.kind ty
            | exception Not_found ->
              Misc.fatal_errorf "Could not find variable: %a@." Variable.print
                var
          in
          TE.add_definition final_env
            (Bound_name.create (Name.var var) Name_mode.in_types)
            kind)
      new_variables base_env
  in
  let final_env =
    TE.add_env_extension final_env
      (TEE.from_map joined_types)
      ~meet_type:(Meet_and_join.meet_type ())
  in
  let final_level = TE.cut final_env ~cut_after:fork_scope in
  (* Make sure we include the shared aliases in the joined extension! *)
  joined_types, final_level

let construct_joined_level envs_with_levels ~env_at_fork ~allowed ~joined_types
    ~params =
  let allowed_and_new =
    (* Parameters are already in the resulting environment *)
    List.fold_left
      (fun allowed_and_new param ->
        Name_occurrences.remove_var allowed_and_new
          ~var:(Bound_parameter.var param))
      allowed params
  in
  let variable_is_in_new_level var =
    Name_occurrences.mem_var allowed_and_new var
  in
  let defined_vars, binding_times =
    List.fold_left
      (fun (defined_vars, binding_times) (_env_at_use, t) ->
        let defined_vars_this_level =
          Variable.Map.filter
            (fun var _ -> variable_is_in_new_level var)
            (TEL.defined_variables_with_kinds t)
        in
        let defined_vars =
          Variable.Map.union
            (fun var kind1 kind2 ->
              if K.equal kind1 kind2
              then Some kind1
              else
                Misc.fatal_errorf
                  "Cannot join levels that disagree on the kind of \
                   [defined_vars] (%a and %a for %a)"
                  K.print kind1 K.print kind2 Variable.print var)
            defined_vars defined_vars_this_level
        in
        let binding_times_this_level =
          Binding_time.Map.filter_map
            (fun _ vars ->
              let vars = Variable.Set.filter variable_is_in_new_level vars in
              if Variable.Set.is_empty vars then None else Some vars)
            (TEL.variables_by_binding_time t)
        in
        let binding_times =
          Binding_time.Map.union
            (fun _bt vars1 vars2 -> Some (Variable.Set.union vars1 vars2))
            binding_times binding_times_this_level
        in
        defined_vars, binding_times)
      (Variable.Map.empty, Binding_time.Map.empty)
      envs_with_levels
  in
  let equations =
    Name.Map.filter
      (fun name _ty -> Name_occurrences.mem_name allowed name)
      joined_types
  in
  let symbol_projections =
    List.fold_left
      (fun symbol_projections (_env_at_use, t) ->
        let projs_this_level =
          Variable.Map.filter
            (fun var _ ->
              let name = Name.var var in
              TE.mem ~min_name_mode:Name_mode.normal env_at_fork name
              || Name_occurrences.mem_name allowed name)
            (TEL.symbol_projections t)
        in
        Variable.Map.union
          (fun _var proj1 proj2 ->
            if Symbol_projection.equal proj1 proj2 then Some proj1 else None)
          symbol_projections projs_this_level)
      Variable.Map.empty envs_with_levels
  in
  TEL.create ~defined_vars ~binding_times ~equations ~symbol_projections

let check_join_inputs ~env_at_fork _envs_with_levels ~params
    ~extra_lifted_consts_in_use_envs =
  (* It might seem as if every name defined in [env_at_fork], with the exception
     of the lifted constant symbols, should occur in every use environment.
     However this is not the case: the introduction of the lifted constants into
     [env_at_fork] in [Simplify_expr] may have produced [In_types] variables
     (from [make_suitable_for_environment]) that will not be present in any use
     environment. *)
  List.iter
    (fun param ->
      if not (TE.mem env_at_fork (Bound_parameter.name param))
      then
        Misc.fatal_errorf "Parameter %a not defined in [env_at_fork] at join"
          Bound_parameter.print param)
    params;
  Symbol.Set.iter
    (fun symbol ->
      if not (TE.mem env_at_fork (Name.symbol symbol))
      then
        Misc.fatal_errorf
          "Symbol %a, which is a new lifted constant that arose during the \
           simplification of the continuation's body, is not defined in the \
           [env_at_fork] when calling [join]"
          Symbol.print symbol)
    extra_lifted_consts_in_use_envs

let join ~env_at_fork envs_with_levels ~params ~extra_lifted_consts_in_use_envs
    ~extra_allowed_names:allowed =
  check_join_inputs ~env_at_fork envs_with_levels ~params
    ~extra_lifted_consts_in_use_envs;
  (* Calculate the joined types of all the names involved. *)
  let joined_types, joined_level = join_types ~env_at_fork envs_with_levels in
  if true
  then joined_level
  else
    (* Next calculate which equations (describing joined types) to propagate to
       the join point. (Recall that the environment at the fork point includes
       the parameters of the continuation being called at the join. We wish to
       ensure that information in the types of these parameters is not lost.)

       - Equations on names defined in the environment at the fork point are
       always propagated.

       - Definitions of, and equations on, names that occur free on the
       right-hand sides of the propagated equations are also themselves
       propagated. The definition of any such propagated name (i.e. one that
       does not occur in the environment at the fork point) will be made
       existential. *)
    let free_names_transitive typ =
      (* We need to compute the free names of joined_types, but we can't use a
         typing environment. *)
      let rec free_names_transitive0 typ ~result =
        let free_names = TG.free_names typ in
        let to_traverse = Name_occurrences.diff free_names ~without:result in
        Name_occurrences.fold_names to_traverse ~init:result
          ~f:(fun result name ->
            let result =
              Name_occurrences.add_name result name Name_mode.in_types
            in
            match Name.Map.find name joined_types with
            | exception Not_found -> result
            | typ -> free_names_transitive0 typ ~result)
      in
      free_names_transitive0 typ ~result:Name_occurrences.empty
    in
    let allowed =
      Name.Map.fold
        (fun name ty allowed ->
          if TE.mem env_at_fork name || Name.is_symbol name
          then
            Name_occurrences.add_name
              (Name_occurrences.union allowed (free_names_transitive ty))
              name Name_mode.in_types
          else allowed)
        joined_types allowed
    in
    let allowed =
      Symbol.Set.fold
        (fun symbol allowed ->
          Name_occurrences.add_symbol allowed symbol Name_mode.in_types)
        extra_lifted_consts_in_use_envs allowed
    in
    (* Having calculated which equations to propagate, the resulting level can
       now be constructed. *)
    construct_joined_level envs_with_levels ~env_at_fork ~allowed ~joined_types
      ~params

let n_way_join ~env_at_fork envs_with_levels ~params
    ~extra_lifted_consts_in_use_envs ~extra_allowed_names =
  match envs_with_levels with
  | [] -> TEL.empty
  | envs_with_levels ->
    join ~env_at_fork envs_with_levels ~params ~extra_lifted_consts_in_use_envs
      ~extra_allowed_names

let cut_and_n_way_join definition_typing_env ts_and_use_ids ~params:_ ~cut_after
    ~extra_lifted_consts_in_use_envs:_ ~extra_allowed_names:_ =
  if false then Format.eprintf "wut?@.";
  let ts_and_use_ids = List.rev ts_and_use_ids in
  let central_env = definition_typing_env in
  let joined_envs =
    List.map
      (fun (t, _use_id, _use_kind) ->
        let level = TE.cut t ~cut_after in
        t, level)
      ts_and_use_ids
  in
  (* let _ = *)
  try
    Join_env.Superjoin.dodoblahdo
      ~meet_type:(Meet_and_join.meet_type ())
      ~join_ty:(Meet_and_join_new.join ?bound_name:None)
      central_env joined_envs
  with Stack_overflow ->
    let bt = Printexc.get_raw_backtrace () in
    Format.eprintf "@[<v>join in:@ @[<v>%a@]@." TE.print central_env;
    Format.eprintf "@[<v>%a@]@."
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ --------------------@ ")
         (fun ppf (_, tel) -> Format.fprintf ppf "@[<v>%a@]" TEL.print tel))
      joined_envs;
    Printexc.raise_with_backtrace Stack_overflow bt
(* in let params = Bound_parameters.to_list params in let level = n_way_join
   ~env_at_fork:definition_typing_env after_cuts ~params
   ~extra_lifted_consts_in_use_envs ~extra_allowed_names in
   TE.add_env_extension_from_level definition_typing_env level
   ~meet_type:(Meet_and_join.meet_type ()) *)

let () = ignore n_way_join

let () = ignore cut_and_n_way_join

module Equal_types = struct
  type env =
    { left_env : TE.t;
      right_env : TE.t;
      left_renaming : Renaming.t
    }

  let equal_row_like_index_domain ~equal_lattice
      (t1 : _ TG.row_like_index_domain) (t2 : _ TG.row_like_index_domain) =
    match t1, t2 with
    | Known t1, Known t2 -> equal_lattice t1 t2
    | Known _, At_least _ | At_least _, Known _ -> false
    | At_least t1, At_least t2 -> equal_lattice t1 t2

  let equal_row_like_index ~equal_lattice ~equal_shape
      (t1 : (_, _) TG.row_like_index) (t2 : (_, _) TG.row_like_index) =
    equal_row_like_index_domain ~equal_lattice t1.domain t2.domain
    && equal_shape t1.shape t2.shape

  let equal_env_extension ~equal_type env (ext1 : TG.env_extension)
      (ext2 : TG.env_extension) =
    let shared_names =
      Name.Map.merge
        (fun name ty1 ty2 ->
          match ty1, ty2 with
          | None, None -> None
          | Some ty1, Some _ -> Some (TG.kind ty1)
          | Some ty1, None ->
            if mem_name env.right_env name then Some (TG.kind ty1) else None
          | None, Some ty2 ->
            if mem_name env.left_env name then Some (TG.kind ty2) else None)
        (TEE.to_map ext1) (TEE.to_map ext2)
    in
    let left_env =
      TE.add_env_extension env.left_env ext1
        ~meet_type:(Meet_and_join.meet_type ())
    in
    let right_env =
      TE.add_env_extension env.left_env ext1
        ~meet_type:(Meet_and_join.meet_type ())
    in
    let env = { env with left_env; right_env } in
    Name.Map.for_all
      (fun name kind ->
        let left_canonical =
          TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types
            env.left_env (Simple.name name)
        in
        let left_ty =
          Simple.pattern_match left_canonical
            ~const:(fun _ -> TG.alias_type_of kind left_canonical)
            ~name:(fun name ~coercion ->
              TG.apply_coercion (TE.find env.left_env name (Some kind)) coercion)
        in
        let right_canonical =
          TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types
            env.right_env (Simple.name name)
        in
        let right_ty =
          Simple.pattern_match right_canonical
            ~const:(fun _ -> TG.alias_type_of kind right_canonical)
            ~name:(fun name ~coercion ->
              TG.apply_coercion
                (TE.find env.right_env name (Some kind))
                coercion)
        in
        let is_equal = equal_type env left_ty right_ty in
        if (not is_equal) && Flambda_features.debug_flambda2 ()
        then Format.eprintf "NOT equal: %a@." Name.print name;
        is_equal)
      shared_names

  let equal_row_like_case ~equal_type ~equal_maps_to ~equal_lattice ~equal_shape
      env (t1 : (_, _, _) TG.row_like_case) (t2 : (_, _, _) TG.row_like_case) =
    match
      ( TE.add_env_extension_strict env.left_env t1.env_extension
          ~meet_type:(Meet_and_join.meet_type ()),
        TE.add_env_extension_strict env.right_env t2.env_extension
          ~meet_type:(Meet_and_join.meet_type ()) )
    with
    | Or_bottom.Bottom, Or_bottom.Bottom -> true
    | Or_bottom.Ok _, Or_bottom.Bottom | Or_bottom.Bottom, Or_bottom.Ok _ ->
      false
    | Or_bottom.Ok left_env, Or_bottom.Ok right_env ->
      let both_env = { env with left_env; right_env } in
      let left_env = { env with left_env } in
      let right_env = { env with right_env } in
      equal_row_like_index ~equal_lattice ~equal_shape t1.index t2.index
      && equal_maps_to left_env t1.maps_to t2.maps_to
      && equal_maps_to right_env t1.maps_to t2.maps_to
      && equal_env_extension ~equal_type both_env t1.env_extension
           t2.env_extension

  let equal_array eq a1 a2 =
    Array.length a1 = Array.length a2 && Array.for_all2 eq a1 a2

  let equal_row_like_block_case ~equal_type env (t1 : TG.row_like_block_case)
      (t2 : TG.row_like_block_case) =
    equal_row_like_case ~equal_type ~equal_lattice:TG.Block_size.equal
      ~equal_shape:Flambda_kind.Block_shape.equal
      ~equal_maps_to:(fun env -> equal_array (equal_type env))
      env t1 t2

  let equal_row_like_for_blocks ~equal_type env (t1 : TG.row_like_for_blocks)
      (t2 : TG.row_like_for_blocks) =
    Tag.Map.equal
      (Or_unknown.equal (equal_row_like_block_case ~equal_type env))
      t1.known_tags t2.known_tags
    && (match t1.other_tags, t2.other_tags with
       | Bottom, Bottom -> true
       | Bottom, Ok _ | Ok _, Bottom -> false
       | Ok t1, Ok t2 -> equal_row_like_block_case ~equal_type env t1 t2)
    && Alloc_mode.For_types.equal t1.alloc_mode t2.alloc_mode

  let equal_function_slot_indexed_product ~equal_type env
      (t1 : TG.function_slot_indexed_product)
      (t2 : TG.function_slot_indexed_product) =
    Function_slot.Map.equal (equal_type env)
      t1.function_slot_components_by_index t2.function_slot_components_by_index

  let equal_value_slot_indexed_product ~equal_type env
      (t1 : TG.value_slot_indexed_product) (t2 : TG.value_slot_indexed_product)
      =
    Value_slot.Map.equal (equal_type env) t1.value_slot_components_by_index
      t2.value_slot_components_by_index

  let equal_function_type ~equal_type env (t1 : TG.function_type)
      (t2 : TG.function_type) =
    Code_id.equal t1.code_id t2.code_id
    && equal_type env t1.rec_info t2.rec_info

  let equal_closures_entry ~equal_type env (t1 : TG.closures_entry)
      (t2 : TG.closures_entry) =
    Function_slot.Map.equal
      (Or_unknown_or_bottom.equal (equal_function_type ~equal_type env))
      t1.function_types t2.function_types
    && equal_function_slot_indexed_product ~equal_type env t1.closure_types
         t2.closure_types
    && equal_value_slot_indexed_product ~equal_type env t1.value_slot_types
         t2.value_slot_types

  let equal_row_like_for_closures ~equal_type env
      (t1 : TG.row_like_for_closures) (t2 : TG.row_like_for_closures) =
    let equal_row_like_case =
      equal_row_like_case ~equal_type env
        ~equal_lattice:Set_of_closures_contents.equal
        ~equal_shape:(fun () () -> true)
        ~equal_maps_to:(equal_closures_entry ~equal_type)
    in
    Function_slot.Map.equal equal_row_like_case t1.known_closures
      t2.known_closures
    &&
    match t1.other_closures, t2.other_closures with
    | Bottom, Bottom -> true
    | Bottom, Ok _ | Ok _, Bottom -> false
    | Ok case1, Ok case2 -> equal_row_like_case case1 case2

  let equal_array_contents ~equal_type env (t1 : TG.array_contents)
      (t2 : TG.array_contents) =
    match t1, t2 with
    | Mutable, Mutable -> true
    | Mutable, Immutable _ | Immutable _, Mutable -> false
    | Immutable { fields = f1 }, Immutable { fields = f2 } ->
      equal_array (equal_type env) f1 f2

  let add_extension env left_extension right_extension =
    let left_env =
      TE.add_env_extension_strict env.left_env left_extension
        ~meet_type:(Meet_and_join.meet_type ())
    in
    let right_env =
      TE.add_env_extension_strict env.right_env right_extension
        ~meet_type:(Meet_and_join.meet_type ())
    in
    match left_env, right_env with
    | Bottom, Bottom -> Some Or_bottom.Bottom
    | Bottom, Ok _ | Ok _, Bottom -> None
    | Ok left_env, Ok right_env ->
      Some (Or_bottom.Ok { env with left_env; right_env })

  let equal_head_of_kind_value_non_null ~equal_type env
      (t1 : TG.head_of_kind_value_non_null)
      (t2 : TG.head_of_kind_value_non_null) =
    match[@warning "-fragile-match"] t1, t2 with
    | Variant t1, Variant t2 -> (
      Bool.equal t1.is_unique t2.is_unique
      &&
      let envs_immediate, envs_block =
        match t1.extensions, t2.extensions with
        | No_extensions, No_extensions ->
          Some (Or_bottom.Ok env), Some (Or_bottom.Ok env)
        | Ext { when_immediate; when_block }, No_extensions ->
          ( add_extension env when_immediate TEE.empty,
            add_extension env when_block TEE.empty )
        | No_extensions, Ext { when_immediate; when_block } ->
          ( add_extension env TEE.empty when_immediate,
            add_extension env TEE.empty when_block )
        | ( Ext { when_immediate = when_immediate1; when_block = when_block1 },
            Ext { when_immediate = when_immediate2; when_block = when_block2 } )
          ->
          ( add_extension env when_immediate1 when_immediate2,
            add_extension env when_block1 when_block2 )
      in
      match envs_immediate, envs_block with
      | None, _ | _, None -> false
      | Some env_immediate, Some env_blocks -> (
        (match env_immediate with
        | Bottom -> true
        | Ok env_immediate ->
          Or_unknown.equal (equal_type env_immediate) t1.immediates
            t2.immediates)
        &&
        match env_blocks with
        | Bottom -> true
        | Ok env_blocks ->
          Or_unknown.equal
            (equal_row_like_for_blocks ~equal_type env_blocks)
            t1.blocks t2.blocks))
    | Mutable_block t1, Mutable_block t2 ->
      Alloc_mode.For_types.equal t1.alloc_mode t2.alloc_mode
    | Boxed_float32 (t1, a1), Boxed_float32 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_float (t1, a1), Boxed_float (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_int32 (t1, a1), Boxed_int32 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_int64 (t1, a1), Boxed_int64 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_nativeint (t1, a1), Boxed_nativeint (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_vec128 (t1, a1), Boxed_vec128 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Closures c1, Closures c2 ->
      equal_row_like_for_closures ~equal_type env c1.by_function_slot
        c2.by_function_slot
      && Alloc_mode.For_types.equal c1.alloc_mode c2.alloc_mode
    | String t1, String t2 -> String_info.Set.equal t1 t2
    | Array t1, Array t2 ->
      Or_unknown_or_bottom.equal Flambda_kind.With_subkind.equal t1.element_kind
        t2.element_kind
      && equal_type env t1.length t2.length
      && Or_unknown.equal
           (equal_array_contents ~equal_type env)
           t1.contents t2.contents
      && Alloc_mode.For_types.equal t1.alloc_mode t2.alloc_mode
    | _, _ -> false

  let equal_head_of_kind_value ~equal_type env (t1 : TG.head_of_kind_value)
      (t2 : TG.head_of_kind_value) =
    match t1.is_null, t2.is_null with
    | Not_null, Maybe_null | Maybe_null, Not_null -> false
    | Not_null, Not_null | Maybe_null, Maybe_null ->
      Or_unknown_or_bottom.equal
        (equal_head_of_kind_value_non_null ~equal_type env)
        t1.non_null t2.non_null

  let equal_head_of_kind_naked_immediate ~equal_type env
      (t1 : TG.head_of_kind_naked_immediate)
      (t2 : TG.head_of_kind_naked_immediate) =
    match t1, t2 with
    | Naked_immediates is1, Naked_immediates is2 ->
      Targetint_31_63.Set.equal is1 is2
    | Is_int t1, Is_int t2 -> equal_type env t1 t2
    | Get_tag t1, Get_tag t2 -> equal_type env t1 t2
    | Is_null t1, Is_null t2 -> equal_type env t1 t2
    | ( (Naked_immediates _ | Is_int _ | Get_tag _ | Is_null _),
        (Naked_immediates _ | Is_int _ | Get_tag _ | Is_null _) ) ->
      false

  let equal_head_of_kind_naked_float32 (t1 : TG.head_of_kind_naked_float32)
      (t2 : TG.head_of_kind_naked_float32) =
    Numeric_types.Float32_by_bit_pattern.Set.equal
      (t1 :> Numeric_types.Float32_by_bit_pattern.Set.t)
      (t2 :> Numeric_types.Float32_by_bit_pattern.Set.t)

  let equal_head_of_kind_naked_float (t1 : TG.head_of_kind_naked_float)
      (t2 : TG.head_of_kind_naked_float) =
    Numeric_types.Float_by_bit_pattern.Set.equal
      (t1 :> Numeric_types.Float_by_bit_pattern.Set.t)
      (t2 :> Numeric_types.Float_by_bit_pattern.Set.t)

  let equal_head_of_kind_naked_int32 (t1 : TG.head_of_kind_naked_int32)
      (t2 : TG.head_of_kind_naked_int32) =
    Numeric_types.Int32.Set.equal
      (t1 :> Numeric_types.Int32.Set.t)
      (t2 :> Numeric_types.Int32.Set.t)

  let equal_head_of_kind_naked_int64 (t1 : TG.head_of_kind_naked_int64)
      (t2 : TG.head_of_kind_naked_int64) =
    Numeric_types.Int64.Set.equal
      (t1 :> Numeric_types.Int64.Set.t)
      (t2 :> Numeric_types.Int64.Set.t)

  let equal_head_of_kind_naked_nativeint (t1 : TG.head_of_kind_naked_nativeint)
      (t2 : TG.head_of_kind_naked_nativeint) =
    Targetint_32_64.Set.equal
      (t1 :> Targetint_32_64.Set.t)
      (t2 :> Targetint_32_64.Set.t)

  let equal_head_of_kind_naked_vec128 (t1 : TG.head_of_kind_naked_vec128)
      (t2 : TG.head_of_kind_naked_vec128) =
    Vector_types.Vec128.Bit_pattern.Set.equal
      (t1 :> Vector_types.Vec128.Bit_pattern.Set.t)
      (t2 :> Vector_types.Vec128.Bit_pattern.Set.t)

  let equal_head_of_kind_rec_info (t1 : TG.head_of_kind_rec_info)
      (t2 : TG.head_of_kind_rec_info) =
    Rec_info_expr.equal t1 t2

  let equal_head_of_kind_region (t1 : TG.head_of_kind_region)
      (t2 : TG.head_of_kind_region) =
    let () = (t1 :> unit) and () = (t2 :> unit) in
    true

  let equal_expanded_head ~equal_type env (t1 : Expand_head.Expanded_type.t)
      (t2 : Expand_head.Expanded_type.t) =
    match
      Expand_head.Expanded_type.descr t1, Expand_head.Expanded_type.descr t2
    with
    | Unknown, Unknown -> true
    | Unknown, (Ok _ | Bottom) | (Ok _ | Bottom), Unknown -> false
    | Bottom, Bottom -> true
    | Ok _, Bottom | Bottom, Ok _ -> false
    | Ok t1, Ok t2 -> (
      match[@warning "-fragile-match"] t1, t2 with
      | Value t1, Value t2 -> equal_head_of_kind_value ~equal_type env t1 t2
      | Naked_immediate t1, Naked_immediate t2 ->
        equal_head_of_kind_naked_immediate ~equal_type env t1 t2
      | Naked_float32 t1, Naked_float32 t2 ->
        equal_head_of_kind_naked_float32 t1 t2
      | Naked_float t1, Naked_float t2 -> equal_head_of_kind_naked_float t1 t2
      | Naked_int32 t1, Naked_int32 t2 -> equal_head_of_kind_naked_int32 t1 t2
      | Naked_int64 t1, Naked_int64 t2 -> equal_head_of_kind_naked_int64 t1 t2
      | Naked_nativeint t1, Naked_nativeint t2 ->
        equal_head_of_kind_naked_nativeint t1 t2
      | Naked_vec128 t1, Naked_vec128 t2 ->
        equal_head_of_kind_naked_vec128 t1 t2
      | Rec_info t1, Rec_info t2 -> equal_head_of_kind_rec_info t1 t2
      | Region t1, Region t2 -> equal_head_of_kind_region t1 t2
      | _, _ -> false)
end

let rec equal_type env t1 t2 =
  let is_equal =
    t1 == t2
    ||
    match
      ( TE.get_alias_then_canonical_simple_exn ~min_name_mode:Name_mode.in_types
          env.Equal_types.left_env t1,
        TE.get_alias_then_canonical_simple_exn ~min_name_mode:Name_mode.in_types
          env.Equal_types.right_env t2 )
    with
    | canonical_simple1, canonical_simple2 ->
      let is_equal =
        match
          ( Simple.must_be_var canonical_simple1,
            Simple.must_be_var canonical_simple2 )
        with
        | None, _ | _, None -> Simple.equal canonical_simple1 canonical_simple2
        | Some (var1, coercion1), Some (var2, coercion2) ->
          let coercion =
            Coercion.compose_exn coercion1 ~then_:(Coercion.inverse coercion2)
          in
          if Coercion.is_id coercion
          then
            Variable.equal
              (Renaming.apply_variable env.Equal_types.left_renaming var1)
              var2
            ||
            let left_renaming =
              Renaming.add_variable env.Equal_types.left_renaming var1 var2
            in
            let env = { env with Equal_types.left_renaming } in
            Equal_types.equal_expanded_head ~equal_type env
              (Expand_head.expand_head env.Equal_types.left_env t1)
              (Expand_head.expand_head env.Equal_types.right_env t2)
          else
            Equal_types.equal_expanded_head ~equal_type env
              (Expand_head.expand_head env.Equal_types.left_env t1)
              (Expand_head.expand_head env.Equal_types.right_env t2)
      in
      if (not is_equal) && Flambda_features.debug_flambda2 ()
      then
        Format.eprintf "distinct canonicals: %a <> %a@." Simple.print
          canonical_simple1 Simple.print canonical_simple2;
      is_equal
    | exception Not_found ->
      Equal_types.equal_expanded_head ~equal_type env
        (Expand_head.expand_head env.Equal_types.left_env t1)
        (Expand_head.expand_head env.Equal_types.right_env t2)
  in
  if (not is_equal) && Flambda_features.debug_flambda2 ()
  then Format.eprintf "%a <> %a@." TG.print t1 TG.print t2;
  is_equal

let check_env_extension_from_level t left_level right_level =
  let left_env =
    TE.add_env_extension_from_level t left_level
      ~meet_type:(Meet_and_join.meet_type ())
  in
  let right_env =
    TE.add_env_extension_from_level t right_level
      ~meet_type:(Meet_and_join.meet_type ())
  in
  let env_for_equality =
    { Equal_types.left_env; right_env; left_renaming = Renaming.empty }
  in
  let t = left_env in
  let level = right_level in
  let defined_names = TEL.defined_names level in
  let t =
    TEL.fold_on_defined_vars
      (fun var kind t ->
        TE.add_definition t
          (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
          kind)
      level t
  in
  let t =
    Name.Map.fold
      (fun name ty t ->
        if Name.Set.mem name defined_names
        then TE.add_equation t name ty ~meet_type:(Meet_and_join.meet_type ())
        else t)
      (TEL.equations level) t
  in
  let t =
    Variable.Map.fold
      (fun var proj t -> TE.add_symbol_projection t var proj)
      (TEL.symbol_projections level)
      t
  in
  let cut_after = TE.current_scope t in
  Equal_types.equal_env_extension ~equal_type env_for_equality
    (TG.Env_extension.create ~equations:(TEL.equations left_level))
    (TG.Env_extension.create ~equations:(TEL.equations right_level))
  ||
  let t = TE.increment_scope t in
  Name.Map.for_all
    (fun name ty ->
      Name.Set.mem name defined_names
      || (try
            ignore (TG.get_alias_exn ty);
            true
          with Not_found -> false)
      ||
      let t' =
        TE.add_equation t name ty ~meet_type:(Meet_and_join.meet_type ())
      in
      let level = TE.cut t' ~cut_after in
      TEL.is_empty level
      ||
      match Meet_and_join.meet_type () with
      | TE.New meet_type_new -> (
        let canonical = get_canonical_simple_exn t (Simple.name name) in
        let existing_ty =
          Simple.pattern_match canonical
            ~const:(fun const -> MTC.type_for_const const)
            ~name:(fun name ~coercion ->
              TG.apply_coercion (TE.find t name None) coercion)
        in
        match meet_type_new t ty existing_ty with
        | Bottom ->
          Format.eprintf "for %a, bottom meet!@." Name.print name;
          Format.eprintf "left: %a@." TG.print ty;
          Format.eprintf "right: %a@." TG.print existing_ty;
          false
        | Ok (meet_ty, _) -> (
          match meet_ty with
          | Left_input ->
            (* Format.eprintf "for %a, got left only@." Name.print name;
               Format.eprintf "left: %a@." TG.print ty; Format.eprintf "right:
               %a@." TG.print existing_ty; *)
            true
          | Right_input | Both_inputs -> true
          | New_result ty' ->
            Format.eprintf "for %a, got a new type: %a@." Name.print name
              TG.print ty';
            false))
      | TE.Old _ -> assert false)
    (TEL.equations level)

let _cut_and_n_way_join definition_typing_env ts_and_use_ids ~params ~cut_after
    ~extra_lifted_consts_in_use_envs ~extra_allowed_names =
  let scope = TE.current_scope definition_typing_env in
  let typing_env = TE.increment_scope definition_typing_env in
  let old_joined_env =
    Join_levels_old.cut_and_n_way_join typing_env ts_and_use_ids ~params
      ~cut_after ~extra_lifted_consts_in_use_envs ~extra_allowed_names
  in
  let old_joined_level = TE.cut old_joined_env ~cut_after:scope in
  let new_joined_env =
    cut_and_n_way_join typing_env ts_and_use_ids ~params ~cut_after
      ~extra_lifted_consts_in_use_envs ~extra_allowed_names
  in
  let new_joined_level = TE.cut new_joined_env ~cut_after:scope in
  let _new_has_all_old_variables =
    Variable.Set.subset
      (TEL.defined_variables old_joined_level)
      (TEL.defined_variables new_joined_level)
  in
  if not
       (check_env_extension_from_level typing_env old_joined_level
          new_joined_level)
  then (
    List.iteri
      (fun i (t, _, _) ->
        let level = TE.cut t ~cut_after in
        Format.eprintf "@[<v>--------@ Level %d:@ %a@]@." i TEL.print level)
      ts_and_use_ids;
    if false then Format.eprintf "@[<v>ENV:@ %a@]@." TE.print old_joined_env;
    Format.eprintf "@[<v>OLD:@ %a@]@." TEL.print old_joined_level;
    Format.eprintf "@[<v>NEW:@ %a@]@." TEL.print new_joined_level;
    assert false);
  TE.add_env_extension_from_level definition_typing_env old_joined_level
    ~meet_type:(Meet_and_join.meet_type ())
