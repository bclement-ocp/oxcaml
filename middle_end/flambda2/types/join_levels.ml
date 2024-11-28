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
module Join_env = TE.Join_env

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
  | (env_at_first_use, _, _, level_at_first_use) :: other_envs_with_levels ->
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
        (fun delta_aliases (env_at_other_use, _, _, _) ->
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
      (fun base_env (env_at_use, _, _, level) ->
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
          Join_env.create base_env ~left_env ~right_env:env_at_use
        in
        let rec loop join_env to_join joined_types =
          match Name.Map.choose to_join with
          | exception Not_found ->
            let to_join, join_env = Join_env.at_next_depth join_env in
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
          Name.Map.inter
            (fun _name joined_ty use_ty -> joined_ty, use_ty)
            joined_types equations
        in
        let joined_types = loop join_env to_join Name.Map.empty in
        let new_variables =
          Join_env.fold_variables Variable.Set.add join_env Variable.Set.empty
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
         (Format.pp_print_list (fun ppf (_, _, _, level) -> TEL.print ppf level))
         envs_with_levels TEE.print
         (TEE.from_map joined_types));
  let final_env =
    Variable.Set.fold
      (fun var final_env ->
        if TE.mem ~min_name_mode:Name_mode.in_types final_env (Name.var var)
        then final_env
        else
          let kind =
            match Name.Map.find (Name.var var) joined_types with
            | ty -> TG.kind ty
            | exception Not_found -> assert false
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
      (fun (defined_vars, binding_times) (_env_at_use, _id, _use_kind, t) ->
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
      (fun symbol_projections (_env_at_use, _id, _use_kind, t) ->
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

let cut_and_n_way_join definition_typing_env ts_and_use_ids ~params ~cut_after
    ~extra_lifted_consts_in_use_envs ~extra_allowed_names =
  let after_cuts =
    List.map
      (fun (t, use_id, use_kind) ->
        let level = TE.cut t ~cut_after in
        t, use_id, use_kind, level)
      ts_and_use_ids
  in
  let params = Bound_parameters.to_list params in
  let level =
    n_way_join ~env_at_fork:definition_typing_env after_cuts ~params
      ~extra_lifted_consts_in_use_envs ~extra_allowed_names
  in
  TE.add_env_extension_from_level definition_typing_env level
    ~meet_type:(Meet_and_join.meet_type ())
