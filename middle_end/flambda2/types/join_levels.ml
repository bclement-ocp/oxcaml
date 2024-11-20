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
let recover_delta_aliases ~target_env env equations =
  let demoted_elements_for_canonicals =
    Name.Map.fold
      (fun name ty demoted_elements_for_canonicals ->
        match get_alias_then_canonical_simple_exn env ty with
        | canonical ->
          let bare_canonical = Simple.without_coercion canonical in
          let coercion_from_bare_canonical = Simple.coercion canonical in
          let coercion_to_bare_canonical =
            Coercion.inverse coercion_from_bare_canonical
          in
          let canonical_at_fork = Simple.name name in
          (if Flambda_features.check_light_invariants ()
          then
            let real_canonical_at_fork =
              get_canonical_simple_exn target_env canonical_at_fork
            in
            if not (Simple.equal canonical_at_fork real_canonical_at_fork)
            then
              Misc.fatal_errorf
                "Alias equation@ %a = %a@ found on demoted element (was \
                 already demoted to: %a)"
                Name.print name TG.print ty Simple.print real_canonical_at_fork);
          let canonical_at_fork =
            Simple.apply_coercion_exn canonical_at_fork
              coercion_to_bare_canonical
          in
          (* This would mean that we have recorded an equation [x: (= y)] where
             the current canonical for [y] is equal to [x], which is not
             possible since [x] was demoted. *)
          assert (not (Simple.equal bare_canonical canonical_at_fork));
          Simple.Map.update bare_canonical
            (function
              | None -> Some (Aliases.Alias_set.singleton canonical_at_fork)
              | Some alias_set ->
                Some (Aliases.Alias_set.add canonical_at_fork alias_set))
            demoted_elements_for_canonicals
        | exception Not_found ->
          (* not an alias *) demoted_elements_for_canonicals)
      equations Simple.Map.empty
  in
  (* We no longer care about the current canonicals. *)
  Simple.Map.fold
    (fun canonical alias_set delta_aliases ->
      Aliases.Alias_set.add canonical alias_set :: delta_aliases)
    demoted_elements_for_canonicals []

let join_aliases base_env env_with_levels =
  match env_with_levels with
  | [] -> base_env, Name.Map.empty
  | (env_at_first_use, _, _, level_at_first_use) :: other_envs_with_levels ->
    let delta_aliases =
      recover_delta_aliases ~target_env:base_env env_at_first_use
        (TEL.equations level_at_first_use)
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
                      Simple.pattern_match alias
                        ~name:(fun name ~coercion:_ ->
                          if TE.mem env_at_other_use name
                          then get_canonical_simple_exn env_at_other_use alias
                          else alias)
                        ~const:(fun _ -> alias)
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
    (* We want to make sure that the map we return never uses canonical elements
       as keys, but we don't know which elements will be canonical until we have
       added all the equations.

       Instead of trying to be smart, we simply add all the equations, then cut
       the resulting environment. Since we only add alias types, the cut
       extension will not have any extension on canonical elements. *)
    let original_scope = TE.current_scope base_env in
    let base_env = TE.increment_scope base_env in
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
        base_env joined_aliases
    in
    ( base_env,
      TEE.to_map (TE.cut_as_extension base_env ~cut_after:original_scope) )

let join_types ~env_at_fork envs_with_levels =
  (* Add all the variables defined by the branches as existentials to the
     [env_at_fork].

     Any such variable will be given type [Bottom] on a branch where it was not
     originally present.

     In addition, this also aggregates the code age relations of the
     branches. *)
  let base_env =
    List.fold_left
      (fun base_env (env_at_use, _, _, level) ->
        let base_env =
          Variable.Map.fold
            (fun var kind base_env ->
              if TE.mem base_env (Name.var var)
              then base_env
              else
                TE.add_definition base_env
                  (Bound_name.create_var
                     (Bound_var.create var Name_mode.in_types))
                  kind)
            (TEL.defined_variables_with_kinds level)
            base_env
        in
        let code_age_relation =
          Code_age_relation.union
            (TE.code_age_relation base_env)
            (TE.code_age_relation env_at_use)
        in
        TE.with_code_age_relation base_env code_age_relation)
      env_at_fork envs_with_levels
  in
  let base_env, joined_aliases = join_aliases base_env envs_with_levels in
  (* Translate all equations, moving them to canonical representatives in the
     shared environment. *)
  let equations_in_base_env =
    List.map
      (fun (env_at_use, _, _, level) ->
        let get_canonical_simple_at_use simple =
          (* We want to know how to refer in [base_env] to the canonical of
             [simple] in [env_at_use].

             This should simply be the canonical of [simple] in [env_at_use],
             but there is a twist: since [base_env] and [env_at_use] do not
             necessarily select the same canonical elements for a given
             equivalence class, the canonical of [simple] in [env_at_use] is not
             necessarily the canonical of its class in [base_env]. *)
          get_canonical_simple_exn base_env
            (get_canonical_simple_exn env_at_use simple)
        in
        let equations = TEL.equations level in
        let cclasses, canonical_equations =
          Name.Map.fold
            (fun name ty (cclasses, canonical_equations) ->
              match TG.get_alias_exn ty with
              | exception Not_found ->
                (* Not an alias type: record it on the current canonical *)
                let canonical_at_use =
                  get_canonical_simple_at_use (Simple.name name)
                in
                ( cclasses,
                  Simple.pattern_match canonical_at_use
                    ~name:(fun bare_canonical_name ~coercion ->
                      let type_for_bare_canonical =
                        TG.apply_coercion ty (Coercion.inverse coercion)
                      in
                      Name.Map.update bare_canonical_name
                        (function
                          | None -> Some type_for_bare_canonical
                          | Some existing_ty ->
                            Format.printf
                              "recording %a on %a but already have %a" TG.print
                              type_for_bare_canonical Name.print
                              bare_canonical_name TG.print existing_ty;
                            assert false)
                        canonical_equations)
                    ~const:(fun _ -> canonical_equations) )
              | alias ->
                (* There are two cases: either the alias is valid at base (i.e.
                   holds in all joined environments), or it is specific to this
                   use. *)
                let base_canonical_simple =
                  get_canonical_simple_exn base_env (Simple.name name)
                in
                let base_canonical_alias =
                  get_canonical_simple_exn base_env alias
                in
                if Simple.equal base_canonical_alias base_canonical_simple
                then
                  (* The alias is true in all joined environments; it has
                     already been computed from the [joined_aliases].

                     We will recover an equivalent equation by cutting the
                     [base_env]. *)
                  cclasses, canonical_equations
                else
                  (* The equality is true in the current environment, but not in
                     the base env.

                     Record that the canonical values in the base env are part
                     of the same equivalence class in the current environment.

                     We do not add any equation to the [canonical_equations];
                     instead, we record that [base_canonical_simple] and
                     [base_canonical_alias] are in the same equivalence class.

                     In the next step, we will use this information to duplicate
                     the equation on the canonical at use onto the whole
                     class. *)
                  let canonical_simple_at_use =
                    get_canonical_simple_at_use base_canonical_simple
                  in
                  (if Flambda_features.check_light_invariants ()
                  then
                    let canonical_alias_at_use =
                      get_canonical_simple_at_use base_canonical_alias
                    in
                    assert (
                      Simple.equal canonical_simple_at_use
                        canonical_alias_at_use));
                  let bare_canonical_simple_at_use =
                    Simple.without_coercion canonical_simple_at_use
                  in
                  let coercion_to_canonical_simple_at_use =
                    Simple.coercion canonical_simple_at_use
                  in
                  let coercion_from_canonical_simple_at_use =
                    Coercion.inverse coercion_to_canonical_simple_at_use
                  in
                  let cclasses =
                    Simple.Map.update bare_canonical_simple_at_use
                      (fun alias_set_opt ->
                        let alias_set =
                          match alias_set_opt with
                          | None -> Aliases.Alias_set.empty
                          | Some alias_set -> alias_set
                        in
                        let alias_set =
                          Aliases.Alias_set.add
                            (Simple.apply_coercion_exn base_canonical_simple
                               coercion_from_canonical_simple_at_use)
                            alias_set
                        in
                        let alias_set =
                          Aliases.Alias_set.add
                            (Simple.apply_coercion_exn base_canonical_alias
                               coercion_from_canonical_simple_at_use)
                            alias_set
                        in
                        Some alias_set)
                      cclasses
                  in
                  cclasses, canonical_equations)
            equations
            (Simple.Map.empty, Name.Map.empty)
        in
        (* If we have an equation [x: ty] in the current environment and [x] is
           equal to [y] in all joined environments, also record equations for
           [y: ty].

           Note that this does not increase the number of equations: to reach
           this situation, we must have removed an alias equation in the
           previous step. *)
        let canonical_equations =
          Simple.Map.fold
            (fun canonical_at_use alias_set canonical_equations ->
              let ty_opt =
                Simple.pattern_match canonical_at_use
                  ~name:(fun name ~coercion ->
                    match Name.Map.find name canonical_equations with
                    | exception Not_found -> None
                    | ty -> Some (TG.apply_coercion ty coercion))
                  ~const:(fun const -> Some (MTC.type_for_const const))
              in
              match ty_opt with
              | Some ty ->
                Aliases.Alias_set.fold
                  (fun simple canonical_equations ->
                    if Simple.equal simple canonical_at_use
                    then canonical_equations
                    else
                      Simple.pattern_match simple
                        ~name:(fun name ~coercion ->
                          Name.Map.add name
                            (TG.apply_coercion ty (Coercion.inverse coercion))
                            canonical_equations)
                        ~const:(fun _ ->
                          (* Any constant is necessarily canonical. *)
                          assert false))
                  alias_set canonical_equations
              | None ->
                Format.eprintf "nothing learned at this level for class: %a@."
                  Aliases.Alias_set.print alias_set;
                canonical_equations)
            cclasses canonical_equations
        in
        Format.eprintf
          "@[<v>@[<v 2>I have split:@ @[<v>%a@]@]@ @[<v 2>Canonicals:@ \
           @[<v>%a@]@ @[<v 2>Classes:@ @[<v>%a@]@]@]@]@."
          (Name.Map.print TG.print) equations (Name.Map.print TG.print)
          canonical_equations
          (Simple.Map.print Aliases.Alias_set.print)
          cclasses;
        env_at_use, canonical_equations)
      envs_with_levels
  in
  (* Find the actual domain of the join of the levels

     We compute an extension that is the join of the extensions corresponding to
     all the levels. To avoid the difficulty with computing the domain lazily
     during the join, we pre-compute the domain and initialise our accumulator
     with bottom types for all variables involved. *)
  let initial_types =
    List.fold_left
      (fun initial_types (_, equations) ->
        Name.Map.fold
          (fun name ty initial_types ->
            if Name.is_var name
            then Name.Map.add name (MTC.bottom_like ty) initial_types
            else initial_types)
          equations initial_types)
      Name.Map.empty equations_in_base_env
  in
  let joined_types =
    (* Now fold over the levels doing the actual join operation on equations. *)
    ListLabels.fold_left equations_in_base_env ~init:initial_types
      ~f:(fun joined_types (env_at_use, canonical_equations) ->
        let left_env =
          (* CR vlaviron: This is very likely quadratic (number of uses times
             number of variables in all uses). However it's hard to know how we
             could do better. *)
          TE.add_env_extension_maybe_bottom base_env
            (TEE.from_map joined_types)
            ~meet_type:(Meet_and_join.meet_type ())
        in
        let join_types name joined_ty use_ty =
          let same_unit =
            Compilation_unit.equal
              (Name.compilation_unit name)
              (Compilation_unit.get_current_exn ())
          in
          if same_unit && not (TE.mem base_env name)
          then
            Misc.fatal_errorf "Name %a not defined in [base_env]:@ %a"
              Name.print name TE.print base_env;
          (* If [name] is that of a lifted constant symbol generated during one
             of the levels, then ignore it. [Simplify_expr] will already have
             made its type suitable for [base_env] and inserted it into that
             environment.

             If [name] is a symbol that is not a lifted constant, then it was
             defined before the fork and already has an equation in base_env.
             While it is possible that its type could be refined by all of the
             branches, it is unlikely. *)
          if not (Name.is_var name)
          then None
          else
            let joined_ty, use_ty =
              match joined_ty, use_ty with
              | None, Some _use_ty ->
                assert false (* See the computation of [initial_types] *)
              | Some joined_ty, None ->
                (* There is no equation, at all (not even saying "unknown"), on
                   the current level for [name]. There are two possible cases
                   for that:

                   - The environment at use knows of this variable, but this
                   level has no equation on it. In this case, we need to
                   retrieve the type from [env_at_use] and join with it.

                   - The variable doesn't exist in this environment. This
                   happens if the variable is defined in one of the other
                   branches, and will be quantified existentially in the result.
                   In this case, it's safe to join with Bottom. *)
                let is_defined_at_use = TE.mem env_at_use name in
                if is_defined_at_use
                then
                  let use_ty =
                    let expected_kind = Some (TG.kind joined_ty) in
                    TE.find env_at_use name expected_kind
                  in
                  joined_ty, use_ty
                else joined_ty, MTC.bottom_like joined_ty
              | Some joined_ty, Some use_ty -> joined_ty, use_ty
              | None, None -> assert false
            in
            let join_env =
              Join_env.create base_env ~left_env ~right_env:env_at_use
            in
            match
              (Meet_and_join.join ()) ~bound_name:name join_env joined_ty use_ty
            with
            | Known joined_ty -> Some joined_ty
            | Unknown -> None
        in
        Name.Map.merge join_types joined_types canonical_equations)
  in
  (* Make sure we include the shared aliases in the joined extension. *)
  Name.Map.disjoint_union joined_aliases joined_types

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
  let joined_types = join_types ~env_at_fork envs_with_levels in
  (* Next calculate which equations (describing joined types) to propagate to
     the join point. (Recall that the environment at the fork point includes the
     parameters of the continuation being called at the join. We wish to ensure
     that information in the types of these parameters is not lost.)

     - Equations on names defined in the environment at the fork point are
     always propagated.

     - Definitions of, and equations on, names that occur free on the right-hand
     sides of the propagated equations are also themselves propagated. The
     definition of any such propagated name (i.e. one that does not occur in the
     environment at the fork point) will be made existential. *)
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
  (* Having calculated which equations to propagate, the resulting level can now
     be constructed. *)
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
