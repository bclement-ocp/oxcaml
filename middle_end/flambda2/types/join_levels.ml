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

module TE = Typing_env
module TEL = Typing_env_level

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

let cut_and_n_way_join_unchecked definition_typing_env ts_and_use_ids ~params
    ~cut_after ~extra_lifted_consts_in_use_envs ~extra_allowed_names:_ =
  let params = Bound_parameters.to_list params in
  check_join_inputs ~env_at_fork:definition_typing_env ts_and_use_ids ~params
    ~extra_lifted_consts_in_use_envs;
  let ts_and_use_ids = List.rev ts_and_use_ids in
  let central_env = definition_typing_env in
  let joined_envs =
    List.map
      (fun (t, _use_id, _use_kind) ->
        let level = TE.cut t ~cut_after in
        t, level)
      ts_and_use_ids
  in
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

let cut_and_n_way_join_checked definition_typing_env ts_and_use_ids ~params
    ~cut_after ~extra_lifted_consts_in_use_envs ~extra_allowed_names =
  (* TODO: symbol projections!! *)
  if Flambda_features.debug_flambda2 ()
  then
    Format.eprintf "extra lifted consts: %a@." Symbol.Set.print
      extra_lifted_consts_in_use_envs;
  if Flambda_features.debug_flambda2 ()
  then
    Format.eprintf "extra allowed names: %a@." Name_occurrences.print
      extra_allowed_names;
  let scope = TE.current_scope definition_typing_env in
  let typing_env = TE.increment_scope definition_typing_env in
  let old_joined_env =
    Join_levels_old.cut_and_n_way_join typing_env ts_and_use_ids ~params
      ~cut_after ~extra_lifted_consts_in_use_envs ~extra_allowed_names
  in
  let old_joined_level = TE.cut old_joined_env ~cut_after:scope in
  let new_joined_env =
    cut_and_n_way_join_unchecked typing_env ts_and_use_ids ~params ~cut_after
      ~extra_lifted_consts_in_use_envs ~extra_allowed_names
  in
  let new_joined_level = TE.cut new_joined_env ~cut_after:scope in
  let _new_has_all_old_variables =
    Variable.Set.subset
      (TEL.defined_variables old_joined_level)
      (TEL.defined_variables new_joined_level)
  in
  if not
       (Equal_types_for_debug.equal_level_ignoring_name_mode
          ~meet_type:(Meet_and_join.meet_type ())
          typing_env old_joined_level new_joined_level)
  then (
    List.iteri
      (fun i (t, _, _) ->
        let level = TE.cut t ~cut_after in
        Format.eprintf "@[<v>--------@ Level %d:@ %a@]@." i TEL.print level)
      ts_and_use_ids;
    if false then Format.eprintf "@[<v>ENV:@ %a@]@." TE.print old_joined_env;
    Format.eprintf "@[<v>OLD:@ %a@]@." TEL.print old_joined_level;
    Format.eprintf "@[<v>NEW:@ %a@]@." TEL.print new_joined_level);
  TE.add_env_extension_from_level definition_typing_env old_joined_level
    ~meet_type:(Meet_and_join.meet_type ())

let cut_and_n_way_join =
  if true then cut_and_n_way_join_unchecked else cut_and_n_way_join_checked
