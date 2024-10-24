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

module TG = Type_grammar

type t = TG.Env_extension.t

let fold = TG.Env_extension.fold

let invariant ({ type_equations; rel_equations = _ } : t) =
  if Flambda_features.check_invariants ()
  then Name.Map.iter More_type_creators.check_equation type_equations

let empty = TG.Env_extension.empty

let mem name ({ type_equations; rel_equations = _ } : t) =
  Name.Map.mem name type_equations (* || Name.Map.mem name rel_equations *)

let is_empty ({ type_equations; rel_equations } : t) =
  Name.Map.is_empty type_equations && Name.Map.is_empty rel_equations

let from_maps ~equations ~relations =
  let t = TG.Env_extension.create ~equations ~relations in
  invariant t;
  t

let one_equation name ty =
  More_type_creators.check_equation name ty;
  TG.Env_extension.create
    ~equations:(Name.Map.singleton name ty)
    ~relations:Name.Map.empty

let one_relation name rel =
  TG.Env_extension.create ~equations:Name.Map.empty
    ~relations:(Name.Map.singleton name (TG.RelationSet.singleton rel))

let add_or_replace_equation ({ type_equations; rel_equations } : t) name ty =
  More_type_creators.check_equation name ty;
  if Flambda_features.check_invariants () && Name.Map.mem name type_equations
  then
    Format.eprintf
      "Warning: Overriding equation for name %a@\n\
       Old equation is@ @[%a@]@\n\
       New equation is@ @[%a@]@." Name.print name TG.print
      (Name.Map.find name type_equations)
      TG.print ty;
  TG.Env_extension.create
    ~equations:(Name.Map.add name ty type_equations)
    ~relations:rel_equations

let add_relation ({ type_equations; rel_equations } : t) name rel =
  TG.Env_extension.create ~equations:type_equations
    ~relations:
      (Name.Map.update name
         (function
           | None -> Some (TG.RelationSet.singleton rel)
           | Some rels -> Some (TG.RelationSet.add rel rels))
         rel_equations)

let replace_equation ({ type_equations; rel_equations } : t) name ty =
  TG.Env_extension.create
    ~equations:(Name.Map.add (* replace *) name ty type_equations)
    ~relations:rel_equations

let ids_for_export = TG.Env_extension.ids_for_export

let apply_renaming = TG.Env_extension.apply_renaming

let free_names = TG.Env_extension.free_names

let print = TG.Env_extension.print

let disjoint_union (env1 : t) (env2 : t) =
  TG.Env_extension.create
    ~equations:(Name.Map.disjoint_union env1.type_equations env2.type_equations)
    ~relations:(Name.Map.disjoint_union env1.rel_equations env2.rel_equations)

module With_extra_variables = struct
  type t =
    { existential_vars : Flambda_kind.t Variable.Map.t;
      env_extension : TG.Env_extension.t
    }

  let print ppf { existential_vars; env_extension } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(variables@ @[<hov 1>%a@])@]@ @[<hov 1>%a@])@ @]"
      (Variable.Map.print Flambda_kind.print)
      existential_vars TG.Env_extension.print env_extension

  let fold ~variable ~equation t acc =
    let acc = Variable.Map.fold variable t.existential_vars acc in
    TG.Env_extension.fold ~equation t.env_extension acc

  let empty =
    { existential_vars = Variable.Map.empty;
      env_extension = TG.Env_extension.empty
    }

  let add_definition t var kind =
    let existential_vars = Variable.Map.add var kind t.existential_vars in
    { existential_vars; env_extension = t.env_extension }

  let add_or_replace_equation t name ty =
    More_type_creators.check_equation name ty;
    { existential_vars = t.existential_vars;
      env_extension = TG.Env_extension.add_type_equation name ty t.env_extension
    }

  let free_names_equation eqn =
    match eqn with
    | TG.Type ty -> TG.free_names ty
    | TG.Rel rel -> (
      match rel with
      | Is_int name | Get_tag name ->
        Name_occurrences.singleton_name name Name_mode.in_types)

  let free_names { existential_vars; env_extension } =
    let variables = Variable.Map.keys existential_vars in
    let free_names =
      Name_occurrences.create_variables variables Name_mode.in_types
    in
    TG.Env_extension.fold
      ~equation:(fun name eqn free_names ->
        let free_names =
          Name_occurrences.add_name free_names name Name_mode.in_types
        in
        Name_occurrences.union free_names (free_names_equation eqn))
      env_extension free_names

  let apply_renaming_equation eqn renaming =
    match eqn with
    | TG.Type ty -> TG.Type (TG.apply_renaming ty renaming)
    | TG.Rel rel ->
      TG.Rel
        (match rel with
        | Is_int name -> Is_int (Renaming.apply_name renaming name)
        | Get_tag name -> Get_tag (Renaming.apply_name renaming name))

  let apply_renaming { existential_vars; env_extension } renaming =
    let existential_vars =
      Variable.Map.fold
        (fun var kind result ->
          let var' = Renaming.apply_variable renaming var in
          Variable.Map.add var' kind result)
        existential_vars Variable.Map.empty
    in
    let env_extension =
      TG.Env_extension.fold
        ~equation:(fun name eqn result ->
          let name' = Renaming.apply_name renaming name in
          let eqn' = apply_renaming_equation eqn renaming in
          TG.Env_extension.add_equation name' eqn' result)
        env_extension TG.Env_extension.empty
    in
    { existential_vars; env_extension }

  let ids_for_export_equation eqn =
    match eqn with
    | TG.Type ty -> TG.ids_for_export ty
    | TG.Rel rel -> (
      match rel with
      | Is_int name | Get_tag name ->
        Ids_for_export.add_name Ids_for_export.empty name)

  let ids_for_export { existential_vars; env_extension } =
    let variables = Variable.Map.keys existential_vars in
    let ids = Ids_for_export.create ~variables () in
    TG.Env_extension.fold
      ~equation:(fun name eqn ids ->
        let ids = Ids_for_export.add_name ids name in
        Ids_for_export.union ids (ids_for_export_equation eqn))
      env_extension ids

  let existential_vars { existential_vars; _ } =
    Variable.Map.keys existential_vars

  let map_types { existential_vars; env_extension } ~f =
    let env_extension = TG.Env_extension.map ~type_:f env_extension in
    { existential_vars; env_extension }
end
