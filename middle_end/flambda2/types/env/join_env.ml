module K = Flambda_kind
module MTC = More_type_creators
module TG = Type_grammar
module TE = Typing_env
module TEE = Typing_env_extension
module TEL = Typing_env_level
module ET = Expand_head.Expanded_type

(* XXX: The only thing we really need from the join env is to get us the
   aliases, and to mark the aliases for joining. We *DO NOT* actually need to
   depend on the typing env in this file, which would make it easier to migrate
   to the database (I have not given up on it). *)

(* Some helpful aliases to access typing environments.

   Note that we only ever care about the "in types" name mode here. *)

let mem_name env name = TE.mem ~min_name_mode:Name_mode.in_types env name

let mem_simple env simple =
  TE.mem_simple ~min_name_mode:Name_mode.in_types env simple

let get_alias_then_canonical_simple_exn env ty =
  TE.get_alias_then_canonical_simple_exn ~min_name_mode:Name_mode.in_types env
    ty

let get_canonical_simple_exn env simple =
  TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types env simple

let find_canonical env name = get_canonical_simple_exn env (Simple.name name)

type coercion_to_canonical = Coercion.t

module Map_to_canonical = struct
  type t = coercion_to_canonical Name.Map.t

  let print ppf map = Name.Map.print Coercion.print ppf map

  let fatal_inconsistent ~func_name elt coercion1 coercion2 =
    Misc.fatal_errorf
      "[%s] maps with inconsistent  element/coercion couples; %a has coercions \
       %a and %a"
      func_name Name.print elt Coercion.print coercion1 Coercion.print coercion2

  let empty = Name.Map.empty

  let is_empty = Name.Map.is_empty

  let add name ~coercion map = Name.Map.add name coercion map

  let compose t ~then_ = Name.Map.map_sharing (Coercion.compose_exn ~then_) t

  let singleton name = Name.Map.singleton name Coercion.id

  let inter map1 map2 =
    Name.Map.merge
      (fun _elt coercion1 coercion2 ->
        match coercion1, coercion2 with
        | None, None | Some _, None | None, Some _ -> None
        | Some coercion1, Some coercion2 ->
          (* See documentation of [Alias_set.inter] *)
          if Coercion.equal coercion1 coercion2 then Some coercion1 else None)
      map1 map2

  let union map1 map2 =
    Name.Map.union
      (fun elt coercion1 coercion2 ->
        match coercion1, coercion2 with
        | coercion1, coercion2 ->
          if Coercion.equal coercion1 coercion2
          then Some coercion1
          else
            fatal_inconsistent ~func_name:"Aliases.Map_to_canonical.union" elt
              coercion1 coercion2)
      map1 map2
end

module Alias_set = struct
  type t =
    { const : Reg_width_const.t option;
      names : Coercion.t Name.Map.t
    }

  let [@ocamlformat "disable"] print ppf { const; names; } =
    let none ppf () =
      Format.fprintf ppf "%t()%t" Flambda_colours.elide Flambda_colours.pop
    in
    Format.fprintf ppf
      "@[<hov 1>(\
           @[<hov 1>(const@ %a)@]@ \
           @[<hov 1>(names@ %a)@]\
       @]"
       (Format.pp_print_option Reg_width_const.print ~none) const
       (Name.Map.print Coercion.print) names

  let create ?const names = { const; names }

  let choose { const; names } =
    match const with
    | Some const -> Some (Simple.const const)
    | None -> (
      match Name.Map.choose names with
      | name, coercion ->
        Some (Simple.with_coercion (Simple.name name) coercion)
      | exception Not_found -> None)

  let get_singleton { const; names } =
    match const with
    | Some const ->
      if Name.Map.is_empty names then Some (Simple.const const) else None
    | None -> (
      match Name.Map.get_singleton names with
      | Some (name, coercion) ->
        Some (Simple.with_coercion (Simple.name name) coercion)
      | None -> None)

  let fold_equations f { const; names } acc =
    match const with
    | Some const ->
      let canonical = Simple.const const in
      Name.Map.fold (fun name _coercion acc -> f name canonical acc) names acc
    | None ->
      if Name.Map.is_empty names
      then acc
      else
        let any_name, any_coercion = Name.Map.choose names in
        let any_simple =
          Simple.with_coercion (Simple.name any_name) any_coercion
        in
        let names = Name.Map.remove any_name names in
        Name.Map.fold
          (fun name coercion acc ->
            f name
              (Simple.apply_coercion_exn any_simple (Coercion.inverse coercion))
              acc)
          names acc

  let fold f t acc =
    let acc =
      match t.const with
      | Some const -> f (Simple.const const) acc
      | None -> acc
    in
    Name.Map.fold
      (fun name coercion acc ->
        f (Simple.with_coercion (Simple.name name) coercion) acc)
      t.names acc

  let is_empty { const; names } =
    Option.is_none const && Name.Map.is_empty names

  let singleton simple =
    Simple.pattern_match simple
      ~const:(fun const -> create ~const Name.Map.empty)
      ~name:(fun name ~coercion -> create (Name.Map.singleton name coercion))

  let add simple t =
    Simple.pattern_match simple
      ~const:(fun const ->
        match t.const with
        | Some existing_const ->
          if Reg_width_const.equal const existing_const then t else assert false
        | None -> { t with const = Some const })
      ~name:(fun name ~coercion ->
        let names =
          Name.Map.update name
            (function
              | None -> Some coercion
              | Some existing_coercion ->
                if Coercion.equal coercion existing_coercion
                then Some existing_coercion
                else None)
            t.names
        in
        { t with names })
end

module Demoted_to_canonical = struct
  type t =
    { demoted_to_canonical_name : Map_to_canonical.t Name.Map.t;
      demoted_to_const : Map_to_canonical.t Reg_width_const.Map.t
    }

  let [@ocamlformat "disable"] print
    ppf { demoted_to_canonical_name; demoted_to_const }
  =
    Format.fprintf ppf
      "@[<hov 1>(\
           @[<hov 1>(const@ %a)@]@ \
           @[<hov 1>(names@ %a)@]\
       @]"
       (Reg_width_const.Map.print Map_to_canonical.print) demoted_to_const
       (Name.Map.print Map_to_canonical.print) demoted_to_canonical_name

  let empty =
    { demoted_to_canonical_name = Name.Map.empty;
      demoted_to_const = Reg_width_const.Map.empty
    }

  let get_demoted_to_canonical_name t name =
    try Name.Map.find name t.demoted_to_canonical_name
    with Not_found -> Map_to_canonical.empty

  let classes ~central_env t =
    let classes =
      Reg_width_const.Map.fold
        (fun const demoted acc ->
          (Alias_set.create ~const demoted, [Simple.const const]) :: acc)
        t.demoted_to_const []
    in
    Name.Map.fold
      (fun name demoted acc ->
        let aliases =
          if mem_name central_env name
          then Map_to_canonical.add name ~coercion:Coercion.id demoted
          else demoted
        in
        (Alias_set.create aliases, [Simple.name name]) :: acc)
      t.demoted_to_canonical_name classes

  let get_demoted_to_canonical_element t canonical =
    try
      Simple.pattern_match canonical
        ~const:(fun const -> Reg_width_const.Map.find const t.demoted_to_const)
        ~name:(fun name ~coercion ->
          assert (Coercion.is_id coercion);
          Name.Map.find name t.demoted_to_canonical_name)
    with Not_found -> Map_to_canonical.empty

  let set_demoted_to_canonical_element t canonical demoted_to_canonical =
    Simple.pattern_match canonical
      ~name:(fun name ~coercion ->
        assert (Coercion.is_id coercion);
        { t with
          demoted_to_canonical_name =
            Name.Map.add (* replace *) name demoted_to_canonical
              t.demoted_to_canonical_name
        })
      ~const:(fun const ->
        { t with
          demoted_to_const =
            Reg_width_const.Map.add (* replace *) const demoted_to_canonical
              t.demoted_to_const
        })

  let add alias ~canonical t =
    let demoted_to_canonical = get_demoted_to_canonical_element t canonical in
    let demoted_to_canonical_simple =
      Name.Map.add alias
        (Coercion.inverse (Simple.coercion canonical))
        demoted_to_canonical
    in
    set_demoted_to_canonical_element t canonical demoted_to_canonical_simple

  let merge ~demoted_name ~canonical t =
    match Name.Map.find demoted_name t.demoted_to_canonical_name with
    | demoted_to_demoted_name ->
      let demoted_to_canonical_name =
        Name.Map.remove demoted_name t.demoted_to_canonical_name
      in
      let t = { t with demoted_to_canonical_name } in
      let demoted_to_canonical_simple =
        get_demoted_to_canonical_element t canonical
      in
      let coercion_from_demoted_name_to_canonical_simple =
        Coercion.inverse (Simple.coercion canonical)
      in
      let demoted_to_canonical_simple =
        Name.Map.merge
          (fun _ coercion_to_demoted_name coercion_to_canonical_simple ->
            match coercion_to_demoted_name, coercion_to_canonical_simple with
            | None, None -> assert false
            | Some coercion_to_demoted_name, None ->
              Some
                (Coercion.compose_exn coercion_to_demoted_name
                   ~then_:coercion_from_demoted_name_to_canonical_simple)
            | None, Some coercion_to_canonical_simple ->
              Some coercion_to_canonical_simple
            | Some coercion_to_demoted_name, Some coercion_to_canonical_simple
              ->
              if Simple.is_const canonical
                 || Coercion.equal coercion_to_demoted_name
                      coercion_to_canonical_simple
              then Some coercion_to_canonical_simple
              else None)
          demoted_to_demoted_name demoted_to_canonical_simple
      in
      set_demoted_to_canonical_element t canonical demoted_to_canonical_simple
    | exception Not_found -> t
end

module Cache = struct
  type entry =
    { right_bottom : Variable.t option;
      right_simples : Variable.t Simple.Map.t
    }

  let empty_entry = { right_bottom = None; right_simples = Simple.Map.empty }

  let add_simple ~name map simple =
    match Simple.Map.find_opt simple map with
    | Some variable ->
      let () = assert false in
      variable, map
    | None -> name, Simple.Map.add simple name map

  let add_entry ~name entry (right : Simple.t Or_bottom.t) =
    match right with
    | Bottom -> (
      match entry.right_bottom with
      | None -> name, { entry with right_bottom = Some name }
      | Some right_bottom ->
        let () = assert false in
        right_bottom, entry)
    | Ok right_simple ->
      let variable, right_simples =
        add_simple ~name entry.right_simples right_simple
      in
      variable, { entry with right_simples }

  type t =
    { left_bottom : Variable.t Simple.Map.t;
      left_simples : entry Simple.Map.t
    }

  let empty =
    { left_bottom = Simple.Map.empty; left_simples = Simple.Map.empty }

  let find_opt t (left : Simple.t Or_bottom.t) (right : Simple.t Or_bottom.t) =
    match left with
    | Bottom -> (
      match right with
      | Bottom -> None
      | Ok right_simple -> Simple.Map.find_opt right_simple t.left_bottom)
    | Ok left_simple -> (
      match Simple.Map.find_opt left_simple t.left_simples with
      | None -> None
      | Some entry -> (
        match right with
        | Bottom -> entry.right_bottom
        | Ok right_simple ->
          Simple.Map.find_opt right_simple entry.right_simples))

  let add ~name t (left : Simple.t Or_bottom.t) (right : Simple.t Or_bottom.t) :
      _ Or_bottom.t * _ =
    match left with
    | Bottom -> (
      match right with
      | Bottom -> Bottom, t
      | Ok right_simple ->
        let variable, left_bottom =
          add_simple ~name t.left_bottom right_simple
        in
        Ok variable, { t with left_bottom })
    | Ok left_simple ->
      let entry =
        try Simple.Map.find left_simple t.left_simples
        with Not_found -> empty_entry
      in
      let variable, entry = add_entry ~name entry right in
      let left_simples = Simple.Map.add left_simple entry t.left_simples in
      Ok variable, { t with left_simples }

  let record ~name t left right =
    let entry =
      try Simple.Map.find left t.left_simples with Not_found -> empty_entry
    in
    let right_simples =
      Simple.Map.update right
        (function None -> Some name | Some _ -> assert false)
        entry.right_simples
    in
    let entry = { entry with right_simples } in
    let left_simples = Simple.Map.add left entry t.left_simples in
    { t with left_simples }
end

(** A [joined_env] represents one of the branches of a join.

    The [joined_env] is relative to a central environment that is the result of
    the join. *)
type joined_env =
  { typing_env : TE.t;  (** The typing env that is getting joined. Invariant. *)
    demoted_to_canonical : Demoted_to_canonical.t;
        (** Names {b from the central env} that have been demoted in this branch,
            mapped to their canonical {b in this branch}. *)
    names_with_new_equation : Name.Set.t
        (** Names that have a new equation in this branch. *)
  }

let partition_classes classes joined_env =
  List.concat_map
    (fun (alias_set, canonicals_in_other_envs) ->
      let partition =
        Alias_set.fold
          (fun alias partition ->
            let canonical_in_this_env =
              (* It seems like [alias] should always be present in all joined
                 envs since it is present in the central env.

                 However, [alias] could have been imported from one of the
                 joined envs (e.g. [alias] is a lifted constant) without
                 necessarily being present in the current env. *)
              if mem_simple joined_env alias
              then get_canonical_simple_exn joined_env alias
              else alias
            in
            Simple.Map.update canonical_in_this_env
              (function
                | None -> Some (Alias_set.singleton alias)
                | Some alias_set -> Some (Alias_set.add alias alias_set))
              partition)
          alias_set Simple.Map.empty
      in
      Simple.Map.fold
        (fun canonical_in_this_env alias_set classes ->
          (alias_set, canonical_in_this_env :: canonicals_in_other_envs)
          :: classes)
        partition [])
    classes

let add_classes0 ~meet_type ~central_env ~classes =
  List.fold_left
    (fun typing_env (alias_set, _) ->
      Alias_set.fold_equations
        (fun name alias typing_env ->
          let kind = TG.kind (TE.find central_env name None) in
          let alias_ty = TG.alias_type_of kind alias in
          TE.add_equation typing_env name alias_ty ~meet_type)
        alias_set typing_env)
    central_env classes

let make_cache0 ~central_env ~classes =
  List.fold_left
    (fun cache (alias_set, shared_names) ->
      match Alias_set.choose alias_set with
      | Some alias ->
        assert (mem_simple central_env alias);
        let the_canonical = get_canonical_simple_exn central_env alias in
        Simple.pattern_match' the_canonical
          ~const:(fun _ -> cache)
          ~symbol:(fun _ ~coercion:_ -> cache)
          ~var:(fun var ~coercion ->
            assert (Coercion.is_id coercion);
            if List.for_all (Simple.equal the_canonical) shared_names
            then cache
            else
              match shared_names with
              | [right_simple; left_simple] ->
                Cache.record ~name:var cache left_simple right_simple
              | [_] -> cache
              | _ -> assert false)
      | None -> cache)
    Cache.empty classes

let demoted_to_canonical0 ~central_env:typing_env ~classes =
  List.fold_left
    (fun demoted_to_canonical (alias_set, _) ->
      Alias_set.fold
        (fun simple demoted_to_canonical ->
          Simple.pattern_match simple
            ~const:(fun _ -> demoted_to_canonical)
            ~name:(fun name ~coercion ->
              assert (Coercion.is_id coercion);
              let canonical = find_canonical typing_env name in
              if Simple.equal canonical simple
              then demoted_to_canonical
              else Demoted_to_canonical.add name ~canonical demoted_to_canonical))
        alias_set demoted_to_canonical)
    Demoted_to_canonical.empty classes

let join_joined_env ~meet_type ~central_env joined_envs =
  match joined_envs with
  | [] ->
    ( { typing_env = central_env;
        demoted_to_canonical = Demoted_to_canonical.empty;
        names_with_new_equation = Name.Set.empty
      },
      Cache.empty )
  | first_joined_env :: other_joined_envs ->
    let classes =
      Demoted_to_canonical.classes ~central_env
        first_joined_env.demoted_to_canonical
    in
    let classes =
      List.fold_left
        (fun classes other_joined_env ->
          partition_classes classes other_joined_env.typing_env)
        classes other_joined_envs
    in
    let typing_env = add_classes0 ~meet_type ~central_env ~classes in
    let demoted_to_canonical =
      demoted_to_canonical0 ~central_env:typing_env ~classes
    in
    let names_with_new_equation = first_joined_env.names_with_new_equation in
    let names_with_new_equation =
      List.fold_left
        (fun names_with_new_equation other_joined_env ->
          Name.Set.inter names_with_new_equation
            other_joined_env.names_with_new_equation)
        names_with_new_equation other_joined_envs
    in
    ( { typing_env; demoted_to_canonical; names_with_new_equation },
      make_cache0 ~central_env:typing_env ~classes )

module Joined_names = struct
  type simple_or_non_alias_type =
    | Nothing
    | Simple of Simple.t
    | Non_alias_type of TG.t

  let print_simple_or_non_alias_type ppf = function
    | Nothing -> Format.pp_print_string ppf "Bottom"
    | Simple simple -> Simple.print ppf simple
    | Non_alias_type ty -> TG.print ppf ty

  let apply_coercion_simple_or_non_alias_type sonat coercion =
    match sonat with
    | Nothing -> Nothing
    | Simple simple -> Simple (Simple.apply_coercion_exn simple coercion)
    | Non_alias_type ty -> Non_alias_type (TG.apply_coercion ty coercion)

  type simples =
    | Repeat of simple_or_non_alias_type
    | Cons of simple_or_non_alias_type * simples

  let print_simples ppf simples =
    let rec print ppf = function
      | Repeat sonat -> print_simple_or_non_alias_type ppf sonat
      | Cons (sonat, simples) ->
        Format.fprintf ppf "%a@ %a" print_simple_or_non_alias_type sonat print
          simples
    in
    Format.fprintf ppf "@[<hov 1>(%a)@]" print simples

  let rec apply_coercion_simples simples coercion =
    match simples with
    | Repeat sonat ->
      Repeat (apply_coercion_simple_or_non_alias_type sonat coercion)
    | Cons (sonat, simples) ->
      Cons
        ( apply_coercion_simple_or_non_alias_type sonat coercion,
          apply_coercion_simples simples coercion )

  type t =
    { lifted_symbols : Symbol.Set.t;
      joined_vars : simples Variable.Map.t
    }

  let is_empty t =
    Symbol.Set.is_empty t.lifted_symbols && Variable.Map.is_empty t.joined_vars

  let print ppf { lifted_symbols; joined_vars } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(imported_names@ @[%a@])@ @[<hov 1>(joined_vars@ \
       @[%a@])@])@]"
      Symbol.Set.print lifted_symbols
      (Variable.Map.print print_simples)
      joined_vars

  let empty =
    { lifted_symbols = Symbol.Set.empty; joined_vars = Variable.Map.empty }

  let import_symbol t symbol =
    let lifted_symbols = Symbol.Set.add symbol t.lifted_symbols in
    { t with lifted_symbols }

  let resolve t simple =
    Simple.pattern_match' simple
      ~const:(fun _ -> Repeat (Simple simple))
      ~symbol:(fun _ ~coercion:_ -> Repeat (Simple simple))
      ~var:(fun var ~coercion ->
        match Variable.Map.find_opt var t.joined_vars with
        | Some simples ->
          if Coercion.is_id coercion
          then simples
          else apply_coercion_simples simples coercion
        | None -> Repeat (Simple simple))

  let cons left right =
    match[@warning "-fragile-match"] left, right with
    | Simple left_simple, Repeat (Simple right_simple)
      when Simple.equal left_simple right_simple ->
      Repeat (Simple left_simple)
    | _ -> Cons (left, right)

  let create_join_var0 ?(raw_name = "join_var") (t, env) kind left right =
    let raw_name =
      ignore raw_name;
      "join_var"
    in
    let var_opt, existing_simple, info =
      match left, right with
      | Simple left_simple, Repeat (Simple right_simple)
        when Simple.equal left_simple right_simple ->
        let var_opt, existing_simple =
          Simple.pattern_match' left_simple
            ~const:(fun _ -> None, Some left_simple)
            ~symbol:(fun _ ~coercion:_ -> None, Some left_simple)
            ~var:(fun var ~coercion ->
              if Coercion.is_id coercion
              then Some var, Some (Simple.var var)
              else None, None)
        in
        var_opt, existing_simple, Repeat (Simple left_simple)
      | Nothing, Repeat (Simple right_simple) ->
        Simple.pattern_match' right_simple
          ~const:(fun _ ->
            None, Some right_simple, Repeat (Simple right_simple))
          ~symbol:(fun _ ~coercion:_ ->
            None, Some right_simple, Repeat (Simple right_simple))
          ~var:(fun _ ~coercion:_ -> None, None, cons left right)
      | Simple left_simple, Repeat Nothing ->
        Simple.pattern_match' left_simple
          ~const:(fun _ -> None, Some left_simple, Repeat (Simple left_simple))
          ~symbol:(fun _ ~coercion:_ ->
            None, Some left_simple, Repeat (Simple left_simple))
          ~var:(fun _ ~coercion:_ -> None, None, cons left right)
      | (Simple _ | Nothing | Non_alias_type _), (Cons _ | Repeat _) ->
        None, None, cons left right
    in
    match existing_simple with
    | Some existing_simple ->
      let t, env =
        match var_opt with
        | None -> t, env
        | Some var ->
          let env =
            if not (mem_name env (Name.var var))
            then
              TE.add_definition env
                (Bound_name.create_var
                   (Bound_var.create var Name_mode.in_types))
                kind
            else env
          in
          let joined_vars =
            Variable.Map.update var
              (function
                | None -> Some info
                | Some existing_info ->
                  assert (
                    match[@warning "-fragile-match"] existing_info with
                    | Repeat (Simple simple) ->
                      Simple.equal simple (Simple.var var)
                    | _ ->
                      Format.eprintf "while creating %a@." Variable.print var;
                      Format.eprintf "found info: %a@." print_simples
                        existing_info;
                      Format.eprintf "while setting info: %a@." print_simples
                        info;
                      false);
                  Some info)
              t.joined_vars
          in
          { t with joined_vars }, env
      in
      None, existing_simple, (t, env)
    | None ->
      let var = Variable.create raw_name in
      let joined_vars = Variable.Map.add var info t.joined_vars in
      let env =
        TE.add_definition env
          (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
          kind
      in
      Some var, Simple.var var, ({ t with joined_vars }, env)
end

module Join_env = struct
  type binary =
    { left_env : joined_env;
      target_env : joined_env;
      right_env : right_env;
      cache : Cache.t;
      joined_names : Joined_names.t
    }

  and unary =
    { joined_env : joined_env;
      target_env : joined_env;
      joined_names : Joined_names.t;
      renaming : Variable.t Variable.Map.t
    }

  and right_env =
    | Join_with_bottom of unary
    | Binary_join of binary

  let target_join_env (env : binary) = env.target_env.typing_env

  let joined_names = function
    | Join_with_bottom { joined_names; _ } -> joined_names
    | Binary_join { joined_names; _ } -> joined_names

  let left_join_env { left_env; _ } = left_env.typing_env

  let right_target_env = function
    | Join_with_bottom unary -> unary.target_env
    | Binary_join binary -> binary.target_env

  let right_typing_env = function
    | Join_with_bottom unary -> unary.target_env.typing_env
    | Binary_join binary -> binary.target_env.typing_env

  let right_join_env { right_env; _ } = right_typing_env right_env

  let resolve_in_typing_env env t =
    match get_alias_then_canonical_simple_exn env t with
    | exception Not_found ->
      if TG.is_obviously_bottom t
      then Joined_names.Nothing
      else Joined_names.Non_alias_type t
    | canonical_simple -> Joined_names.Simple canonical_simple

  let resolve_in_right_env env simple =
    match simple with
    | Joined_names.Nothing -> Joined_names.Repeat Joined_names.Nothing
    | Joined_names.Non_alias_type t ->
      (* XXX: This is wrong, we need to import names if [env] is a
         [Binary_join]. *)
      Joined_names.Repeat (Joined_names.Non_alias_type t)
    | Joined_names.Simple canonical_simple -> (
      match env with
      | Join_with_bottom _ -> Joined_names.Repeat (Simple canonical_simple)
      | Binary_join binary ->
        Joined_names.resolve binary.joined_names canonical_simple)

  let as_key = function
    | Joined_names.Nothing -> Some Or_bottom.Bottom
    | Joined_names.Non_alias_type _ -> None
    | Joined_names.Simple simple -> Some (Or_bottom.Ok simple)

  let join_type0 env kind t1 t2 : TG.t Or_unknown.t * binary =
    let left_simple = resolve_in_typing_env (left_join_env env) t1 in
    let right_simple = resolve_in_typing_env (right_join_env env) t2 in
    let key1 = as_key left_simple in
    let key2 = as_key right_simple in
    let canonical_var =
      match key1, key2 with
      | Some key1, Some key2 -> Cache.find_opt env.cache key1 key2
      | None, None | Some _, None | None, Some _ -> None
    in
    match canonical_var with
    | Some canonical_var ->
      assert (mem_name (target_join_env env) (Name.var canonical_var));
      Known (TG.alias_type_of kind (Simple.var canonical_var)), env
    | None ->
      let right_simples = resolve_in_right_env env.right_env right_simple in
      let joined_var_opt, joined_simple, (joined_names, target_env) =
        Joined_names.create_join_var0
          (env.joined_names, target_join_env env)
          kind left_simple right_simples
      in
      assert (mem_simple target_env joined_simple);
      let cache =
        match joined_var_opt, key1, key2 with
        | Some joined_var, Some key1, Some key2 ->
          assert (mem_name target_env (Name.var joined_var));
          snd (Cache.add ~name:joined_var env.cache key1 key2)
        | _ -> env.cache
      in
      let target_env = { env.target_env with typing_env = target_env } in
      ( Known (TG.alias_type_of kind joined_simple),
        { env with target_env; cache; joined_names } )

  type import_from =
    | Left_env
    | Right_env

  let as_simple key =
    match key with
    | Or_bottom.Ok simple -> Joined_names.Simple simple
    | Or_bottom.Bottom -> Joined_names.Nothing

  let import_var ~import_from env kind var =
    let left_key, right_key =
      match import_from with
      | Left_env -> Or_bottom.Ok (Simple.var var), Or_bottom.Bottom
      | Right_env -> Or_bottom.Bottom, Or_bottom.Ok (Simple.var var)
    in
    match Cache.find_opt env.cache left_key right_key with
    | Some canonical -> canonical, env
    | None ->
      let left_simple = as_simple left_key in
      let right_simple = as_simple right_key in
      let right_simples = resolve_in_right_env env.right_env right_simple in
      let var = Variable.create (Variable.raw_name var) in
      let target_env =
        TE.add_definition (target_join_env env)
          (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
          kind
      in
      let joined_vars =
        Variable.Map.add var
          (Joined_names.cons left_simple right_simples)
          env.joined_names.joined_vars
      in
      let joined_names = { env.joined_names with Joined_names.joined_vars } in
      let _, cache = Cache.add ~name:var env.cache left_key right_key in
      let target_env = { env.target_env with typing_env = target_env } in
      var, { env with joined_names; cache; target_env }

  let import_symbol env symbol =
    let joined_names = Joined_names.import_symbol env.joined_names symbol in
    { env with joined_names }

  let get_joined_names = joined_names

  let make ~meet_type target_env joined_envs =
    match joined_envs with
    | [] -> Or_bottom.Bottom
    | [joined_env] ->
      let target_env, _ =
        join_joined_env ~meet_type ~central_env:target_env [joined_env]
      in
      let joined_names =
        Name.Set.fold
          (fun name joined_names ->
            Name.pattern_match name
              ~symbol:(fun _ -> joined_names)
              ~var:(fun var ->
                let joined_vars =
                  Variable.Map.add var
                    (Joined_names.Repeat (Simple (Simple.var var)))
                    joined_names.Joined_names.joined_vars
                in
                { joined_names with Joined_names.joined_vars }))
          target_env.names_with_new_equation Joined_names.empty
      in
      let unary =
        { joined_env; target_env; joined_names; renaming = Variable.Map.empty }
      in
      Or_bottom.Ok (Join_with_bottom unary, target_env)
    | first_env :: (_ :: _ as other_envs) ->
      Or_bottom.Ok
        (List.fold_right
           (fun left_env (right_env, joined_env) ->
             let target_env, cache =
               join_joined_env ~meet_type ~central_env:target_env
                 [left_env; joined_env]
             in
             let joined_names =
               Name.Set.fold
                 (fun name joined_names ->
                   Name.pattern_match name
                     ~symbol:(fun _ -> joined_names)
                     ~var:(fun var ->
                       let right_simple =
                         Joined_names.resolve
                           (get_joined_names right_env)
                           (Simple.var var)
                       in
                       let joined_vars =
                         Variable.Map.add var
                           (Joined_names.cons
                              (Simple (Simple.var var))
                              right_simple)
                           joined_names.Joined_names.joined_vars
                       in
                       { joined_names with Joined_names.joined_vars }))
                 target_env.names_with_new_equation Joined_names.empty
             in
             ( Binary_join
                 { left_env; right_env; target_env; cache; joined_names },
               target_env ))
           other_envs
           ( Join_with_bottom
               { joined_env = first_env;
                 target_env = first_env;
                 joined_names = Joined_names.empty;
                 renaming = Variable.Map.empty
               },
             first_env ))

  let nary_join_type ~join_ty env types =
    let rec aux env types =
      match env with
      | Join_with_bottom unary -> (
        match types with
        | [ty] ->
          let names = TG.free_names ty in
          let renaming, target_env, joined_vars, cache =
            Name_occurrences.fold_names names
              ~init:
                ( Renaming.empty,
                  unary.target_env.typing_env,
                  unary.joined_names.joined_vars,
                  unary.renaming )
              ~f:(fun ((renaming, target_env, joined_vars, cache) as acc) name
                 ->
                let kind =
                  TG.kind (TE.find unary.joined_env.typing_env name None)
                in
                Name.pattern_match name
                  ~symbol:(fun _ -> acc)
                  ~var:(fun var ->
                    if mem_name target_env (Name.var var)
                    then acc
                    else
                      match Variable.Map.find_opt var cache with
                      | Some import_var ->
                        ( Renaming.add_variable renaming var import_var,
                          target_env,
                          joined_vars,
                          cache )
                      | None ->
                        let import_var =
                          Variable.create (Variable.raw_name var)
                        in
                        let target_env =
                          TE.add_definition target_env
                            (Bound_name.create_var
                               (Bound_var.create import_var Name_mode.in_types))
                            kind
                        in
                        let joined_vars =
                          Variable.Map.add import_var
                            (Joined_names.Repeat (Simple (Simple.var var)))
                            joined_vars
                        in
                        let cache = Variable.Map.add var import_var cache in
                        ( Renaming.add_variable renaming var import_var,
                          target_env,
                          joined_vars,
                          cache )))
          in
          let target_env = { unary.target_env with typing_env = target_env } in
          let joined_names = { unary.joined_names with joined_vars } in
          ( TG.apply_renaming ty renaming,
            Join_with_bottom
              { unary with target_env; joined_names; renaming = cache } )
        | [] | _ :: _ :: _ -> assert false)
      | Binary_join ({ right_env; _ } as binary_env) -> (
        match types with
        | [] -> assert false
        | left_ty :: right_types ->
          let joined_ty, right_env = aux right_env right_types in
          let joined_ty, binary_env =
            join_ty { binary_env with right_env } left_ty joined_ty
          in
          joined_ty, Binary_join binary_env)
    in
    aux env types

  let simple_or_non_alias_type_to_type env kind = function
    | Joined_names.Nothing -> ET.create_bottom kind
    | Joined_names.Simple simple ->
      Expand_head.expand_head env (TG.alias_type_of kind simple)
    | Joined_names.Non_alias_type ty -> Expand_head.expand_head env ty

  let rec repeat_simple_or_non_alias_type_to_type kind join_tree sonat =
    match join_tree with
    | Join_with_bottom unary ->
      [simple_or_non_alias_type_to_type unary.joined_env.typing_env kind sonat]
    | Binary_join binary_join ->
      simple_or_non_alias_type_to_type binary_join.left_env.typing_env kind
        sonat
      :: repeat_simple_or_non_alias_type_to_type kind binary_join.right_env
           sonat

  let rec simples_to_types kind join_tree simples =
    match join_tree, simples with
    | _, Joined_names.Repeat sonat ->
      repeat_simple_or_non_alias_type_to_type kind join_tree sonat
    | Binary_join binary_join, Joined_names.Cons (sonat, simples) ->
      simple_or_non_alias_type_to_type binary_join.left_env.typing_env kind
        sonat
      :: simples_to_types kind binary_join.right_env simples
    | Join_with_bottom _, Joined_names.Cons _ -> invalid_arg "simples_to_types"

  let map_target_env env f =
    match env with
    | Join_with_bottom unary ->
      Join_with_bottom
        { unary with
          target_env =
            { unary.target_env with typing_env = f unary.target_env.typing_env }
        }
    | Binary_join binary ->
      Binary_join
        { binary with
          target_env =
            { binary.target_env with
              typing_env = f binary.target_env.typing_env
            }
        }

  let nary_join ~meet_type ~join_ty ~already_joined env =
    let rec aux already_joined env =
      let to_join =
        Variable.Map.keys (joined_names env).Joined_names.joined_vars
      in
      let to_join_this_round = Variable.Set.diff to_join already_joined in
      if Variable.Set.is_empty to_join_this_round
      then env
      else
        let env =
          Variable.Set.fold
            (fun var env ->
              let joined_names = joined_names env in
              let kind =
                TG.kind (TE.find (right_typing_env env) (Name.var var) None)
              in
              let simples =
                Joined_names.resolve joined_names (Simple.var var)
              in
              let types = simples_to_types kind env simples in
              if List.for_all TG.is_obviously_bottom (List.map ET.to_type types)
              then (
                Format.eprintf "all bottom (for %a): %a@." Variable.print var
                  Joined_names.print_simples simples;
                assert false);
              let ty, env =
                nary_join_type ~join_ty env (List.map ET.to_type types)
              in
              map_target_env env (fun target_env ->
                  TE.add_equation target_env (Name.var var) ty ~meet_type))
            to_join_this_round env
        in
        aux to_join env
    in
    aux already_joined env
end

module Binary = struct
  type t = Join_env.binary

  let target_join_env binary = Join_env.target_join_env binary

  let left_join_env ({ left_env; _ } : t) = left_env.typing_env

  let right_join_env ({ right_env; _ } : t) =
    Join_env.right_typing_env right_env

  let cache ({ cache; _ } : t) = cache

  let with_cache (t : t) cache = { t with cache }

  let with_target_env (t : t) target_env =
    { t with target_env = { t.target_env with typing_env = target_env } }

  let with_joined_names (t : t) joined_names = { t with joined_names }

  let right_joined_names ({ right_env; _ } : t) =
    Join_env.joined_names right_env

  let joined_names ({ joined_names; _ } : t) = joined_names
end

module Superjoin = struct
  (* XXX: We are interested in names that have:

     - Changed in at least one extension, and

     - Changed in *all* the envs (since the central env) *)

  (* Recover the info in central env. *)
  let split1 ~central_env ~parent_env env equations =
    Name.Map.fold
      (fun name ty ((demoted_in_env, changed_in_extension) as acc) ->
        let exists_in_central_env = mem_name central_env name in
        let demoted_to_name =
          Demoted_to_canonical.get_demoted_to_canonical_name demoted_in_env name
        in
        let aliases_in_central_env =
          if exists_in_central_env
          then Map_to_canonical.add name ~coercion:Coercion.id demoted_to_name
          else demoted_to_name
        in
        if Map_to_canonical.is_empty aliases_in_central_env
        then acc
        else
          match TG.get_alias_exn ty with
          | alias ->
            let canonical_in_env = get_canonical_simple_exn env alias in
            let demoted_in_env =
              Demoted_to_canonical.merge ~demoted_name:name
                ~canonical:canonical_in_env demoted_in_env
            in
            let demoted_in_env =
              if exists_in_central_env
              then
                Demoted_to_canonical.add name ~canonical:canonical_in_env
                  demoted_in_env
              else demoted_in_env
            in
            let changed_in_extension =
              Name.Map.fold
                (fun name_in_central_env _ changed_in_extension ->
                  Name.Set.add name_in_central_env changed_in_extension)
                aliases_in_central_env changed_in_extension
            in
            demoted_in_env, changed_in_extension
          | exception Not_found ->
            (* We are adding a non-alias type equation, which can only happen if
               [name] is canonical in [env]. *)
            if Flambda_features.check_light_invariants ()
            then
              assert (Simple.equal (find_canonical env name) (Simple.name name));
            (* If the name is an existential from [env], any name in
               [central_env] it applies to will have been demoted somehow.

               If the name exists in the [parent_env], the type refines the type
               of all its aliases in [central_env]. *)
            let changed_in_extension =
              Name.Map.fold
                (fun name _ canonical_equations ->
                  Name.Set.add name canonical_equations)
                aliases_in_central_env changed_in_extension
            in
            demoted_in_env, changed_in_extension)
      equations
      (parent_env.demoted_to_canonical, Name.Set.empty)

  let construct_joined_env ~central_env ~parent_env env equations =
    let demoted_in_env, changed_in_extension =
      split1 ~central_env ~parent_env env equations
    in
    let changed_in_env =
      Name.Set.union changed_in_extension parent_env.names_with_new_equation
    in
    ( { typing_env = env;
        demoted_to_canonical = demoted_in_env;
        names_with_new_equation = changed_in_env
      },
      changed_in_extension )

  let joinit0 ~meet_type ~join_ty central_env extended_envs =
    let join_ty env left right =
      let left = Expand_head.expand_head (Binary.left_join_env env) left in
      let right = Expand_head.expand_head (Binary.right_join_env env) right in
      if Flambda_features.debug_flambda2 ()
      then
        Format.eprintf "join of: (%a) and (%a)@ " TG.print (ET.to_type left)
          TG.print (ET.to_type right);
      let ty, env = join_ty env (ET.to_type left) (ET.to_type right) in
      match ty with
      | Or_unknown.Unknown ->
        if Flambda_features.debug_flambda2 () then Format.eprintf "unknown!@ ";
        MTC.unknown_like (ET.to_type left), env
      | Or_unknown.Known ty ->
        if Flambda_features.debug_flambda2 ()
        then (
          Format.eprintf "join of: (%a) and (%a)@ " TG.print (ET.to_type left)
            TG.print (ET.to_type right);
          Format.eprintf "is: %a@ " TG.print ty);
        ty, env
    in
    let changed_in_any_extension = ref Name.Set.empty in
    let joined_extensions =
      List.map
        (fun (parent_env, env, equations) ->
          let extension_joined_env, changed_in_extension =
            construct_joined_env ~central_env ~parent_env env equations
          in
          changed_in_any_extension
            := Name.Set.union changed_in_extension !changed_in_any_extension;
          extension_joined_env)
        extended_envs
    in
    let scope = TE.current_scope central_env in
    let initial_env = central_env in
    let central_env = TE.increment_scope central_env in
    match Join_env.make ~meet_type central_env joined_extensions with
    | Bottom -> assert false
    | Ok (join_env', shared_env') ->
      assert (
        Scope.equal
          (TE.current_scope shared_env'.typing_env)
          (TE.current_scope central_env));
      let ext = TE.cut shared_env'.typing_env ~cut_after:scope in
      if Flambda_features.debug_flambda2 ()
      then
        if not (TEL.is_empty ext)
        then
          Format.eprintf "shared aliases from %d environments: %a@."
            (List.length joined_extensions)
            TEL.print ext;
      assert (
        Name.Set.equal shared_env'.names_with_new_equation
          shared_env'.names_with_new_equation);
      let to_join =
        Variable.Map.keys
          (Join_env.joined_names join_env').Joined_names.joined_vars
      in
      let already_joined =
        Variable.Set.filter
          (fun var ->
            not (Name.Set.mem (Name.var var) !changed_in_any_extension))
          to_join
      in
      let central_env = shared_env'.typing_env in
      let join_env' =
        Join_env.nary_join ~meet_type ~join_ty ~already_joined join_env'
      in
      let level =
        TE.cut (Join_env.right_typing_env join_env') ~cut_after:scope
      in
      assert (
        Scope.equal
          (TE.current_scope (Join_env.right_typing_env join_env'))
          (TE.current_scope central_env));
      let final_env =
        TE.add_env_extension_from_level initial_env level ~meet_type
      in
      final_env, level

  let joinit ~meet_type ~join_ty central_env envs_with_equations =
    let parent_env =
      { typing_env = central_env;
        demoted_to_canonical = Demoted_to_canonical.empty;
        names_with_new_equation = Name.Set.empty
      }
    in
    joinit0 ~meet_type ~join_ty central_env
      (List.map (fun (env, eqn) -> parent_env, env, eqn) envs_with_equations)

  let join_env_extensions ~meet_type ~join_ty central_env envs_with_extensions =
    let env, _ =
      joinit ~meet_type ~join_ty central_env
        (List.map (fun (t, te) -> t, te.TG.equations) envs_with_extensions)
    in
    env

  let dodoblahdo ~meet_type ~join_ty central_env envs_with_levels =
    let out, _ =
      joinit ~meet_type ~join_ty central_env
        (List.map (fun (t, level) -> t, TEL.equations level) envs_with_levels)
    in
    out
end

let join_binary_env_extensions ~meet_type ~join_ty join_env left_ext right_ext =
  (* TODO: We need to make sure we do not join again things we were already
     joining. *)
  let central_env = Binary.target_join_env join_env in
  let left_parent_env = Binary.left_join_env join_env in
  let right_parent_env = Binary.right_join_env join_env in
  let left_scope = TE.current_scope left_parent_env in
  let left_env = TE.increment_scope left_parent_env in
  let left_env = TE.add_env_extension ~meet_type left_env left_ext in
  let left_ext = TE.cut_as_extension left_env ~cut_after:left_scope in
  let right_scope = TE.current_scope right_parent_env in
  let right_env = TE.increment_scope right_parent_env in
  let right_env = TE.add_env_extension ~meet_type right_env right_ext in
  let right_ext = TE.cut_as_extension right_env ~cut_after:right_scope in
  let right_joined_env =
    match join_env.Join_env.right_env with
    | Join_with_bottom { target_env; _ } -> target_env
    | Binary_join { target_env; _ } -> target_env
  in
  let _, level =
    Superjoin.joinit0 ~meet_type ~join_ty central_env
      [ join_env.Join_env.left_env, left_env, left_ext.TG.equations;
        right_joined_env, right_env, right_ext.TG.equations ]
  in
  let ext = TEL.as_extension_with_extra_variables level in
  let central_env, equations =
    TEE.With_extra_variables.fold
      ~variable:(fun var kind (env, equations) ->
        ( TE.add_definition env
            (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
            kind,
          equations ))
      ~equation:(fun name ty (env, equations) ->
        ( env,
          if TG.is_obviously_unknown ty
          then equations
          else Name.Map.add name ty equations ))
      ext
      (central_env, Name.Map.empty)
  in
  let ext = TG.Env_extension.create ~equations in
  Binary.with_target_env join_env central_env, ext
