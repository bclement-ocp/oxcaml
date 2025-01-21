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

module Trie : sig
  type 'a t

  val print :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  val empty : 'a t

  val iter : (Simple.t list -> 'a -> unit) -> 'a t -> unit

  val fold : (Simple.t list -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val add : 'a t -> Simple.t list -> 'a -> 'a t

  val find : 'a t -> Simple.t list -> 'a
end = struct
  type 'a t =
    | Value of 'a
    | Map of 'a t Simple.Map.t

  let rec iter f trie =
    match trie with
    | Value v -> f [] v
    | Map m ->
      Simple.Map.iter
        (fun simple sub -> iter (fun rest v -> f (simple :: rest) v) sub)
        m

  let rec fold f trie acc =
    match trie with
    | Value v -> f [] v acc
    | Map m ->
      Simple.Map.fold
        (fun simple sub acc -> fold (fun rest -> f (simple :: rest)) sub acc)
        m acc

  let is_empty trie =
    match trie with Map m -> Simple.Map.is_empty m | Value _ -> false

  let print pp ppf trie =
    if is_empty trie
    then Format.fprintf ppf "{}"
    else (
      Format.fprintf ppf "@[<hv 1>{";
      let first = ref true in
      iter
        (fun args datum ->
          if !first then first := false else Format.fprintf ppf "@ ";
          Format.fprintf ppf "@[<hov 1>(@[<hov 1>(%a)@]@ %a)@]"
            (Format.pp_print_list ~pp_sep:Format.pp_print_space Simple.print)
            args pp datum)
        trie;
      Format.fprintf ppf "}@]")

  let empty = Map Simple.Map.empty

  let rec find t inputs =
    match t, inputs with
    | Value v, [] -> v
    | Value _, _ :: _ -> invalid_arg "Trie.find"
    | Map _, [] -> invalid_arg "Trie.find"
    | Map m, first_input :: other_inputs ->
      find (Simple.Map.find first_input m) other_inputs

  let rec singleton inputs v =
    match inputs with
    | [] -> Value v
    | first_input :: other_inputs ->
      Map (Simple.Map.singleton first_input (singleton other_inputs v))

  let rec add t inputs v =
    match t, inputs with
    | Value _, [] -> Value v
    | Value _, _ :: _ -> invalid_arg "Trie.add"
    | Map _, [] -> invalid_arg "Trie.add"
    | Map m, first_input :: other_inputs ->
      Map
        (Simple.Map.update first_input
           (function
             | None -> Some (singleton other_inputs v)
             | Some t' -> Some (add t' other_inputs v))
           m)
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

let make_trie0 ~central_env ~classes =
  List.fold_left
    (fun trie (alias_set, shared_names) ->
      let trie =
        match Alias_set.choose alias_set with
        | Some alias ->
          assert (mem_simple central_env alias);
          let the_canonical = get_canonical_simple_exn central_env alias in
          Simple.pattern_match the_canonical
            ~const:(fun _ -> trie)
            ~name:(fun name ~coercion ->
              assert (Coercion.is_id coercion);
              if List.for_all (Simple.equal the_canonical) shared_names
              then trie
              else Trie.add trie (List.rev shared_names) name)
        | None -> trie
      in
      trie)
    Trie.empty classes

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
      Trie.empty )
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
      make_trie0 ~central_env:typing_env ~classes )

module Binary = struct
  type join_simple =
    | Join_simples of Simple.t Or_bottom.t * Simple.t Or_bottom.t
    | Join_types of TG.t * TG.t

  type t =
    { central_env : TE.t;
      left_join_env : joined_env;
      right_join_env : joined_env;
      trie : Name.t Trie.t;
          (* Map from pairs of canonicals in the left and right environment to
             the corresponding canonical in the central environment.

             No entry if the canonicals are the same in both environments. *)
      join_at_next_depth : (K.t * join_simple) Name.Map.t
    }

  let target_join_env { central_env; _ } = central_env

  let left_join_env { left_join_env; _ } = left_join_env.typing_env

  let right_join_env { right_join_env; _ } = right_join_env.typing_env

  let import_name ~meet_type t kind name =
    let exists_in_central_env = mem_name t.central_env name in
    let central_env =
      if not exists_in_central_env
      then
        TE.add_definition t.central_env
          (Bound_name.create name Name_mode.in_types)
          kind
      else t.central_env
    in
    let exists_in_left_env = mem_name (left_join_env t) name in
    let exists_in_right_env = mem_name (right_join_env t) name in
    let left_canonical =
      if exists_in_left_env
      then Or_bottom.Ok (find_canonical (left_join_env t) name)
      else Or_bottom.Bottom
    in
    let right_canonical =
      if exists_in_right_env
      then Or_bottom.Ok (find_canonical (right_join_env t) name)
      else Or_bottom.Bottom
    in
    (* TODO: if the name exists in the central env and is not updated in neither
       left nor right we do not need to join its type. *)
    let join_at_next_depth =
      Name.Map.add name
        (kind, Join_simples (left_canonical, right_canonical))
        t.join_at_next_depth
    in
    match left_canonical, right_canonical with
    | Ok left_canonical, Ok right_canonical -> (
      match Trie.find t.trie [left_canonical; right_canonical] with
      | canonical ->
        (* No need to add the entry to [join_at_next_depth]: we already have a
           name for this pair of canonicals. *)
        let central_env =
          if Name.equal name canonical
          then central_env
          else
            TE.add_equation central_env name ~meet_type
              (TG.alias_type_of kind (Simple.name canonical))
        in
        { t with central_env }
      | exception Not_found ->
        let trie = Trie.add t.trie [left_canonical; right_canonical] name in
        { t with central_env; trie; join_at_next_depth })
    | (Ok _ | Bottom), (Ok _ | Bottom) ->
      { t with central_env; join_at_next_depth }

  let now_joining_simple ~meet_type t kind left_simple right_simple :
      Simple.t Or_unknown.t * t =
    assert (
      (not (mem_simple (left_join_env t) left_simple))
      || Simple.equal left_simple
           (get_canonical_simple_exn (left_join_env t) left_simple));
    assert (
      (not (mem_simple (right_join_env t) right_simple))
      || Simple.equal right_simple
           (get_canonical_simple_exn (right_join_env t) right_simple));
    if Simple.equal left_simple right_simple
    then
      Simple.pattern_match left_simple
        ~const:(fun _ -> Or_unknown.Known left_simple, t)
        ~name:(fun name ~coercion:_ ->
          (* TODO: if the name exists in the central env and is not updated in
             neither left nor right we do not need to join its type. *)
          let join_at_next_depth =
            Name.Map.add name
              (kind, Join_simples (Ok (Simple.name name), Ok (Simple.name name)))
              t.join_at_next_depth
          in
          let central_env =
            if mem_name t.central_env name
            then t.central_env
            else
              TE.add_definition t.central_env
                (Bound_name.create name Name_mode.in_types)
                kind
          in
          let central_env, join_at_next_depth =
            match Trie.find t.trie [Simple.name name; Simple.name name] with
            | central_name ->
              if Name.equal name central_name
              then central_env, t.join_at_next_depth
              else
                ( TE.add_equation central_env name ~meet_type
                    (TG.alias_type_of kind (Simple.name central_name)),
                  t.join_at_next_depth )
            | exception Not_found -> central_env, join_at_next_depth
          in
          ( Or_unknown.Known left_simple,
            { t with central_env; join_at_next_depth } ))
    else
      match Trie.find t.trie [left_simple; right_simple] with
      | canonical -> Or_unknown.Known (Simple.name canonical), t
      | exception Not_found ->
        let raw_name =
          Simple.pattern_match right_simple
            ~const:(fun _ ->
              Simple.pattern_match' left_simple
                ~const:(fun _ -> "cte")
                ~var:(fun var ~coercion:_ -> Variable.raw_name var)
                ~symbol:(fun _ ~coercion:_ -> "join_var"))
            ~name:(fun right_name ~coercion:_ ->
              Simple.pattern_match' left_simple
                ~const:(fun _ ->
                  Name.pattern_match right_name ~var:Variable.raw_name
                    ~symbol:(fun _ -> "join_var"))
                ~var:(fun left_var ~coercion:_ ->
                  Name.pattern_match right_name
                    ~var:(fun right_var ->
                      let left_raw_name = Variable.raw_name left_var in
                      let right_raw_name = Variable.raw_name right_var in
                      if String.equal left_raw_name right_raw_name
                      then left_raw_name
                      else "join_var")
                    ~symbol:(fun _ -> "join_var"))
                ~symbol:(fun _ ~coercion:_ -> "join_var"))
        in
        let name = Name.var (Variable.create raw_name) in
        if Flambda_features.debug_flambda2 ()
        then
          Format.eprintf "Creating %a = (%a, %a)@." Name.print name Simple.print
            left_simple Simple.print right_simple;
        let join_at_next_depth =
          Name.Map.add name
            ( kind,
              Join_simples (Or_bottom.Ok left_simple, Or_bottom.Ok right_simple)
            )
            t.join_at_next_depth
        in
        let central_env =
          TE.add_definition t.central_env
            (Bound_name.create name Name_mode.in_types)
            kind
        in
        ( Or_unknown.Known (Simple.name name),
          { t with central_env; join_at_next_depth } )

  let now_joining_types ~meet_type t kind left_ty right_ty :
      TG.t Or_unknown.t * t =
    (* TODO: check kind *)
    match
      ( get_alias_then_canonical_simple_exn (left_join_env t) left_ty,
        get_alias_then_canonical_simple_exn (right_join_env t) right_ty )
    with
    | left_canonical, right_canonical ->
      let simple_ou, t =
        now_joining_simple ~meet_type t kind left_canonical right_canonical
      in
      Or_unknown.map ~f:(TG.alias_type_of kind) simple_ou, t
    | exception Not_found ->
      let name = Name.var (Variable.create "anon") in
      let join_at_next_depth =
        Name.Map.add name
          (kind, Join_types (left_ty, right_ty))
          t.join_at_next_depth
      in
      let central_env =
        TE.add_definition t.central_env
          (Bound_name.create name Name_mode.in_types)
          kind
      in
      ( Or_unknown.Known (TG.alias_type_of kind (Simple.name name)),
        { t with central_env; join_at_next_depth } )
end

module Superjoin = struct
  type join_simple =
    | Import_simple of Simple.t
    | Import_type of TG.t
    | Join_simples of Simple.t Or_bottom.t * join_simple
    | Join_type of TG.t * join_simple

  let join_simple simple simples =
    match simple, simples with
    | Or_bottom.Ok simple1, Import_simple simple2
      when Simple.equal simple1 simple2 ->
      simples
    | Or_bottom.Ok simple1, Import_type ty2 -> (
      match TG.get_alias_opt ty2 with
      | Some simple2 when Simple.equal simple1 simple2 -> simples
      | _ -> Join_type (TG.alias_type_of (TG.kind ty2) simple1, simples))
    | Or_bottom.Bottom, (Import_simple _ | Import_type _) -> simples
    | ( (Or_bottom.Ok _ | Or_bottom.Bottom),
        (Import_simple _ | Join_simples _ | Join_type _) ) ->
      Join_simples (simple, simples)

  let join_type ty simples =
    match TG.get_alias_opt ty with
    | Some simple -> join_simple (Ok simple) simples
    | None -> Join_type (ty, simples)

  let rec map_join_simple ~simple ~type_ = function
    | Import_simple simple0 -> Import_simple (simple simple0)
    | Import_type ty -> Import_type (type_ ty)
    | Join_simples (simple_ob, join_simples) ->
      join_simple
        (Or_bottom.map ~f:simple simple_ob)
        (map_join_simple ~simple ~type_ join_simples)
    | Join_type (ty, join_simples) ->
      join_type (type_ ty) (map_join_simple ~simple ~type_ join_simples)

  let rec equal_join_simple j1 j2 =
    match j1, j2 with
    | Import_simple n1, Import_simple n2 -> Simple.equal n1 n2
    | Import_type ty1, Import_type ty2 -> (
      match TG.get_alias_exn ty1, TG.get_alias_exn ty2 with
      | simple1, simple2 -> Simple.equal simple1 simple2
      | exception Not_found -> false)
    | Join_simples (simple1, rest1), Join_simples (simple2, rest2) ->
      (match simple1, simple2 with
      | Or_bottom.Ok a, Or_bottom.Ok b -> Simple.equal a b
      | Or_bottom.Ok _, Or_bottom.Bottom | Or_bottom.Bottom, Or_bottom.Ok _ ->
        false
      | Or_bottom.Bottom, Or_bottom.Bottom -> true)
      && equal_join_simple rest1 rest2
    | Join_type (ty1, rest1), Join_type (ty2, rest2) -> (
      match TG.get_alias_exn ty1, TG.get_alias_exn ty2 with
      | simple1, simple2 ->
        Simple.equal simple1 simple2 && equal_join_simple rest1 rest2
      | exception Not_found -> false)
    | ( (Import_simple _ | Join_simples _ | Join_type _ | Import_type _),
        (Import_simple _ | Join_simples _ | Join_type _ | Import_type _) ) ->
      false

  let rec print_join_simple ppf j =
    match j with
    | Import_simple n ->
      Format.fprintf ppf "@[<hov 1>(import@ %a)@]" Simple.print n
    | Import_type ty -> Format.fprintf ppf "@[<hov 1>(import@ %a)@]" TG.print ty
    | Join_simples (simple, rest) ->
      Format.fprintf ppf "@[<hov 1>(join@ %a@ %a)@]"
        (Or_bottom.print Simple.print)
        simple print_join_simple rest
    | Join_type (ty, rest) ->
      Format.fprintf ppf "@[<hov 1>(join@ %a@ %a)@]" TG.print ty
        print_join_simple rest

  type t =
    { central_env : TE.t;
      joined_envs : joined_env list;
      join_at_next_depth : join_simple Name.Map.t
    }

  type joined_simple =
    | Same_simple of Simple.t
    | Simple_in_left_env of Simple.t * joined_simple

  let rec equal_joined_simple a b =
    match a, b with
    | Same_simple a, Same_simple b -> Simple.equal a b
    | Simple_in_left_env (a1, a2), Same_simple b1 ->
      Simple.equal a1 b1 && equal_joined_simple a2 b
    | Simple_in_left_env (a1, a2), Simple_in_left_env (b1, b2) ->
      Simple.equal a1 b1 && equal_joined_simple a2 b2
    | Same_simple a1, Simple_in_left_env (b1, b2) ->
      Simple.equal a1 b1 && equal_joined_simple a b2

  let rec map_joined_simples f = function
    | Same_simple simple -> Same_simple (f simple)
    | Simple_in_left_env (simple, rest) ->
      Simple_in_left_env (f simple, map_joined_simples f rest)

  let rec all_joined_simples f = function
    | Same_simple simple -> f simple
    | Simple_in_left_env (simple, rest) -> f simple && all_joined_simples f rest

  let print_joined_simples ppf joined =
    let rec pp ppf joined =
      match joined with
      | Same_simple simple -> Format.fprintf ppf "%a..." Simple.print simple
      | Simple_in_left_env (left, right) ->
        Format.fprintf ppf "%a@ %a" Simple.print left pp right
    in
    Format.fprintf ppf "@[<hov 1>(%a)@]" pp joined

  module T = struct
    type binary_join_adapter =
      | Join_with_bottom of joined_env
      | Binary_join of
          { left_env : joined_env;
            right_env : joined_env;
            trie : Name.t Trie.t;
            recursive_join : binary_join_adapter
          }

    let print_joined_env ppf joined_env = TE.print ppf joined_env.typing_env

    let rec print_binary_join_adapter ppf bja =
      match bja with
      | Join_with_bottom joined_env -> print_joined_env ppf joined_env
      | Binary_join { left_env; right_env = _; trie = _; recursive_join } ->
        Format.fprintf ppf "(join@ @[%a@]@ @[%a@])" print_joined_env left_env
          print_binary_join_adapter recursive_join

    let make_binary_join_adapter ~meet_type central_env joined_envs =
      match joined_envs with
      | [] -> Or_bottom.Bottom
      | [joined_env] ->
        let shared_env, _ =
          join_joined_env ~meet_type ~central_env [joined_env]
        in
        Or_bottom.Ok (shared_env, Join_with_bottom joined_env)
      | first_env :: (_ :: _ as other_envs) ->
        Or_bottom.Ok
          (List.fold_right
             (fun left_env (right_env, adapter) ->
               (* central_env + shared eqn *)
               let shared_env, trie =
                 join_joined_env ~meet_type ~central_env [left_env; right_env]
               in
               ( shared_env,
                 Binary_join
                   { left_env; right_env; trie; recursive_join = adapter } ))
             other_envs
             (first_env, Join_with_bottom first_env))

    let rec loop ~join_ty central_env adapter types =
      match adapter, types with
      | Join_with_bottom left_env, [ty] ->
        let names = TG.free_names ty in
        let central_env, to_join =
          Name_occurrences.fold_names names ~init:(central_env, Name.Map.empty)
            ~f:(fun (central_env, to_join_next) name ->
              let kind = TG.kind (TE.find left_env.typing_env name None) in
              let to_join =
                Name.Map.add name
                  (kind, Import_type (TG.alias_type_of kind (Simple.name name)))
                  to_join_next
              in
              let central_env =
                if mem_name central_env name
                then central_env
                else
                  TE.add_definition central_env
                    (Bound_name.create name Name_mode.in_types)
                    kind
              in
              central_env, to_join)
        in
        ty, central_env, Join_with_bottom left_env, Name.Map.empty, to_join
      | Join_with_bottom _, ([] | _ :: _ :: _) -> assert false
      | ( Binary_join
            { left_env = left_join_env;
              right_env = right_join_env;
              trie;
              recursive_join = adapter
            },
          left_ty :: other_types ) ->
        (* [n] is the depth of [adapter] *)
        let ( joined_ty,
              right_typing_env,
              adapter,
              _right_joined_names,
              right_join_at_next_depth ) =
          loop ~join_ty right_join_env.typing_env adapter other_types
        in
        let right_join_env =
          { right_join_env with typing_env = right_typing_env }
        in
        let binary_join_env =
          { Binary.central_env;
            left_join_env;
            right_join_env;
            trie;
            join_at_next_depth = Name.Map.empty
          }
        in
        let joined_ty, result_env = join_ty binary_join_env left_ty joined_ty in
        let left_join_env0 = left_join_env in
        let right_join_env0 = right_join_env in
        let { Binary.central_env;
              left_join_env;
              right_join_env;
              trie;
              join_at_next_depth
            } =
          result_env
        in
        assert (left_join_env == left_join_env0);
        assert (right_join_env == right_join_env0);
        let join_next_depth =
          Name.Map.map
            (fun (kind, binary_join) ->
              match binary_join with
              | Binary.Join_types (left_ty, right_ty) -> (
                match TG.get_alias_opt right_ty with
                | None -> kind, join_type left_ty (Import_type right_ty)
                | Some right_simple ->
                  let right_simple =
                    get_canonical_simple_exn right_join_env.typing_env
                      right_simple
                  in
                  Simple.pattern_match right_simple
                    ~const:(fun _ ->
                      ( kind,
                        join_type left_ty
                          (Import_type (TG.alias_type_of kind right_simple)) ))
                    ~name:(fun right_name ~coercion ->
                      match
                        Name.Map.find right_name right_join_at_next_depth
                      with
                      | _, right_simples ->
                        let right_simples =
                          if Coercion.is_id coercion
                          then right_simples
                          else
                            map_join_simple
                              ~simple:(fun simple ->
                                Simple.apply_coercion_exn simple coercion)
                              ~type_:(fun ty -> TG.apply_coercion ty coercion)
                              right_simples
                        in
                        kind, join_type left_ty right_simples
                      | exception Not_found ->
                        if Flambda_features.debug_flambda2 ()
                        then
                          Format.eprintf "Forcing right import of %a@."
                            Simple.print right_simple;
                        ( kind,
                          join_type left_ty
                            (Import_type (TG.alias_type_of kind right_simple)) ))
                )
              | Binary.Join_simples (left_simple_ob, right_simple_ob) -> (
                match left_simple_ob, right_simple_ob with
                | Or_bottom.Bottom, Or_bottom.Bottom -> assert false
                | Or_bottom.Ok left_simple, Or_bottom.Bottom ->
                  kind, Import_type (TG.alias_type_of kind left_simple)
                | left_simple, Or_bottom.Ok right_simple ->
                  let left_simple =
                    match left_simple with
                    | Or_bottom.Bottom ->
                      if mem_simple left_join_env.typing_env right_simple
                      then Or_bottom.Ok right_simple
                      else left_simple
                    | Or_bottom.Ok _ -> left_simple
                  in
                  Simple.pattern_match right_simple
                    ~const:(fun _ ->
                      ( kind,
                        join_simple left_simple
                          (Import_type (TG.alias_type_of kind right_simple)) ))
                    ~name:(fun right_name ~coercion ->
                      if Flambda_features.debug_flambda2 ()
                      then Format.eprintf "expanding %a@." Name.print right_name;
                      match
                        Name.Map.find right_name right_join_at_next_depth
                      with
                      | _, right_simples ->
                        let right_simples =
                          if Coercion.is_id coercion
                          then right_simples
                          else
                            map_join_simple
                              ~simple:(fun simple ->
                                Simple.apply_coercion_exn simple coercion)
                              ~type_:(fun ty -> TG.apply_coercion ty coercion)
                              right_simples
                        in
                        if Flambda_features.debug_flambda2 ()
                        then
                          Format.eprintf "into: %a@." print_join_simple
                            right_simples;
                        kind, join_simple left_simple right_simples
                      | exception Not_found ->
                        if Flambda_features.debug_flambda2 ()
                        then (
                          Format.eprintf "not (%d)? %a@."
                            (List.length other_types) Simple.print right_simple;
                          Format.eprintf "Forcing right import of %a@."
                            Simple.print right_simple);
                        ( kind,
                          join_simple left_simple
                            (Import_type (TG.alias_type_of kind right_simple)) ))
                ))
            join_at_next_depth
        in
        ( joined_ty,
          central_env,
          Binary_join
            { left_env = left_join_env;
              right_env = right_join_env;
              trie;
              recursive_join = adapter
            },
          Name.Map.empty,
          join_next_depth )
      | Binary_join _, [] -> assert false

    type nary =
      { central_env : TE.t;
        joined_envs : binary_join_adapter;
        join_at_next_depth : (K.t * join_simple) Name.Map.t;
        depth : int
      }

    let do_one ~join_ty nary types =
      if List.length types >= 1
      then
        if Flambda_features.debug_flambda2 ()
        then
          Format.eprintf "going for %d types: @[<v>%a@]@." (List.length types)
            (Format.pp_print_list TG.print)
            types;
      let ty, central_env, bja, _, join_at_next_depth =
        loop ~join_ty nary.central_env nary.joined_envs types
      in
      let join_at_next_depth =
        Name.Map.union
          (fun _ (kind, a) (_kind, b) ->
            if not (equal_join_simple a b)
            then (
              Format.eprintf "@[<2>@[<hov 1>(%a) <>@ @[<hov 1>(%a)@]@."
                print_join_simple a print_join_simple b;
              assert false);
            Some (kind, a))
          join_at_next_depth nary.join_at_next_depth
      in
      Name.Map.iter
        (fun name _ -> assert (mem_name central_env name))
        join_at_next_depth;
      ( ty,
        { central_env;
          joined_envs = bja;
          join_at_next_depth;
          depth = nary.depth
        } )

    let rec resolve_simples joined kind simples =
      match joined with
      | Join_with_bottom left_env -> (
        match simples with
        | Import_simple simple ->
          Simple.pattern_match simple
            ~const:(fun _ -> [TG.alias_type_of kind simple])
            ~name:(fun name ~coercion ->
              let ty =
                if mem_name left_env.typing_env name
                then
                  TG.apply_coercion
                    (TE.find left_env.typing_env name (Some kind))
                    coercion
                else (
                  if Flambda_features.debug_flambda2 ()
                  then
                    Format.eprintf "NO TYPE for %a; BOTTOM for %a@." Name.print
                      name Name.print name;
                  MTC.bottom kind)
              in
              [ty])
        | Import_type ty -> (
          match TG.get_alias_opt ty with
          | Some simple ->
            if mem_simple left_env.typing_env simple
            then [ET.to_type (Expand_head.expand_head left_env.typing_env ty)]
            else [MTC.bottom kind]
          | None -> [ty])
        | Join_type _ -> assert false
        | Join_simples _ -> assert false)
      | Binary_join { left_env; right_env = _; trie = _; recursive_join } -> (
        match simples with
        | Import_type _ | Join_type _ ->
          let ty, other_simples =
            match simples with
            | Import_type ty -> ty, Import_type ty
            | Join_type (ty, simples) -> ty, simples
            | Import_simple _ | Join_simples _ -> assert false
          in
          let ty =
            match TG.get_alias_opt ty with
            | Some simple ->
              if mem_simple left_env.typing_env simple
              then ET.to_type (Expand_head.expand_head left_env.typing_env ty)
              else MTC.bottom kind
            | None -> ty
          in
          ty :: resolve_simples recursive_join kind other_simples
        | (Import_simple _ | Join_simples _) as simples ->
          let this_simple, other_simples =
            match simples with
            | Import_simple simple -> Or_bottom.Ok simple, Import_simple simple
            | Join_simples (left_simple, right_simples) ->
              left_simple, right_simples
            | Import_type _ | Join_type _ -> assert false
          in
          let ty =
            match this_simple with
            | Or_bottom.Bottom -> MTC.bottom kind
            | Or_bottom.Ok this_simple ->
              if mem_simple left_env.typing_env this_simple
              then
                ET.to_type
                  (Expand_head.expand_head left_env.typing_env
                     (TG.alias_type_of kind this_simple))
              else MTC.bottom kind
          in
          ty :: resolve_simples recursive_join kind other_simples)

    let rec fixpoint ~meet_type ~join_ty already_joined nary =
      let join_at_this_depth = nary.join_at_next_depth in
      let join_at_this_depth =
        Name.Map.filter
          (fun name _ -> not (Name.Set.mem name already_joined))
          join_at_this_depth
      in
      if Name.Map.is_empty join_at_this_depth
      then nary
      else
        let already_joined =
          Name.Set.union already_joined (Name.Map.keys join_at_this_depth)
        in
        let nary =
          Name.Map.fold
            (fun name (kind, simples) nary ->
              let types = resolve_simples nary.joined_envs kind simples in
              if Flambda_features.debug_flambda2 ()
              then
                Format.eprintf "resolving %a: @[<h>(%a)@]@." Name.print name
                  print_join_simple simples;
              if List.for_all TG.is_obviously_bottom types
              then (
                Format.eprintf "all bottom (for %a): %a@." Name.print name
                  print_join_simple simples;
                assert false);
              let ty, nary = do_one ~join_ty nary types in
              match TG.get_alias_exn ty with
              | alias ->
                if not
                     (Simple.equal
                        (get_canonical_simple_exn nary.central_env alias)
                        (find_canonical nary.central_env name))
                then (
                  if Flambda_features.debug_flambda2 ()
                  then
                    Format.eprintf "learned a new equality: %a = %a@."
                      Name.print name Simple.print alias;
                  let central_env =
                    TE.add_equation nary.central_env name ty ~meet_type
                  in
                  { nary with central_env })
                else nary
              | exception Not_found ->
                if Flambda_features.debug_flambda2 ()
                then
                  Format.eprintf "join next (after %d): %a@." nary.depth
                    Name.Set.print
                    (Name.Map.keys nary.join_at_next_depth);
                Name.Map.iter
                  (fun name _ -> assert (mem_name nary.central_env name))
                  nary.join_at_next_depth;
                if Flambda_features.debug_flambda2 ()
                then
                  Format.eprintf "adding: %a = %a@." Name.print name TG.print ty;
                let central_env =
                  TE.add_equation nary.central_env name ty ~meet_type
                in
                { nary with central_env })
            join_at_this_depth
            { nary with
              join_at_next_depth = Name.Map.empty;
              depth = nary.depth + 1
            }
        in
        fixpoint ~meet_type ~join_ty already_joined nary
  end

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
    match
      T.make_binary_join_adapter ~meet_type central_env joined_extensions
    with
    | Bottom -> assert false
    | Ok (shared_env, bja) ->
      assert (
        Scope.equal
          (TE.current_scope shared_env.typing_env)
          (TE.current_scope central_env));
      let ext = TE.cut shared_env.typing_env ~cut_after:scope in
      if Flambda_features.debug_flambda2 ()
      then
        if not (TEL.is_empty ext)
        then
          Format.eprintf "shared aliases from %d environments: %a@."
            (List.length joined_extensions)
            TEL.print ext;
      let to_consider =
        Name.Set.inter !changed_in_any_extension
          shared_env.names_with_new_equation
      in
      if Flambda_features.debug_flambda2 ()
      then Format.eprintf "Names to consider: %a@ " Name.Set.print to_consider;
      let central_env = shared_env.typing_env in
      let nary =
        { T.central_env;
          joined_envs = bja;
          join_at_next_depth =
            Name.Set.fold
              (fun name join_at_next_depth ->
                let kind = TG.kind (TE.find central_env name None) in
                Name.Map.add name
                  (kind, Import_type (TG.alias_type_of kind (Simple.name name)))
                  join_at_next_depth)
              to_consider Name.Map.empty;
          depth = 0
        }
      in
      let nary = T.fixpoint ~meet_type ~join_ty Name.Set.empty nary in
      assert (
        Scope.equal
          (TE.current_scope nary.central_env)
          (TE.current_scope central_env));
      let level = TE.cut nary.central_env ~cut_after:scope in
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
    let env, level =
      joinit ~meet_type ~join_ty central_env
        (List.map (fun (t, te) -> t, te.TG.equations) envs_with_extensions)
    in
    env, TEL.as_extension_without_bindings level

  let dodoblahdo ~meet_type ~join_ty central_env envs_with_levels =
    let out, outl =
      joinit ~meet_type ~join_ty central_env
        (List.map (fun (t, level) -> t, TEL.equations level) envs_with_levels)
    in
    ignore outl;
    out
end

let join_binary_env_extensions0 ~meet_type ~join_ty join_env left_ext right_ext
    =
  (* TODO: We need to make sure we do not join again things we were already
     joining. *)
  let central_env = join_env.Binary.central_env in
  let left_parent_env = join_env.Binary.left_join_env in
  let right_parent_env = join_env.Binary.right_join_env in
  let left_scope = TE.current_scope left_parent_env.typing_env in
  let left_env = TE.increment_scope left_parent_env.typing_env in
  let left_env = TE.add_env_extension ~meet_type left_env left_ext in
  let left_ext = TE.cut_as_extension left_env ~cut_after:left_scope in
  let right_scope = TE.current_scope right_parent_env.typing_env in
  let right_env = TE.increment_scope right_parent_env.typing_env in
  let right_env = TE.add_env_extension ~meet_type right_env right_ext in
  let right_ext = TE.cut_as_extension right_env ~cut_after:right_scope in
  let _, level =
    Superjoin.joinit0 ~meet_type ~join_ty central_env
      [ left_parent_env, left_env, left_ext.TG.equations;
        right_parent_env, right_env, right_ext.TG.equations ]
  in
  let ext = TEL.as_extension level in
  let central_env =
    TEL.fold_on_defined_vars
      (fun var kind env ->
        TE.add_definition env
          (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
          kind)
      level central_env
  in
  let equations =
    Name.Map.filter
      (fun _ ty -> not (TG.is_obviously_unknown ty))
      ext.TG.equations
  in
  let ext = TG.Env_extension.create ~equations in
  { join_env with Binary.central_env }, ext

let join_binary_env_extensions ~meet_type ~join_ty join_env left_ext right_ext =
  if true
  then (
    let pouet_env, candidate_ext =
      join_binary_env_extensions0 ~meet_type ~join_ty join_env left_ext
        right_ext
    in
    if TEE.is_empty left_ext && TEE.is_empty right_ext
       && not (TEE.is_empty candidate_ext)
    then (
      Format.eprintf "@[<v>JOIN OF EMPTIES:@ %a@]@." TEE.print candidate_ext;
      Format.eprintf "@[%a@]@." (Trie.print Name.print) join_env.Binary.trie;
      Format.eprintf "@[<v>CENTRAL:@ %a@]@." TE.print
        join_env.Binary.central_env;
      Format.eprintf "@[<v>LEFT:@ %a@]@." TE.print
        join_env.Binary.left_join_env.typing_env;
      Format.eprintf "@[<v>RIGHT:@ %a@]@." TE.print
        join_env.Binary.right_join_env.typing_env;
      assert false);
    if (not (TEE.is_empty candidate_ext)) && Flambda_features.debug_flambda2 ()
    then (
      Format.eprintf "@[<v 2>LOSING JOIN OF:@ @[<v>%a@]@ AND:@ @[<v>%a@]@]@."
        TEE.print left_ext TEE.print right_ext;
      Format.eprintf "@[%a@]@." TEE.print candidate_ext;
      Format.eprintf "@[%a@]@." (Trie.print Name.print) join_env.Binary.trie;
      Name.Map.iter
        (fun name _ty ->
          let canonical =
            TE.get_canonical_simple_exn join_env.Binary.left_join_env.typing_env
              (Simple.name name)
          in
          let to_canonical =
            Demoted_to_canonical.get_demoted_to_canonical_element
              join_env.Binary.left_join_env.demoted_to_canonical canonical
          in
          Format.eprintf "@[Aliases of %a: %a@]@." Name.print name
            Name.Set.print
            (Name.Map.keys to_canonical);
          ())
        left_ext.TG.equations;
      Name.Map.iter
        (fun name _ty ->
          let canonical =
            TE.get_canonical_simple_exn
              join_env.Binary.right_join_env.typing_env (Simple.name name)
          in
          let to_canonical =
            Demoted_to_canonical.get_demoted_to_canonical_element
              join_env.Binary.right_join_env.demoted_to_canonical canonical
          in
          Format.eprintf "@[Aliases of %a: %a@]@." Name.print name
            Name.Set.print
            (Name.Map.keys to_canonical);
          ())
        right_ext.TG.equations);
    pouet_env, candidate_ext)
  else
    join_binary_env_extensions0 ~meet_type ~join_ty join_env left_ext right_ext
