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
      ~name:(fun name ~coercion:_ ->
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

module Aliases_of_canonical_element = struct
  type t = Coercion.t Name.Map.t

  let empty = Name.Map.empty

  let is_empty m = Name.Map.is_empty m

  let to_map m = m

  let of_map m = m
end

module Trie = struct
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

type joined_env =
  { typing_env : TE.t;
    demoted_to_canonical : Demoted_to_canonical.t;
        (** Names that have been demoted in this env. *)
    changed_equations : Name.Set.t
        (** Names whose type has changed compared to the central env. *)
  }

let join_joined_env ~meet_type ~central_env joined_envs =
  match joined_envs with
  | [] -> assert false
  | first_joined_env :: other_joined_envs ->
    let classes =
      Demoted_to_canonical.classes ~central_env
        first_joined_env.demoted_to_canonical
    in
    let changed_equations = first_joined_env.changed_equations in
    let classes, changed_equations =
      List.fold_left
        (fun (classes, changed_equations) other_joined_env ->
          let classes =
            List.concat_map
              (fun (alias_set, other_simples) ->
                let partition =
                  Alias_set.fold
                    (fun alias partition ->
                      let canonical_in_other_env =
                        if mem_simple other_joined_env.typing_env alias
                        then
                          get_canonical_simple_exn other_joined_env.typing_env
                            alias
                        else alias
                      in
                      Simple.Map.update canonical_in_other_env
                        (function
                          | None -> Some (Alias_set.singleton alias)
                          | Some alias_set_in_other_env ->
                            Some (Alias_set.add alias alias_set_in_other_env))
                        partition)
                    alias_set Simple.Map.empty
                in
                Simple.Map.fold
                  (fun this_canonical alias_set partition ->
                    (alias_set, this_canonical :: other_simples) :: partition)
                  partition [])
              classes
          in
          ( classes,
            Name.Set.inter changed_equations other_joined_env.changed_equations
          ))
        (classes, changed_equations)
        other_joined_envs
    in
    let typing_env, demoted_to_canonical, trie =
      List.fold_left
        (fun (typing_env, demoted_to_canonical, trie) (alias_set, shared_names) ->
          let typing_env =
            Alias_set.fold_equations
              (fun name alias typing_env ->
                let kind = TG.kind (TE.find central_env name None) in
                let alias_ty = TG.alias_type_of kind alias in
                TE.add_equation typing_env name alias_ty ~meet_type)
              alias_set typing_env
          in
          let demoted_to_canonical =
            Alias_set.fold
              (fun simple demoted_to_canonical ->
                Simple.pattern_match simple
                  ~const:(fun _ -> demoted_to_canonical)
                  ~name:(fun name ~coercion:_ ->
                    let canonical = find_canonical typing_env name in
                    if Simple.equal canonical simple
                    then demoted_to_canonical
                    else
                      Demoted_to_canonical.add name ~canonical
                        demoted_to_canonical))
              alias_set demoted_to_canonical
          in
          let the_canonical =
            match Alias_set.choose alias_set with
            | Some alias -> get_canonical_simple_exn typing_env alias
            | None -> assert false
          in
          let trie =
            Simple.pattern_match the_canonical
              ~const:(fun _ -> trie)
              ~name:(fun name ~coercion ->
                assert (Coercion.is_id coercion);
                if List.for_all (Simple.equal the_canonical) shared_names
                then trie
                else Trie.add trie (List.rev shared_names) name)
          in
          typing_env, demoted_to_canonical, trie)
        (central_env, Demoted_to_canonical.empty, Trie.empty)
        classes
    in
    let joined_names =
      Trie.fold
        (fun simples name joined_names ->
          Name.Map.add name simples joined_names)
        trie Name.Map.empty
    in
    { typing_env; demoted_to_canonical; changed_equations }, trie, joined_names

let aliases_in_central_env ~central_env demoted name =
  let demoted_to_name =
    Demoted_to_canonical.get_demoted_to_canonical_name demoted name
  in
  if mem_name central_env name
  then Map_to_canonical.add name ~coercion:Coercion.id demoted_to_name
  else demoted_to_name

let aliases_in_central_env' ~central_env demoted simple =
  let demoted =
    Demoted_to_canonical.get_demoted_to_canonical_element demoted simple
  in
  Simple.pattern_match simple
    ~const:(fun _ -> demoted)
    ~name:(fun name ~coercion ->
      assert (Coercion.is_id coercion);
      if mem_simple central_env simple
      then Map_to_canonical.add name ~coercion demoted
      else demoted)

module Binary = struct
  type t =
    { central_env : TE.t;
      left_join_env : joined_env;
      right_join_env : joined_env;
      trie : Name.t Trie.t;
          (* Map from pairs of canonicals in the left and right environment to
             the corresponding canonical in the central environment.

             No entry if the canonicals are the same in both environments. *)
      join_at_next_depth : (K.t * Simple.t * Simple.t) Name.Map.t
    }

  let target_join_env { central_env; _ } = central_env

  let left_join_env { left_join_env; _ } = left_join_env.typing_env

  let right_join_env { right_join_env; _ } = right_join_env.typing_env

  let now_joining_simple t kind left_simple right_simple :
      Simple.t Or_unknown.t * t =
    (* XXX: importing is broken if the name is not canonical!!! *)
    if Simple.equal left_simple right_simple
    then
      Simple.pattern_match left_simple
        ~const:(fun _ -> Or_unknown.Known left_simple, t)
        ~name:(fun name ~coercion:_ ->
          if mem_name t.central_env name
          then Or_unknown.Known left_simple, t
          else
            let join_at_next_depth =
              Name.Map.add name
                (kind, Simple.name name, Simple.name name)
                t.join_at_next_depth
            in
            let central_env =
              TE.add_definition t.central_env
                (Bound_name.create name Name_mode.in_types)
                kind
            in
            ( Or_unknown.Known left_simple,
              { t with central_env; join_at_next_depth } ))
    else
      match Trie.find t.trie [left_simple; right_simple] with
      | canonical -> Or_unknown.Known (Simple.name canonical), t
      | exception Not_found ->
        let reuse_name =
          Simple.pattern_match right_simple
            ~const:(fun _ -> None)
            ~name:(fun name ~coercion ->
              assert (Coercion.is_id coercion);
              if not (mem_name t.left_join_env.typing_env name)
              then Some name
              else None)
        in
        let left_ty =
          Simple.pattern_match left_simple ~const:MTC.type_for_const
            ~name:(fun name ~coercion:_ ->
              TE.find t.left_join_env.typing_env name None)
        in
        let right_ty =
          Simple.pattern_match right_simple ~const:MTC.type_for_const
            ~name:(fun name ~coercion:_ ->
              TE.find t.right_join_env.typing_env name None)
        in
        let name =
          ignore reuse_name;
          (* match reuse_name with | Some name -> name | None -> *)
          Name.var (Variable.create "join_var")
        in
        let join_at_next_depth =
          Name.Map.add name
            (kind, left_simple, right_simple)
            t.join_at_next_depth
        in
        if Flambda_features.debug_flambda2 ()
        then (
          let left_ali =
            aliases_in_central_env' ~central_env:t.central_env
              t.left_join_env.demoted_to_canonical left_simple
          in
          let right_ali =
            aliases_in_central_env' ~central_env:t.central_env
              t.right_join_env.demoted_to_canonical right_simple
          in
          Format.eprintf "creating: %a for (%a[%b] : %a, %a[%b] : %a)@."
            Name.print name Simple.print left_simple
            (TG.is_obviously_unknown left_ty)
            TG.print left_ty Simple.print right_simple
            (TG.is_obviously_unknown right_ty)
            TG.print right_ty;
          Format.eprintf "left aliases: %a@ right aliases: %a@." Name.Set.print
            (Name.Map.keys left_ali) Name.Set.print (Name.Map.keys right_ali));
        let central_env =
          TE.add_definition t.central_env
            (Bound_name.create name Name_mode.in_types)
            kind
        in
        ( Or_unknown.Known (Simple.name name),
          { t with central_env; join_at_next_depth } )
end

module Superjoin = struct
  type t =
    { central_env : TE.t;
      joined_envs : joined_env list;
      join_at_next_depth : Simple.t list Name.Map.t
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
      | Same_simple simple -> Simple.print ppf simple
      | Simple_in_left_env (left, right) ->
        Format.fprintf ppf "%a@ %a" Simple.print left pp right
    in
    Format.fprintf ppf "@[<hov 1>(%a)@]" pp joined

  module T = struct
    type binary_join_adapter =
      | Bottom_env of joined_env
      | Binary_join of
          { left_env : joined_env;
            right_env : joined_env;
            trie : Name.t Trie.t;
            recursive_join : binary_join_adapter
          }

    let print_joined_env ppf joined_env = TE.print ppf joined_env.typing_env

    let rec print_binary_join_adapter ppf bja =
      match bja with
      | Bottom_env _ -> Format.fprintf ppf "⊥"
      | Binary_join { left_env; right_env = _; trie = _; recursive_join } ->
        Format.fprintf ppf "(join@ @[%a@]@ @[%a@])" print_joined_env left_env
          print_binary_join_adapter recursive_join

    let make_binary_join_adapter ~meet_type central_env joined_envs =
      List.fold_right
        (fun left_env acc ->
          match acc with
          | Or_bottom.Bottom ->
            (* This is the first env. *)
            Or_bottom.Ok
              ( left_env (* join_joined_env ~meet_type ~central_env [left_env] *),
                Name.Map.empty,
                Bottom_env left_env )
          | Or_bottom.Ok (right_env, right_joined_names, adapter) ->
            (* central_env + shared eqn *)
            let shared_env, trie, _joined_names =
              join_joined_env ~meet_type ~central_env [left_env; right_env]
            in
            let new_joined_names =
              Trie.fold
                (fun simples name new_trie ->
                  match simples with
                  | [left_simple; right_simple] ->
                    let right_simples =
                      Simple.pattern_match right_simple
                        ~const:(fun _ -> Same_simple right_simple)
                        ~name:(fun name ~coercion:_ ->
                          try Name.Map.find name right_joined_names
                          with Not_found -> Same_simple right_simple)
                    in
                    Name.Map.add name
                      (Simple_in_left_env (left_simple, right_simples))
                      new_trie
                  | _ -> assert false)
                trie Name.Map.empty
            in
            Or_bottom.Ok
              ( shared_env,
                new_joined_names,
                Binary_join
                  { left_env; right_env; trie; recursive_join = adapter } ))
        joined_envs Or_bottom.Bottom

    let rec loop ~join_ty central_env adapter types =
      match adapter, types with
      | Bottom_env left_env, [ty] ->
        let names = TG.free_names ty in
        let central_env, to_join =
          Name_occurrences.fold_names names ~init:(central_env, Name.Map.empty)
            ~f:(fun (central_env, to_join_next) name ->
              let kind = TG.kind (TE.find left_env.typing_env name None) in
              let to_join =
                Name.Map.add name
                  (kind, Same_simple (Simple.name name))
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
        ty, central_env, Bottom_env left_env, Name.Map.empty, to_join
      | Bottom_env _, _ -> assert false
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
        let { Binary.central_env;
              left_join_env;
              right_join_env;
              trie;
              join_at_next_depth
            } =
          result_env
        in
        let join_next_depth =
          Name.Map.map
            (fun (kind, left_simple, right_simple) ->
              if Simple.equal left_simple right_simple
              then (
                assert (mem_simple central_env left_simple);
                kind, Same_simple left_simple)
              else
                Simple.pattern_match right_simple
                  ~const:(fun _ ->
                    ( kind,
                      Simple_in_left_env (left_simple, Same_simple right_simple)
                    ))
                  ~name:(fun right_name ~coercion ->
                    match Name.Map.find right_name right_join_at_next_depth with
                    | _, right_simples ->
                      let right_simples =
                        if Coercion.is_id coercion
                        then right_simples
                        else
                          map_joined_simples
                            (fun simple ->
                              Simple.apply_coercion_exn simple coercion)
                            right_simples
                      in
                      kind, Simple_in_left_env (left_simple, right_simples)
                    | exception Not_found -> kind, Same_simple right_simple))
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
        join_at_next_depth : (K.t * joined_simple) Name.Map.t
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
            assert (equal_joined_simple a b);
            Some (kind, a))
          join_at_next_depth nary.join_at_next_depth
      in
      Name.Map.iter
        (fun name _ -> assert (mem_name central_env name))
        join_at_next_depth;
      ty, { central_env; joined_envs = bja; join_at_next_depth }

    let rec resolve_simples joined kind simples =
      match joined with
      | Bottom_env left_env -> (
        match simples with
        | Same_simple simple ->
          let ty =
            Simple.pattern_match simple
              ~const:(fun const -> MTC.type_for_const const)
              ~name:(fun name ~coercion ->
                if mem_name left_env.typing_env name
                then
                  let ty = TE.find left_env.typing_env name None in
                  let ty =
                    match TG.get_alias_exn ty with
                    | alias when Simple.is_const alias -> ty
                    | _ | (exception Not_found) ->
                      let et = Expand_head.expand_head left_env.typing_env ty in
                      ET.to_type et
                  in
                  TG.apply_coercion ty coercion
                else MTC.bottom kind)
          in
          [ty]
        | Simple_in_left_env _ -> assert false)
      | Binary_join { left_env; right_env = _; trie = _; recursive_join } ->
        let this_simple, other_simples =
          match simples with
          | Same_simple simple -> simple, simples
          | Simple_in_left_env (left_simple, right_simples) ->
            left_simple, right_simples
        in
        let ty =
          Simple.pattern_match this_simple
            ~const:(fun const -> MTC.type_for_const const)
            ~name:(fun name ~coercion ->
              if mem_name left_env.typing_env name
              then
                let ty = TE.find left_env.typing_env name None in
                let ty =
                  match TG.get_alias_exn ty with
                  | alias when Simple.is_const alias -> ty
                  | _ | (exception Not_found) ->
                    let et = Expand_head.expand_head left_env.typing_env ty in
                    ET.to_type et
                in
                TG.apply_coercion ty coercion
              else MTC.bottom kind)
        in
        ty :: resolve_simples recursive_join kind other_simples

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
                  Format.eprintf "join next: %a@." Name.Set.print
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
            { nary with join_at_next_depth = Name.Map.empty }
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
      Name.Set.union changed_in_extension parent_env.changed_equations
    in
    ( { typing_env = env;
        demoted_to_canonical = demoted_in_env;
        changed_equations = changed_in_env
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
        then Format.eprintf "known = %a@ " TG.print ty;
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
    | Ok (shared_env, _joined, bja) ->
      let shared_env, _trie, _join =
        join_joined_env ~meet_type ~central_env [shared_env]
      in
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
        Name.Set.inter !changed_in_any_extension shared_env.changed_equations
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
                  (kind, Same_simple (Simple.name name))
                  join_at_next_depth)
              to_consider Name.Map.empty
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
        changed_equations = Name.Set.empty
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

let join_binary_env_extensions ~meet_type ~join_ty join_env left_ext right_ext =
  let central_env = join_env.Binary.central_env in
  let left_parent_env = join_env.Binary.left_join_env in
  let right_parent_env = join_env.Binary.right_join_env in
  let left_env =
    TE.add_env_extension ~meet_type left_parent_env.typing_env left_ext
  in
  let right_env =
    TE.add_env_extension ~meet_type right_parent_env.typing_env right_ext
  in
  let _, level =
    Superjoin.joinit0 ~meet_type ~join_ty central_env
      [ left_parent_env, left_env, left_ext.TG.equations;
        right_parent_env, right_env, right_ext.TG.equations ]
  in
  TEL.as_extension level
