module TG = Type_grammar

type 'a or_gone =
  | There of 'a
  | Gone

let print_or_gone pp ppf = function
  | Gone -> Format.fprintf ppf "<gone>"
  | There x -> pp ppf x

let relation_for_const (rel : TG.Relation.t) const : _ Or_bottom.t =
  match rel with
  | Is_null -> (
    match Reg_width_const.is_tagged_immediate const with
    | None -> Bottom
    | Some _ -> Ok (Reg_width_const.naked_immediate Targetint_31_63.zero))
  | Is_int -> (
    match Reg_width_const.is_tagged_immediate const with
    | None -> Bottom
    | Some _ -> Ok (Reg_width_const.naked_immediate Targetint_31_63.one))
  | Get_tag -> Bottom

module type Abelian_set = sig
  type t

  type elt

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val diff : t -> t -> t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val print : Format.formatter -> t -> unit
end

module Int_abelian_set : Abelian_set with type t = int and type elt = unit =
struct
  type t = int

  type elt = unit

  let empty = 0

  let is_empty n = n = 0

  let mem () n = n > 0

  let add () n = n + 1

  let singleton () = 1

  let remove () n = n - 1

  let union n1 n2 = n1 + n2

  let diff n1 n2 = n1 - n2

  let compare = Numeric_types.Int.compare

  let equal = Numeric_types.Int.equal

  let print = Numeric_types.Int.print
end

module ZRel (Key : Container_types.S) (ZSet : Abelian_set) :
  Abelian_set with type t = ZSet.t Key.Map.t and type elt = Key.t * ZSet.elt =
struct
  type t = ZSet.t Key.Map.t

  type elt = Key.t * ZSet.elt

  let empty = Key.Map.empty

  let is_empty = Key.Map.is_empty

  let mem (elt1, elt2) zrel =
    match Key.Map.find_opt elt1 zrel with
    | None -> false
    | Some zset -> ZSet.mem elt2 zset

  let norm zset = if ZSet.is_empty zset then None else Some zset

  let update elt1 f zrel =
    Key.Map.update elt1
      (fun zset -> norm (f (Option.value ~default:ZSet.empty zset)))
      zrel

  let add (elt1, elt2) zrel = update elt1 (ZSet.add elt2) zrel

  let singleton (elt1, elt2) = Key.Map.singleton elt1 (ZSet.singleton elt2)

  let remove (elt1, elt2) zrel = update elt1 (ZSet.remove elt2) zrel

  let union zrel1 zrel2 =
    Key.Map.union
      (fun _ zset1 zset2 -> norm (ZSet.union zset1 zset2))
      zrel1 zrel2

  let diff zrel1 zrel2 =
    Key.Map.merge
      (fun _ zset1 zset2 ->
        norm
          (ZSet.diff
             (Option.value ~default:ZSet.empty zset1)
             (Option.value ~default:ZSet.empty zset2)))
      zrel1 zrel2

  let compare = Key.Map.compare ZSet.compare

  let equal = Key.Map.equal ZSet.equal

  let print = Key.Map.print ZSet.print
end

module ZSet (Key : Container_types.S) :
  Abelian_set with type t = int Key.Map.t and type elt = Key.t = struct
  include ZRel (Key) (Int_abelian_set)

  type elt = Key.t

  let mem elt zset = mem (elt, ()) zset

  let add elt zset = add (elt, ()) zset

  let singleton elt = singleton (elt, ())

  let remove elt zset = remove (elt, ()) zset
end

module ZRel2 (Key1 : Container_types.S) (Key2 : Container_types.S) :
  Abelian_set
    with type t = ZSet(Key2).t Key1.Map.t
     and type elt = Key1.t * Key2.t =
  ZRel (Key1) (ZSet (Key2))

module Unary_function0 (Key : Container_types.S) (Value : Container_types.S) =
struct
  include ZRel2 (Key) (Value)

  let find_opt key t =
    match Key.Map.find_opt key t with
    | None -> None
    | Some values -> (
      match Value.Map.get_singleton values with
      | Some (value, 1) -> Some value
      | _ -> Misc.fatal_error "Ill-formed.")

  let remove key value t = remove (key, value) t

  let add key value t = add (key, value) t

  let replace key ~existing_value value t =
    let t = remove key existing_value t in
    add key value t

  let concat ~earlier ~later = union earlier later
end

module Function = Unary_function0 (Name) (Simple)
module Inverse = ZRel2 (Name) (Name)

type 'a incremental =
  { current : 'a;
    difference : 'a
  }

module Incremental0 = struct
  let find_opt ~find_opt key t = find_opt key t.current

  let replace ~find_opt ~add ~replace key value t =
    match find_opt key t.current with
    | None ->
      let current = add key value t.current in
      let difference = add key value t.difference in
      { current; difference }
    | Some existing_value ->
      let current = replace key ~existing_value value t.current in
      let difference = replace key ~existing_value value t.difference in
      { current; difference }
end

type 'a meet_return_value =
  | Left_input
  | Right_input
  | Both_inputs
  | New_result of 'a

let map_return_value f (x : _ meet_return_value) =
  match x with
  | Left_input -> Left_input
  | Right_input -> Right_input
  | Both_inputs -> Both_inputs
  | New_result x -> New_result (f x)

let generic_meet_then_add ~replace ~meet ~existing_value key value env t :
    _ Or_bottom.t =
  match meet env value existing_value with
  | Or_bottom.Bottom -> Bottom
  | Or_bottom.Ok (meet_value, env) -> (
    match (meet_value : _ meet_return_value) with
    | Right_input | Both_inputs -> Ok (t, env)
    | Left_input -> Ok (replace key value t, env)
    | New_result value -> Ok (replace key value t, env))

let generic_add ~find_opt ~replace ~meet key value env t : _ Or_bottom.t =
  match find_opt key t with
  | None ->
    (* TODO: [add] *)
    Ok (replace key value t, env)
  | Some existing_value ->
    generic_meet_then_add ~replace ~meet ~existing_value key value env t

module Row_like = struct
  type 'a case = 'a Or_bottom.t

  let print_case pp = Or_bottom.print pp

  let meet_case ~meet (env : 'b) (case1 : 'a case) (case2 : 'a case) :
      'a case meet_return_value * 'b =
    match case1, case2 with
    | Bottom, Bottom -> Both_inputs, env
    | Bottom, _ -> Left_input, env
    | _, Bottom -> Right_input, env
    | Ok case1, Ok case2 -> (
      match meet env case1 case2 with
      | Or_bottom.Bottom -> New_result Or_bottom.Bottom, env
      | Or_bottom.Ok (case, env) ->
        let case = map_return_value (fun case -> Or_bottom.Ok case) case in
        case, env)

  type 'a t =
    { known : 'a Reg_width_const.Map.t;
      other : 'a Or_bottom.t
    }

  let print_known pp ppf known = Reg_width_const.Map.print pp ppf known

  let print pp ppf { known; other } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(known@ %a)@]@ @[<hov 1>(other@ %a)@]@]"
      (print_known pp) known (print_case pp) other

  let extract_value res left right =
    match res with
    | Left_input -> left
    | Right_input -> right
    | Both_inputs -> left
    | New_result value -> value

  let meet ~meet env { known = known1; other = other1 }
      { known = known2; other = other2 } =
    let result_is_left = ref true in
    let result_is_right = ref true in
    let update_refs = function
      | Both_inputs -> ()
      | Left_input -> result_is_right := false
      | Right_input -> result_is_left := false
      | New_result _ ->
        result_is_left := false;
        result_is_right := false
    in
    let other, env = meet_case ~meet env other1 other2 in
    update_refs other;
    let other = extract_value other other1 other2 in
    let env_ref = ref env in
    let known =
      Reg_width_const.Map.merge
        (fun _ case1 case2 ->
          let case1 =
            match case1 with None -> other1 | Some case1 -> Or_bottom.Ok case1
          in
          let case2 =
            match case2 with None -> other2 | Some case2 -> Or_bottom.Ok case2
          in
          let case, env = meet_case ~meet !env_ref case1 case2 in
          env_ref := env;
          update_refs case;
          match extract_value case case1 case2 with
          | Bottom -> None
          | Ok case -> Some case)
        known1 known2
    in
    let env = !env_ref in
    match !result_is_left, !result_is_right with
    | true, true -> Both_inputs, env
    | true, false -> Left_input, env
    | false, true -> Right_input, env
    | false, false -> New_result { known; other }, env

  let find const { known; other } =
    match Reg_width_const.Map.find_opt const known with
    | None -> other
    | Some case -> Or_bottom.Ok case
end
[@@warning "-32"]

module Aliases0 = struct
  type t =
    { aliases : Aliases.t;
      demotions : Simple.t Name.Map.t
    }

  let meet ~binding_time_resolver ~binding_times_and_modes t simple1 simple2 =
    if Simple.equal simple1 simple2
    then Or_bottom.Ok (Both_inputs, t)
    else
      let find_canonical simple =
        Simple.pattern_match simple
          ~const:(fun _ -> simple)
          ~name:(fun name ~coercion ->
            Simple.apply_coercion_exn
              (Aliases.get_canonical_ignoring_name_mode t.aliases name)
              coercion)
      in
      let canonical_element1 = find_canonical simple1 in
      let canonical_element2 = find_canonical simple2 in
      let return t canonical_element =
        if Simple.equal canonical_element simple2
        then Or_bottom.Ok (Right_input, t)
        else if Simple.equal canonical_element simple1
        then Or_bottom.Ok (Left_input, t)
        else Or_bottom.Ok (New_result canonical_element, t)
      in
      if Simple.equal canonical_element1 canonical_element2
      then return t canonical_element1
      else
        match
          Aliases.add ~binding_time_resolver ~binding_times_and_modes t.aliases
            ~canonical_element1 ~canonical_element2
        with
        | Ok { canonical_element; alias_of_demoted_element; t = aliases } ->
          let demotions =
            Simple.pattern_match alias_of_demoted_element
              ~const:(fun _ ->
                Misc.fatal_error "Unexpected demotion of constant")
              ~name:(fun name ~coercion ->
                Name.Map.add name
                  (Simple.apply_coercion_exn canonical_element
                     (Coercion.inverse coercion))
                  t.demotions)
          in
          return { aliases; demotions } canonical_element
        | Bottom -> Or_bottom.Bottom

  exception Bottom_equation

  let rebuild ~demotions ~binding_time_resolver ~binding_times_and_modes f t acc
      =
    let meet = meet ~binding_time_resolver ~binding_times_and_modes in
    match
      Name.Map.fold
        (fun to_be_demoted canonical_at_demotion (acc, t) ->
          let canonical_element =
            Simple.pattern_match canonical_at_demotion
              ~const:(fun _ -> canonical_at_demotion)
              ~name:(fun name ~coercion ->
                Simple.apply_coercion_exn
                  (Aliases.get_canonical_ignoring_name_mode t.aliases name)
                  coercion)
          in
          match f ~to_be_demoted ~canonical_element ~meet t acc with
          | Or_bottom.Bottom -> raise Bottom_equation
          | Or_bottom.Ok (acc, t) -> acc, t)
        demotions (acc, t)
    with
    | acc, t -> Or_bottom.Ok (acc, t)
    | exception Bottom_equation -> Or_bottom.Bottom
end

module Z_lattice (Key : Container_types.S) = struct
  type 'a t = 'a or_gone Key.Map.t

  let find_opt key t =
    match Key.Map.find_opt key t with
    | None | Some Gone -> None
    | Some (There value) -> Some value

  let add key value t = Name.Map.add key (There value) t

  let replace name ~existing_value:_ value t = add name value t

  let remove name t = Key.Map.add name Gone t
end

module Z_lattice_on_names = Z_lattice (Name)

let find_z_lattice_on_names =
  Incremental0.find_opt ~find_opt:Z_lattice_on_names.find_opt

let remove_z_lattice_on_names name _value t =
  let current = Z_lattice_on_names.remove name t.current in
  let difference = Z_lattice_on_names.remove name t.difference in
  { current; difference }

let add_z_lattice_on_names ~meet name value env t =
  generic_add ~find_opt:find_z_lattice_on_names
    ~replace:
      (Incremental0.replace ~find_opt:Z_lattice_on_names.find_opt
         ~add:Z_lattice_on_names.add ~replace:Z_lattice_on_names.replace)
    ~meet name value env t

module Final = struct
  module Location = struct
    module T0 = struct
      type t =
        | Relation_arg of TG.Relation.t
        | Relation_val of TG.Relation.t
        | Switch
        | Relation_switch of TG.Relation.t

      let print ppf = function
        | Relation_arg r -> Format.fprintf ppf "_ = %a(·)" TG.Relation.print r
        | Relation_val r -> Format.fprintf ppf "· = %a(_)" TG.Relation.print r
        | Switch -> Format.fprintf ppf "switch (·) { _ }"
        | Relation_switch r ->
          Format.fprintf ppf "switch (%a(·)) { _ }" TG.Relation.print r

      let equal l1 l2 =
        match l1, l2 with
        | Relation_arg r1, Relation_arg r2
        | Relation_val r1, Relation_val r2
        | Relation_switch r1, Relation_switch r2 ->
          TG.Relation.equal r1 r2
        | Switch, Switch -> true
        | (Relation_arg _ | Relation_val _ | Relation_switch _ | Switch), _ ->
          false

      let hash = function
        | Switch -> Hashtbl.hash 0
        | Relation_arg r -> Hashtbl.hash (0, TG.Relation.hash r)
        | Relation_val r -> Hashtbl.hash (1, TG.Relation.hash r)
        | Relation_switch r -> Hashtbl.hash (2, TG.Relation.hash r)

      let compare l1 l2 =
        match l1, l2 with
        | Relation_arg r1, Relation_arg r2
        | Relation_val r1, Relation_val r2
        | Relation_switch r1, Relation_switch r2 ->
          TG.Relation.compare r1 r2
        | Switch, Switch -> 0
        | Relation_arg _, _ -> -1
        | _, Relation_arg _ -> 1
        | Relation_val _, _ -> -1
        | _, Relation_val _ -> 1
        | Switch, _ -> -1
        | _, Switch -> 1
    end

    include T0
    include Container_types.Make (T0)
  end

  type 'a t =
    { relations : Function.t TG.Relation.Map.t;
      inverse_relations : Inverse.t TG.Relation.Map.t;
      switches_on_names : 'a Row_like.t Z_lattice_on_names.t;
      switches_on_relations :
        'a Row_like.t Z_lattice_on_names.t TG.Relation.Map.t;
      continuation_uses : Apply_cont_rewrite_id.Set.t Continuation.Map.t;
      free_names : Location.Set.t Name.Map.t
    }

  let print _pp ppf
      { relations;
        inverse_relations = _;
        switches_on_names;
        switches_on_relations;
        continuation_uses;
        free_names = _
      } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(relations@ %a)@]@ @[<hov 1>(continuation_uses@ \
       %a)@])@ @[<hov 1>(switch_on_names@ %a)@]@ @[<hov \
       1>(switch_on_relations@ %a)@]@]"
      (TG.Relation.Map.print Function.print)
      relations
      (Continuation.Map.print Apply_cont_rewrite_id.Set.print)
      continuation_uses
      (Name.Map.print
         (print_or_gone
            (Row_like.print
               (Continuation.Map.print Apply_cont_rewrite_id.Set.print))))
      switches_on_names
      (TG.Relation.Map.print
         (Name.Map.print
            (print_or_gone
               (Row_like.print
                  (Continuation.Map.print Apply_cont_rewrite_id.Set.print)))))
      switches_on_relations

  let apply_renaming_function (fn : Function.t) renaming : Function.t =
    Name.Map.fold
      (fun name values fn ->
        Name.Map.add
          (Renaming.apply_name renaming name)
          (Simple.Map.map_keys (Renaming.apply_simple renaming) values)
          fn)
      fn Name.Map.empty

  let apply_renaming_inverse (inverse : Inverse.t) renaming : Inverse.t =
    Name.Map.fold
      (fun name values inverse ->
        Name.Map.add
          (Renaming.apply_name renaming name)
          (Name.Map.map_keys (Renaming.apply_name renaming) values)
          inverse)
      inverse Name.Map.empty

  let apply_renaming t renaming =
    let relations =
      TG.Relation.Map.map
        (fun fn -> apply_renaming_function fn renaming)
        t.relations
    in
    let inverse_relations =
      TG.Relation.Map.map
        (fun inverse -> apply_renaming_inverse inverse renaming)
        t.inverse_relations
    in
    let switches_on_names =
      Name.Map.map_keys (Renaming.apply_name renaming) t.switches_on_names
    in
    let switches_on_relations =
      TG.Relation.Map.map
        (fun switch -> Name.Map.map_keys (Renaming.apply_name renaming) switch)
        t.switches_on_relations
    in
    let free_names =
      Name.Map.map_keys (Renaming.apply_name renaming) t.free_names
    in
    { relations;
      inverse_relations;
      switches_on_names;
      switches_on_relations;
      continuation_uses = t.continuation_uses;
      free_names
    }

  let empty =
    { relations = TG.Relation.Map.empty;
      inverse_relations = TG.Relation.Map.empty;
      switches_on_names = Name.Map.empty;
      switches_on_relations = TG.Relation.Map.empty;
      continuation_uses = Continuation.Map.empty;
      free_names = Name.Map.empty
    }

  let is_empty t =
    TG.Relation.Map.is_empty t.relations
    && Name.Map.is_empty t.switches_on_names
    && TG.Relation.Map.is_empty t.switches_on_relations

  let get_incremental get t =
    { current = get t.current; difference = get t.difference }

  let get_continuation_uses t = t.continuation_uses

  let set_continuation_uses continuation_uses t = { t with continuation_uses }

  let set_incremental set value t =
    { current = set value.current t.current;
      difference = set value.difference t.difference
    }

  let map_incremental f t =
    { current = f t.current; difference = f t.difference }

  let get_switches_on_relations t = t.switches_on_relations

  let set_switches_on_relations switches_on_relations t =
    { t with switches_on_relations }

  let get_switches_on_names t = t.switches_on_names

  let set_switches_on_names switches_on_names t = { t with switches_on_names }

  let get_switches_on_relation relation t =
    try TG.Relation.Map.find relation t.switches_on_relations
    with Not_found -> Name.Map.empty

  let set_switches_on_relation relation switches_on_relation t =
    let switches_on_relations =
      TG.Relation.Map.add relation switches_on_relation t.switches_on_relations
    in
    { t with switches_on_relations }

  let create_switch ~default ~arms:known =
    let other : _ Or_bottom.t =
      match default with None -> Bottom | Some other -> Ok other
    in
    Row_like.{ known; other }

  let meet_row_like ~meet env case1 case2 =
    let meet env case1 case2 =
      Or_bottom.map ~f:(fun case -> case, env) (meet env case1 case2)
    in
    Or_bottom.Ok (Row_like.meet ~meet env case1 case2)

  let add_switch0 ~meet name row_like env t =
    let open Or_bottom.Let_syntax in
    let meet env case1 case2 =
      let meet env case1 case2 =
        Or_bottom.map ~f:(fun case -> case, env) (meet env case1 case2)
      in
      Or_bottom.Ok (Row_like.meet ~meet env case1 case2)
    in
    let<+ t, new_env = add_z_lattice_on_names ~meet name row_like env t in
    (* We can't modify the environment from a switch. *)
    assert (env == new_env);
    t

  let get_relation relation t =
    try TG.Relation.Map.find relation t.relations
    with Not_found -> Function.empty

  let add_switch_on_name ~meet name row_like t =
    let open Or_bottom.Let_syntax in
    let<+ switches_on_names =
      add_switch0 ~meet name row_like t.current
        (get_incremental get_switches_on_names t)
    in
    set_incremental set_switches_on_names switches_on_names t

  let add_switch_on_simple ~add_arm ~meet simple row_like t =
    Simple.pattern_match simple
      ~const:(fun const ->
        match Reg_width_const.Map.find_opt const row_like.Row_like.known with
        | Some arm -> add_arm arm t
        | None -> (
          match row_like.Row_like.other with
          | Ok default -> add_arm default t
          | Bottom -> Or_bottom.Bottom))
      ~name:(fun name ~coercion ->
        assert (Coercion.is_id coercion);
        add_switch_on_name ~meet name row_like t)

  let remove_switch_on_relation relation name t =
    let switches_on_relation =
      get_incremental (get_switches_on_relation relation) t
    in
    match Name.Map.find_opt name switches_on_relation.current with
    | None | Some Gone -> t
    | Some (There _) ->
      let switches_on_relation =
        map_incremental (Name.Map.remove name) switches_on_relation
      in
      set_incremental (set_switches_on_relation relation) switches_on_relation t

  let add_switch_on_relation ~meet relation name ?default ~arms t =
    let open Or_bottom.Let_syntax in
    let<+ switches_on_relation =
      add_switch0 ~meet name
        (create_switch ~default ~arms)
        t.current
        (get_incremental (get_switches_on_relation relation) t)
    in
    set_incremental (set_switches_on_relation relation) switches_on_relation t

  let interredox ~add_arm ~meet switches_on_relations relations t =
    let t_ref = ref (Or_bottom.Ok t) in
    ignore
      (TG.Relation.Map.inter
         (fun relation switches fn ->
           ignore
             (Name.Map.inter
                (fun name row_like values ->
                  match row_like with
                  | Gone -> None
                  | There row_like ->
                    Simple.Map.iter
                      (fun simple count ->
                        if count > 0
                        then
                          match !t_ref with
                          | Bottom -> ()
                          | Ok t ->
                            let t = remove_switch_on_relation relation name t in
                            t_ref
                              := add_switch_on_simple ~add_arm ~meet simple
                                   row_like t)
                      values;
                    None)
                switches fn);
           None)
         switches_on_relations relations);
    !t_ref

  let interredox ~add_arm ~meet ~previous ~current ~difference t =
    let open Or_bottom.Let_syntax in
    (* Seminaive evaluation. *)
    let<* t =
      interredox ~add_arm ~meet previous.switches_on_relations
        difference.relations t
    in
    interredox ~add_arm ~meet difference.switches_on_relations current.relations
      t

  let meet_apply_cont_rewrite_id_set uses1 uses2 : _ Or_bottom.t =
    match
      ( Apply_cont_rewrite_id.Set.subset uses1 uses2,
        Apply_cont_rewrite_id.Set.subset uses2 uses1 )
    with
    | true, true -> Ok Both_inputs
    | true, false -> Ok Left_input
    | false, true -> Ok Right_input
    | false, false ->
      let uses = Apply_cont_rewrite_id.Set.inter uses1 uses2 in
      if Apply_cont_rewrite_id.Set.is_empty uses
      then Bottom
      else Ok (New_result uses)

  exception Bottom_equation

  let meet_continuation_uses _ uses1 uses2 : _ Or_bottom.t =
    let result_is_left = ref true in
    let result_is_right = ref true in
    match
      Continuation.Map.union
        (fun _ uses1 uses2 ->
          match meet_apply_cont_rewrite_id_set uses1 uses2 with
          | Bottom -> raise Bottom_equation
          | Ok Left_input ->
            result_is_right := false;
            Some uses1
          | Ok Right_input ->
            result_is_left := false;
            Some uses2
          | Ok Both_inputs -> Some uses1
          | Ok (New_result uses) ->
            result_is_left := false;
            result_is_right := false;
            Some uses)
        uses1 uses2
    with
    | uses -> (
      match !result_is_left, !result_is_right with
      | true, true -> Ok Both_inputs
      | true, false -> Ok Left_input
      | false, true -> Ok Right_input
      | false, false -> Ok (New_result uses))
    | exception Bottom_equation -> Bottom

  let interredox ~previous ~current ~difference t =
    let meet = meet_continuation_uses in
    let add_arm _ t = Or_bottom.Ok t in
    interredox ~add_arm ~meet ~previous ~current ~difference t

  let add_free_name name loc t =
    let free_names =
      Name.Map.update name
        (function
          | None -> Some (Location.Set.singleton loc)
          | Some locs -> Some (Location.Set.add loc locs))
        t.free_names
    in
    { t with free_names }

  let remove_free_name name t =
    { t with free_names = Name.Map.remove name t.free_names }

  let add_free_names_of_simple simple loc t =
    Simple.pattern_match simple
      ~const:(fun _ -> t)
      ~name:(fun name ~coercion:_ -> add_free_name name loc t)

  let add_many_free_names_of_simple simple locs t =
    Simple.pattern_match simple
      ~const:(fun _ -> t)
      ~name:(fun name ~coercion:_ ->
        Location.Set.fold (fun loc t -> add_free_name name loc t) locs t)

  let add_switch_on_relation relation name ?default ~arms t =
    let t = map_incremental (add_free_name name (Relation_switch relation)) t in
    add_switch_on_relation ~meet:meet_continuation_uses relation name ?default
      ~arms t

  let add_switch_on_name name ?default ~arms t =
    let t = map_incremental (add_free_name name Switch) t in
    add_switch_on_name ~meet:meet_continuation_uses name
      (create_switch ~default ~arms)
      t

  let concat ~earlier ~later =
    let relations =
      TG.Relation.Map.union
        (fun _ earlier later -> Some (Function.concat ~earlier ~later))
        earlier.relations later.relations
    in
    let inverse_relations =
      TG.Relation.Map.union
        (fun _ earlier later -> Some (Inverse.union earlier later))
        earlier.inverse_relations later.inverse_relations
    in
    let concat_or_gone ~earlier ~later =
      match earlier, later with
      | There _, Gone -> Some later
      | There _, There _ -> Some later
      | Gone, _ ->
        let _ = assert false in
        Misc.fatal_error "Already gone! What?"
    in
    let switches_on_names =
      Name.Map.union
        (fun _ earlier later -> concat_or_gone ~earlier ~later)
        earlier.switches_on_names later.switches_on_names
    in
    let switches_on_relations =
      TG.Relation.Map.union
        (fun _ earlier later ->
          Some
            (Name.Map.union
               (fun _ earlier later -> concat_or_gone ~earlier ~later)
               earlier later))
        earlier.switches_on_relations later.switches_on_relations
    in
    { relations;
      inverse_relations;
      switches_on_names;
      switches_on_relations;
      continuation_uses = later.continuation_uses;
      free_names =
        Name.Map.union
          (fun _ _locs1 locs2 -> Some locs2)
          earlier.free_names later.free_names
    }

  let set_relation relation table t =
    let relations = TG.Relation.Map.add relation table t.relations in
    { t with relations }

  let add_relation relation table t =
    let relations =
      TG.Relation.Map.update relation
        (function
          | None -> Some table
          | Some earlier -> Some (Function.concat ~earlier ~later:table))
        t.relations
    in
    { t with relations }

  let add_inverse_relation relation table t =
    let inverse_relations =
      TG.Relation.Map.update relation
        (function
          | None -> Some table
          | Some earlier -> Some (Inverse.union earlier table))
        t.inverse_relations
    in
    { t with inverse_relations }

  let get_inverse_relation relation t =
    try TG.Relation.Map.find relation t.inverse_relations
    with Not_found -> Inverse.empty

  let set_inverse_relation relation table t =
    let inverse_relations =
      TG.Relation.Map.add relation table t.inverse_relations
    in
    { t with inverse_relations }

  let compute_inverse_difference table_difference =
    Name.Map.fold
      (fun name values inverse_difference ->
        Simple.Map.fold
          (fun value count inverse_difference ->
            Simple.pattern_match value
              ~const:(fun _ -> inverse_difference)
              ~name:(fun value_name ~coercion ->
                assert (Coercion.is_id coercion);
                if count > 0
                then Inverse.add (value_name, name) inverse_difference
                else Inverse.remove (value_name, name) inverse_difference))
          values inverse_difference)
      table_difference Inverse.empty

  let update_inverse relation difference t =
    let inverse_difference = compute_inverse_difference difference in
    let current = add_inverse_relation relation inverse_difference t.current in
    let difference =
      add_inverse_relation relation inverse_difference t.difference
    in
    { current; difference }

  let add_relation ~meet relation key value aliases t : _ Or_bottom.t =
    let t = map_incremental (add_free_name key (Relation_arg relation)) t in
    let t =
      map_incremental (add_free_names_of_simple value (Relation_val relation)) t
    in
    let open Or_bottom.Let_syntax in
    let table = get_relation relation t.current in
    let<+ { current = table; difference = table_difference }, aliases =
      generic_add
        ~find_opt:(Incremental0.find_opt ~find_opt:Function.find_opt)
        ~replace:
          (Incremental0.replace ~find_opt:Function.find_opt ~add:Function.add
             ~replace:Function.replace)
        ~meet key value aliases
        { current = table; difference = Function.empty }
    in
    let current = set_relation relation table t.current in
    let difference = add_relation relation table_difference t.difference in
    let t = update_inverse relation table_difference { current; difference } in
    t, aliases

  let remove_relation relation key value t =
    let fn = get_incremental (get_relation relation) t in
    let fn = map_incremental (Function.remove key value) fn in
    let t = set_incremental (set_relation relation) fn t in
    Simple.pattern_match value
      ~const:(fun _ -> t)
      ~name:(fun name ~coercion ->
        assert (Coercion.is_id coercion);
        let inverse = get_incremental (get_inverse_relation relation) t in
        let inverse = map_incremental (Inverse.remove (name, key)) inverse in
        set_incremental (set_inverse_relation relation) inverse t)

  let add_continuation_use cont use t =
    let continuation_uses = get_incremental get_continuation_uses t in
    let continuation_uses =
      Incremental0.replace ~find_opt:Continuation.Map.find_opt
        ~add:Continuation.Map.add
        ~replace:(fun cont ~existing_value:_ use map ->
          Continuation.Map.add cont use map)
        cont
        (Apply_cont_rewrite_id.Set.singleton use)
        continuation_uses
    in
    set_incremental set_continuation_uses continuation_uses t

  let continuation_uses t = t.current.continuation_uses
end

type t = Apply_cont_rewrite_id.Set.t Continuation.Map.t Final.t incremental

let print ppf t =
  Final.print
    (Continuation.Map.print Apply_cont_rewrite_id.Set.print)
    ppf t.current

let empty = { current = Final.empty; difference = Final.empty }

let apply_renaming t renaming =
  Final.map_incremental (fun t -> Final.apply_renaming t renaming) t

let empty_snapshot = Final.empty

let apply_renaming_snapshot = Final.apply_renaming

type difference = Apply_cont_rewrite_id.Set.t Continuation.Map.t Final.t

let print_extension ppf t =
  Final.print (Continuation.Map.print Apply_cont_rewrite_id.Set.print) ppf t

type relation_extension = Function.t

let fold_relations f t acc =
  TG.Relation.Map.fold
    (fun relation table acc -> f relation table acc)
    t.Final.relations acc

let fold_relation_extension f (t : relation_extension) acc =
  Name.Map.fold
    (fun key values acc ->
      Simple.Map.fold
        (fun value count acc -> if count > 0 then f key value acc else acc)
        values acc)
    t acc

let empty_extension = Final.empty

let is_empty_extension = Final.is_empty

let tick { current; difference } = current, difference

let from_snapshot current = { current; difference = Final.empty }

let concat_extension = Final.concat

let demote_in_function ~to_be_demoted ~canonical_element ~meet aliases (t : t) =
  let open Or_bottom.Let_syntax in
  Simple.pattern_match canonical_element
    ~const:(fun const ->
      TG.Relation.Map.fold
        (fun relation fn result ->
          let<* t, aliases = result in
          match Function.find_opt to_be_demoted fn with
          | None -> Ok (t, aliases)
          | Some existing_value ->
            let t =
              Final.remove_relation relation to_be_demoted existing_value t
            in
            let<* const_value = relation_for_const relation const in
            let<+ _, aliases =
              meet aliases (Simple.const const_value) existing_value
            in
            t, aliases)
        t.current.relations
        (Or_bottom.Ok (t, aliases)))
    ~name:(fun canonical_name ~coercion ->
      assert (Coercion.is_id coercion);
      TG.Relation.Map.fold
        (fun relation fn result ->
          let<* t, aliases = result in
          match Function.find_opt to_be_demoted fn with
          | None -> Ok (t, aliases)
          | Some existing_value ->
            let t =
              Final.remove_relation relation to_be_demoted existing_value t
            in
            Final.add_relation ~meet relation canonical_name existing_value
              aliases t)
        t.current.relations
        (Or_bottom.Ok (t, aliases)))

let demote_switch ~apply_coercion ~to_be_demoted ~canonical_element aliases
    switches : _ Or_bottom.t =
  match find_z_lattice_on_names to_be_demoted switches with
  | None -> Ok (switches, aliases)
  | Some value ->
    let switches = remove_z_lattice_on_names to_be_demoted value switches in
    Simple.pattern_match canonical_element
      ~const:(fun _const -> Or_bottom.Ok (switches, aliases))
      ~name:(fun canonical_name ~coercion ->
        let value = apply_coercion value (Coercion.inverse coercion) in
        add_z_lattice_on_names
          ~meet:(Final.meet_row_like ~meet:Final.meet_continuation_uses)
          canonical_name value aliases switches)

let demote_in_inverse ~to_be_demoted ~canonical_element ~meet aliases (t : t) =
  let open Or_bottom.Let_syntax in
  TG.Relation.Map.fold
    (fun relation inverse result ->
      match Name.Map.find_opt to_be_demoted inverse with
      | None -> result
      | Some keys ->
        Name.Map.fold
          (fun key count result ->
            if count <= 0
            then result
            else
              let<* t, aliases = result in
              let t =
                Final.remove_relation relation key (Simple.name to_be_demoted) t
              in
              Final.add_relation ~meet relation key canonical_element aliases t)
          keys result)
    t.current.inverse_relations
    (Or_bottom.Ok (t, aliases))

let demote ~to_be_demoted ~canonical_element ~meet aliases t =
  let open Or_bottom.Let_syntax in
  let<* switches_on_names, () =
    demote_switch
      ~apply_coercion:(fun switch coercion ->
        assert (Coercion.is_id coercion);
        switch)
      ~to_be_demoted ~canonical_element ()
      (Final.get_incremental Final.get_switches_on_names t)
  in
  let t =
    Final.set_incremental Final.set_switches_on_names switches_on_names t
  in
  let<* switches_on_relations =
    TG.Relation.Map.fold
      (fun relation switches switches_on_relations ->
        let<* switches_on_relations = switches_on_relations in
        let switches_diff =
          try TG.Relation.Map.find relation switches_on_relations.difference
          with Not_found -> Name.Map.empty
        in
        let<+ switches, () =
          demote_switch
            ~apply_coercion:(fun row_like coercion ->
              assert (Coercion.is_id coercion);
              row_like)
            ~to_be_demoted ~canonical_element ()
            { current = switches; difference = switches_diff }
        in
        Final.set_incremental
          (TG.Relation.Map.add relation)
          switches switches_on_relations)
      t.current.switches_on_relations
      (Or_bottom.Ok (Final.get_incremental Final.get_switches_on_relations t))
  in
  let t =
    Final.set_incremental Final.set_switches_on_relations switches_on_relations
      t
  in
  let<* t, aliases =
    demote_in_function ~to_be_demoted ~canonical_element ~meet aliases t
  in
  let<+ t, aliases =
    demote_in_inverse ~to_be_demoted ~canonical_element ~meet aliases t
  in
  let t =
    match Name.Map.find_opt to_be_demoted t.current.Final.free_names with
    | None -> t
    | Some locs ->
      let t = Final.map_incremental (Final.remove_free_name to_be_demoted) t in
      Final.map_incremental
        (Final.add_many_free_names_of_simple canonical_element locs)
        t
  in
  t, aliases

let rebuild ~demotions ~binding_time_resolver ~binding_times_and_modes aliases0
    database =
  Aliases0.rebuild ~demotions ~binding_time_resolver ~binding_times_and_modes
    demote aliases0 database

let add_relation ~binding_time_resolver ~binding_times_and_modes aliases0
    database relation name value =
  Final.add_relation
    ~meet:(Aliases0.meet ~binding_time_resolver ~binding_times_and_modes)
    relation name value aliases0 database

let add_continuation_use cont use t = Final.add_continuation_use cont use t

let continuation_uses = Final.continuation_uses

let add_switch_on_name = Final.add_switch_on_name

let add_switch_on_relation = Final.add_switch_on_relation

let switch_on_scrutinee t ~scrutinee =
  Simple.pattern_match scrutinee
    ~const:(fun _ -> Or_unknown.Unknown)
    ~name:(fun name ~coercion:_ ->
      match Name.Map.find_opt name t.current.Final.switches_on_names with
      | None | Some Gone -> Or_unknown.Unknown
      | Some (There continuations) -> Or_unknown.Known continuations.known)

let add_extension t extension =
  let current = concat_extension ~earlier:t.current ~later:extension in
  let difference = concat_extension ~earlier:t.difference ~later:extension in
  { current; difference }

let make_demotions t types =
  let types =
    Name.Map.inter (fun _ _locs ty -> ty) t.current.Final.free_names types
  in
  Name.Map.filter_map (fun _ ty -> Type_grammar.get_alias_opt ty) types

let interreduce ~previous ~current ~difference =
  Final.interredox ~previous ~current:current.current ~difference current

type snapshot = difference
