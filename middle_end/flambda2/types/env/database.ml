module TG = Type_grammar

module type Abelian_group = sig
  type t

  val ( ~- ) : t -> t

  val ( + ) : t -> t -> t

  val ( - ) : t -> t -> t
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

let extract_value res left right =
  match res with
  | Left_input -> left
  | Right_input -> right
  | Both_inputs -> left
  | New_result value -> value

module Row_like0 = struct
  type 'a case = 'a Or_bottom.t

  let print_case pp = Or_bottom.print pp

  let merge_case f (case1 : 'a case) (case2 : 'a case) : _ case =
    match case1, case2 with
    | Bottom, Bottom -> Bottom
    | Bottom, Ok case | Ok case, Bottom -> Ok case
    | Ok case1, Ok case2 -> f case1 case2

  let meet_case ~meet (env : 'b) (case1 : 'a case) (case2 : 'a case) :
      'a case meet_return_value * 'b =
    match case1, case2 with
    | Bottom, Bottom -> Both_inputs, env
    | Bottom, Ok _ -> Left_input, env
    | Ok _, Bottom -> Right_input, env
    | Ok case1, Ok case2 -> (
      match meet env case1 case2 with
      | Or_bottom.Bottom -> New_result Or_bottom.Bottom, env
      | Or_bottom.Ok (case, env) ->
        let case = map_return_value (fun case -> Or_bottom.Ok case) case in
        case, env)

  module Make (Branch : Container_types.S) : S = struct
    type key = Branch.t

    type 'a t =
      { known : 'a Branch.Map.t;
        other : 'a case
      }

    let print_known pp ppf known = Branch.Map.print pp ppf known

    let print pp ppf { known; other } =
      Format.fprintf ppf
        "@[<hov 1>(@[<hov 1>(known@ %a)@]@ @[<hov 1>(other@ %a)@]@]"
        (print_known pp) known (print_case pp) other

    let is_bottom { other; known } =
      match other with Bottom -> Branch.Map.is_empty known | Ok _ -> false

    let map f { known; other } =
      let other = Or_bottom.map ~f other in
      let known = Branch.Map.map f known in
      { known; other }

    let merge f { known = known1; other = other1 }
        { known = known2; other = other2 } =
      let known =
        Branch.Map.merge
          (fun _ case1 case2 ->
            let case1 : _ Or_bottom.t =
              match case1 with None -> other1 | Some case1 -> Ok case1
            in
            let case2 : _ Or_bottom.t =
              match case2 with None -> other2 | Some case2 -> Ok case2
            in
            match (f case1 case2 : _ Or_bottom.t) with
            | Bottom -> None
            | Ok case -> Some case)
          known1 known2
      in
      let other = f other1 other2 in
      { known; other }

    let find const { other; known } : _ Or_bottom.t =
      match Branch.Map.find_opt const known with
      | Some arm -> Ok arm
      | None -> other

    let meet ~meet env t1 t2 =
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
      let env_ref = ref env in
      let result =
        merge
          (fun case1 case2 ->
            let case, env = meet_case ~meet !env_ref case1 case2 in
            env_ref := env;
            update_refs case;
            extract_value case case1 case2)
          t1 t2
      in
      let env = !env_ref in
      match !result_is_left, !result_is_right with
      | true, true -> Both_inputs, env
      | true, false -> Left_input, env
      | false, true -> Right_input, env
      | false, false -> New_result result, env

    module Abelian_group (G : Abelian_group) : Abelian_group = struct
      type nonrec t = G.t t

      let ( ~- ) = map G.( ~- )

      let ( + ) = merge (merge_case (fun x y -> Ok (G.( + ) x y)))

      let ( - ) = merge (merge_case (fun x y -> Ok (G.( - ) x y)))
    end
  end
end

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
end

type 'a incremental =
  { current : 'a;
    difference : 'a
  }

module Incremental = struct
  let current { current; _ } = current

  let get get t = { current = get t.current; difference = get t.difference }

  let set set value t =
    { current = set value.current t.current;
      difference = set value.difference t.difference
    }

  let map f t = { current = f t.current; difference = f t.difference }
end

let get_singleton z_value =
  match Simple.Map.get_singleton z_value with
  | Some (value, 1) -> value
  | _ -> Misc.fatal_error "Not a function"

let canonicalize aliases simple =
  Simple.pattern_match simple
    ~const:(fun _ -> simple)
    ~name:(fun name ~coercion ->
      Simple.apply_coercion_exn
        (Aliases.get_canonical_ignoring_name_mode aliases name)
        coercion)

module Aliases0 = struct
  type t =
    { aliases : Aliases.t;
      demotions : Simple.t Name.Map.t
    }

  let canonicalize { aliases; _ } simple = canonicalize aliases simple

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
end

module Function = struct
  include Unary_function0 (Name) (Simple)

  let apply_renaming fn renaming =
    Name.Map.fold
      (fun name values fn ->
        Name.Map.add
          (Renaming.apply_name renaming name)
          (Simple.Map.map_keys (Renaming.apply_simple renaming) values)
          fn)
      fn Name.Map.empty

  let add_simple ~meet ~for_const ~scrutinee value t aliases =
    let open Or_bottom.Let_syntax in
    Simple.pattern_match scrutinee
      ~const:(fun const ->
        let<* const_value = for_const const in
        Format.eprintf "meet %a and %a@." Simple.print value
          Reg_width_const.print const_value;
        let<+ _, aliases = meet aliases value (Simple.const const_value) in
        t, aliases)
      ~name:(fun name ~coercion : _ Or_bottom.t ->
        let inverse_coercion = Coercion.inverse coercion in
        let value = Simple.apply_coercion_exn value inverse_coercion in
        match find_opt name (Incremental.current t) with
        | None ->
          let t = Incremental.map (add name value) t in
          Ok (t, aliases)
        | Some existing_value ->
          let<+ _, aliases = meet aliases value existing_value in
          t, aliases)

  exception Bottom_relation

  let rebuild ~meet ~for_const demotions t aliases : _ Or_bottom.t =
    let t_ref = ref t in
    let aliases_ref = ref aliases in
    match
      (Name.Map.inter
         (fun to_be_demoted canonical_at_demotion z_value ->
           let aliases = !aliases_ref in
           let scrutinee =
             Aliases0.canonicalize aliases canonical_at_demotion
           in
           let value = get_singleton z_value in
           let t = !t_ref in
           match add_simple ~meet ~for_const ~scrutinee value t aliases with
           | Bottom -> raise Bottom_relation
           | Ok (t, aliases) ->
             let t = Incremental.map (remove to_be_demoted value) t in
             t_ref := t;
             aliases_ref := aliases)
         demotions (Incremental.current t)
        : unit Name.Map.t)
    with
    | exception Bottom_relation -> Bottom
    | _ ->
      let t = !t_ref in
      let aliases = !aliases_ref in
      Ok (t, aliases)
end

module Row_like = struct
  module Make (Branch : Container_types.S) = struct
    type 'a case = 'a Or_bottom.t

    let print_case pp = Or_bottom.print pp

    let add_case ~add (case1 : 'a case) (case2 : 'a case) : _ case =
      match case1, case2 with
      | Bottom, Bottom -> Bottom
      | Bottom, Ok case | Ok case, Bottom -> Ok case
      | Ok case1, Ok case2 -> add case1 case2

    let meet_case ~meet (env : 'b) (case1 : 'a case) (case2 : 'a case) :
        'a case meet_return_value * 'b =
      match case1, case2 with
      | Bottom, Bottom -> Both_inputs, env
      | Bottom, Ok _ -> Left_input, env
      | Ok _, Bottom -> Right_input, env
      | Ok case1, Ok case2 -> (
        match meet env case1 case2 with
        | Or_bottom.Bottom -> New_result Or_bottom.Bottom, env
        | Or_bottom.Ok (case, env) ->
          let case = map_return_value (fun case -> Or_bottom.Ok case) case in
          case, env)

    type 'a t =
      { known : 'a Branch.Map.t;
        other : 'a Or_bottom.t
      }

    let merge f { known = known1; other = other1 }
        { known = known2; other = other2 } =
      let known =
        Branch.Map.merge
          (fun _ case1 case2 ->
            let case1 : _ Or_bottom.t =
              match case1 with None -> other1 | Some case1 -> Ok case1
            in
            let case2 : _ Or_bottom.t =
              match case2 with None -> other2 | Some case2 -> Ok case2
            in
            match (f case1 case2 : _ Or_bottom.t) with
            | Bottom -> None
            | Ok case -> Some case)
          known1 known2
      in
      let other = f other1 other2 in
      { known; other }

    let add ~add t1 t2 = merge (add_case ~add) t1 t2

    let () = ignore add

    let is_bottom { other; known } =
      match other with Bottom -> Branch.Map.is_empty known | Ok _ -> false

    let print_known pp ppf known = Branch.Map.print pp ppf known

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

    let find const { other; known } : _ Or_bottom.t =
      match Branch.Map.find_opt const known with
      | Some arm -> Ok arm
      | None -> other

    let meet ~meet env t1 t2 =
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
      let env_ref = ref env in
      let result =
        merge
          (fun case1 case2 ->
            let case, env = meet_case ~meet !env_ref case1 case2 in
            env_ref := env;
            update_refs case;
            extract_value case case1 case2)
          t1 t2
      in
      let env = !env_ref in
      match !result_is_left, !result_is_right with
      | true, true -> Both_inputs, env
      | true, false -> Left_input, env
      | false, true -> Right_input, env
      | false, false -> New_result result, env
  end

  include Make (Reg_width_const)
end

module One_relation = struct
  (* Note: we use [Simple] for the value of these relations, but they may never
     contain constants -- only names with (or without) coercion. *)
  module Inverse_of_names = ZRel2 (Name) (Simple)
  module Inverse_of_consts = ZRel2 (Reg_width_const) (Simple)

  type t =
    { values : Function.t;
      inverse_of_names : Inverse_of_names.t;
      inverse_of_consts : Inverse_of_consts.t
    }

  let print ppf { values; inverse_of_names = _; inverse_of_consts = _ } =
    Function.print ppf values

  let empty =
    { values = Function.empty;
      inverse_of_names = Inverse_of_names.empty;
      inverse_of_consts = Inverse_of_consts.empty
    }

  let apply_renaming t renaming =
    let values = Function.apply_renaming t.values renaming in
    let inverse_of_names =
      Name.Map.fold
        (fun name values inverse ->
          Name.Map.add
            (Renaming.apply_name renaming name)
            (Simple.Map.map_keys (Renaming.apply_simple renaming) values)
            inverse)
        t.inverse_of_names Name.Map.empty
    in
    let inverse_of_consts =
      Reg_width_const.Map.map
        (Simple.Map.map_keys (Renaming.apply_simple renaming))
        t.inverse_of_consts
    in
    { values; inverse_of_names; inverse_of_consts }

  let union t1 t2 =
    let values = Function.union t1.values t2.values in
    let inverse_of_names =
      Inverse_of_names.union t1.inverse_of_names t2.inverse_of_names
    in
    let inverse_of_consts =
      Inverse_of_consts.union t1.inverse_of_consts t2.inverse_of_consts
    in
    { values; inverse_of_names; inverse_of_consts }

  let concat ~earlier ~later = union earlier later

  let linear_rule_inverse (values : Function.t) aliases =
    let aliases = Aliases0.{ aliases; demotions = Name.Map.empty } in
    (* Consider that we have a function with [R(key1) = value1]. At this point,
       reduction will introduce [R⁻¹(value1) = { key1 }] to the inverse map.

       Suppose now that we have demoted both [value1] to [value2], and also
       [key1] to [key2] and we want to restore consistency.

       This induce three changes to the relations, that can be processed in any
       order (as long as (c) is after (b)):

       (a) Demotion of [value1] to [value2] will add an inverse difference;

       (b) Demotion of [key1] to [key2] will add a value difference;

       (c) Reduction of the value difference created in (b) will add another
       inverse difference.

       If we process in (a) - (b) - (c) order:

       - In step (a) we remove [key1] from [R⁻¹(value1)] and add it to
       [R⁻¹(value2)].

       - In step (b) we remove [value1] from [R(key1)] and add it to [R(key2)].

       - In step (c) we remove [key1] from [R⁻¹(value2)] and add [key2] instead.
       Note that, crucially, this is [value2] because we canonicalise the value
       used for the inverse map.

       We end up with [R(key2) = value1] and [R⁻¹(value2) = {key2}] as expected
       (recall that values in the direct map are not canonicalized, so this is
       not [R(key2) = value2]).)

       The same happens if we process in (b) - (a) - (c) or (b) - (c) - (a)
       order, except that in this last case, we remove [key1] from [R⁻¹(value2)]
       in step (c) {b before} adding it in step (a). [key1] will thus
       temporarily have a negative multiplicity in [R⁻¹(value2)].

       If we only demote [key1] to [key2] before restoring consistency, there is
       no step (a) and [value1] is still canonical in step (c), so we end up
       with [R⁻¹(value1) = {key2}].

       If we later demote [value1] to [value2], we will only perform step (a),
       during which we simply remove [key2] from [R⁻¹(value1)] and add it to
       [R⁻¹(value2)]. *)
    let inverse_of_consts, inverse_of_names =
      Name.Map.fold
        (fun scrutinee z_values inverse ->
          Simple.Map.fold
            (fun value multiplicity (inverse_of_consts, inverse_of_names) ->
              let value = Aliases0.canonicalize aliases value in
              Simple.pattern_match value
                ~const:(fun const ->
                  let inverse_of_consts =
                    Inverse_of_consts.union inverse_of_consts
                      (Reg_width_const.Map.singleton const
                         (Simple.Map.singleton (Simple.name scrutinee)
                            multiplicity))
                  in
                  inverse_of_consts, inverse_of_names)
                ~name:(fun name ~coercion ->
                  let scrutinee_with_coercion =
                    Simple.with_coercion (Simple.name scrutinee)
                      (Coercion.inverse coercion)
                  in
                  let inverse_of_names =
                    Inverse_of_names.union inverse_of_names
                      (Name.Map.singleton name
                         (Simple.Map.singleton scrutinee_with_coercion
                            multiplicity))
                  in
                  inverse_of_consts, inverse_of_names))
            z_values inverse)
        values
        (Inverse_of_consts.empty, Inverse_of_names.empty)
    in
    { values; inverse_of_consts; inverse_of_names }

  let add ~meet ~for_const ~scrutinee value t aliases =
    let open Or_bottom.Let_syntax in
    let values = Incremental.get (fun t -> t.values) t in
    let<+ values, aliases =
      Function.add_simple ~meet ~for_const ~scrutinee value values aliases
    in
    Incremental.set (fun values t -> { t with values }) values t, aliases

  let rebuild ~meet ~for_const demotions t aliases =
    let open Or_bottom.Let_syntax in
    let values = Incremental.get (fun t -> t.values) t in
    let<+ values, aliases =
      Function.rebuild ~meet ~for_const demotions values aliases
    in
    let t = Incremental.set (fun values t -> { t with values }) values t in
    let inverse_of_names = ref Inverse_of_names.empty in
    let inverse_of_consts = ref Inverse_of_consts.empty in
    ignore
      (Name.Map.inter
         (fun to_be_demoted canonical_at_demotion z_inverses ->
           let canonical_element =
             Aliases0.canonicalize aliases canonical_at_demotion
           in
           let z_inverses_neg = Simple.Map.map ( ~- ) z_inverses in
           inverse_of_names
             := Inverse_of_names.union !inverse_of_names
                  (Name.Map.singleton to_be_demoted z_inverses_neg);
           Simple.pattern_match canonical_element
             ~const:(fun const ->
               inverse_of_consts
                 := Inverse_of_consts.union !inverse_of_consts
                      (Reg_width_const.Map.singleton const z_inverses))
             ~name:(fun name ~coercion ->
               let z_inverses =
                 if Coercion.is_id coercion
                 then z_inverses
                 else
                   let inverse_coercion = Coercion.inverse coercion in
                   Simple.Map.map_keys
                     (fun simple ->
                       Simple.apply_coercion_exn simple inverse_coercion)
                     z_inverses
               in
               inverse_of_names
                 := Inverse_of_names.union !inverse_of_names
                      (Name.Map.singleton name z_inverses)))
         demotions (Incremental.current t).inverse_of_names
        : unit Name.Map.t);
    let inverse_of_names = !inverse_of_names in
    let inverse_of_consts = !inverse_of_consts in
    let diff =
      { values = Function.empty; inverse_of_names; inverse_of_consts }
    in
    Incremental.map (union diff) t, aliases

  let interreduce ~difference t aliases =
    let diff = linear_rule_inverse difference.values aliases in
    let diff = { diff with values = Function.empty } in
    Incremental.map (union diff) t
end

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
    { relations : One_relation.t TG.Relation.Map.t;
      switches_on_names : 'a Row_like.t or_gone Name.Map.t;
      switches_on_relations :
        'a Row_like.t or_gone Name.Map.t TG.Relation.Map.t;
      continuation_uses : Apply_cont_rewrite_id.Set.t Continuation.Map.t;
      free_names : Location.Set.t Name.Map.t
    }

  let print _pp ppf
      { relations;
        switches_on_names;
        switches_on_relations;
        continuation_uses;
        free_names = _
      } =
    Format.fprintf ppf
      "@[<hov 1>(@[<hov 1>(relations@ %a)@]@ @[<hov 1>(continuation_uses@ \
       %a)@])@ @[<hov 1>(switch_on_names@ %a)@]@ @[<hov \
       1>(switch_on_relations@ %a)@]@]"
      (TG.Relation.Map.print One_relation.print)
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

  let apply_renaming t renaming =
    let relations =
      TG.Relation.Map.map
        (fun fn -> One_relation.apply_renaming fn renaming)
        t.relations
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
      switches_on_names;
      switches_on_relations;
      continuation_uses = t.continuation_uses;
      free_names
    }

  let empty =
    { relations = TG.Relation.Map.empty;
      switches_on_names = Name.Map.empty;
      switches_on_relations = TG.Relation.Map.empty;
      continuation_uses = Continuation.Map.empty;
      free_names = Name.Map.empty
    }

  let is_empty t =
    TG.Relation.Map.is_empty t.relations
    && Name.Map.is_empty t.switches_on_names
    && TG.Relation.Map.is_empty t.switches_on_relations

  let get_incremental = Incremental.get

  let get_continuation_uses t = t.continuation_uses

  let set_continuation_uses continuation_uses t = { t with continuation_uses }

  let set_incremental = Incremental.set

  let map_incremental = Incremental.map

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

  let add_switch0 ~meet name row_like env t : _ Or_bottom.t =
    if Row_like.is_bottom row_like
    then Bottom
    else
      let meet env case1 case2 =
        Or_bottom.map ~f:(fun case -> case, env) (meet env case1 case2)
      in
      match Name.Map.find_opt name (Incremental.current t) with
      | None -> Ok (Incremental.map (Name.Map.add name (There row_like)) t)
      | Some Gone -> Misc.fatal_error "Cannot add a switch to a demoted name."
      | Some (There old_row_like) -> (
        let meet_result, _env = Row_like.meet ~meet env row_like old_row_like in
        match meet_result with
        | Right_input | Both_inputs -> Ok t
        | Left_input ->
          Ok (Incremental.map (Name.Map.add name (There row_like)) t)
        | New_result row_like ->
          if Row_like.is_bottom row_like
          then Bottom
          else Ok (Incremental.map (Name.Map.add name (There row_like)) t))

  exception Bottom_relation

  let rebuild_switches ~meet ~apply_coercion demotions env t : _ Or_bottom.t =
    let t_ref = ref t in
    match
      Name.Map.inter
        (fun _to_be_demoted canonical_element switch ->
          let switch =
            match switch with There switch -> switch | Gone -> assert false
          in
          Simple.pattern_match canonical_element
            ~const:(fun const ->
              match Row_like.find const switch with
              | Bottom -> raise Bottom_relation
              | Ok _arm -> (* TODO: add arm *) ())
            ~name:(fun name ~coercion ->
              let switch = apply_coercion switch (Coercion.inverse coercion) in
              match add_switch0 ~meet name switch env !t_ref with
              | Bottom -> raise Bottom_relation
              | Ok t -> t_ref := t);
          Gone)
        demotions (Incremental.current t)
    with
    | exception Bottom_relation -> Bottom
    | demoted ->
      let t = !t_ref in
      let current = Name.Map.diff_domains t.current demoted in
      let difference =
        Name.Map.union
          (fun _name _earlier later -> Some later)
          t.difference demoted
      in
      Ok { current; difference }

  let get_relation relation t =
    try TG.Relation.Map.find relation t.relations
    with Not_found -> One_relation.empty

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

  let interredox ~add_arm ~meet switches_on_relations relations t aliases =
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
                            let simple = canonicalize aliases simple in
                            t_ref
                              := add_switch_on_simple ~add_arm ~meet simple
                                   row_like t)
                      values;
                    None)
                switches fn.One_relation.values);
           None)
         switches_on_relations relations);
    !t_ref

  let interredox ~add_arm ~meet ~previous ~current ~difference t aliases =
    let open Or_bottom.Let_syntax in
    (* Seminaive evaluation. *)
    let<* t =
      interredox ~add_arm ~meet previous.switches_on_relations
        difference.relations t aliases
    in
    interredox ~add_arm ~meet difference.switches_on_relations current.relations
      t aliases

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

  let interredox ~previous ~current ~difference t aliases =
    let meet = meet_continuation_uses in
    let add_arm _ t = Or_bottom.Ok t in
    interredox ~add_arm ~meet ~previous ~current ~difference t aliases

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
        (fun _ earlier later -> Some (One_relation.concat ~earlier ~later))
        earlier.relations later.relations
    in
    let concat_or_gone ~earlier ~later =
      match earlier, later with
      | There _, Gone -> Some later
      | There _, There _ -> Some later
      | Gone, _ ->
        (* if true then Some later else let _ = assert false in *)
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

  let canonicalize aliases simple =
    Simple.pattern_match simple
      ~const:(fun _ -> simple)
      ~name:(fun name ~coercion ->
        Simple.apply_coercion_exn
          (Aliases.get_canonical_ignoring_name_mode aliases.Aliases0.aliases
             name)
          coercion)

  let add_relation ~meet relation ~scrutinee:key value aliases t : _ Or_bottom.t
      =
    let open Or_bottom.Let_syntax in
    if Flambda_features.check_light_invariants ()
    then (
      let canonical_key = canonicalize aliases key in
      if not (Simple.equal canonical_key key)
      then Misc.fatal_errorf "Key is not canonical@.";
      let canonical_value = canonicalize aliases value in
      if not (Simple.equal canonical_value value)
      then Misc.fatal_errorf "Value is not canonical@.");
    let t =
      Incremental.map (add_free_names_of_simple key (Relation_arg relation)) t
    in
    let t =
      Incremental.map (add_free_names_of_simple value (Relation_val relation)) t
    in
    let one_relation = Incremental.get (get_relation relation) t in
    let<+ one_relation, aliases =
      One_relation.add ~meet
        ~for_const:(relation_for_const relation)
        ~scrutinee:key value one_relation aliases
    in
    Incremental.set (set_relation relation) one_relation t, aliases

  let add_continuation_use cont use t =
    let continuation_uses = get_incremental get_continuation_uses t in
    let continuation_uses =
      Incremental.map
        (Continuation.Map.add cont (Apply_cont_rewrite_id.Set.singleton use))
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

type relation_extension = One_relation.t

let fold_relations f t acc =
  TG.Relation.Map.fold
    (fun relation table acc -> f relation table acc)
    t.Final.relations acc

let fold_name_relations f (t : relation_extension) acc =
  Name.Map.fold
    (fun value keys acc ->
      Simple.Map.fold
        (fun key count acc ->
          if count > 0
          then
            match Simple.must_be_name key with
            | None -> Misc.fatal_error "Do not"
            | Some (key, coercion) ->
              f key
                (Simple.with_coercion (Simple.name value)
                   (Coercion.inverse coercion))
                acc
          else acc)
        keys acc)
    t.inverse_of_names acc

let fold_constant_relations f (t : relation_extension) acc =
  Reg_width_const.Map.fold
    (fun value keys acc ->
      Simple.Map.fold
        (fun key count acc ->
          if count > 0
          then
            match Simple.must_be_name key with
            | None -> Misc.fatal_error "Do not"
            | Some (name, _coercion) -> f name value acc
          else acc)
        keys acc)
    t.inverse_of_consts acc

let fold_relation_extension f t acc =
  let acc =
    fold_constant_relations
      (fun key value acc -> f key (Simple.const value) acc)
      t acc
  in
  fold_name_relations f t acc

let empty_extension = Final.empty

let is_empty_extension = Final.is_empty

let tick { current; difference } = current, difference

let from_snapshot current = { current; difference = Final.empty }

let concat_extension = Final.concat

exception Bottom_relation

let rebuild_exn ~meet ~demotions aliases0 db =
  let relations = ref TG.Relation.Set.empty in
  let relation_switches = ref TG.Relation.Set.empty in
  let db_ref = ref db in
  let canonical_demotions =
    Name.Map.inter
      (fun to_be_demoted canonical_at_demotion locs ->
        let canonical_element =
          Aliases0.canonicalize aliases0 canonical_at_demotion
        in
        let db = !db_ref in
        let db = Incremental.map (Final.remove_free_name to_be_demoted) db in
        let db =
          Incremental.map
            (Final.add_many_free_names_of_simple canonical_element locs)
            db
        in
        db_ref := db;
        Final.Location.Set.iter
          (fun (loc : Final.Location.t) ->
            match loc with
            | Switch -> ()
            | Relation_switch rel ->
              relation_switches := TG.Relation.Set.add rel !relation_switches
            | Relation_arg rel | Relation_val rel ->
              relations := TG.Relation.Set.add rel !relations)
          locs;
        canonical_element)
      demotions db.current.Final.free_names
  in
  let relation_switches = !relation_switches in
  let relations = !relations in
  let db, aliases =
    TG.Relation.Set.fold
      (fun relation (db, aliases) ->
        let one_relation = Incremental.get (Final.get_relation relation) db in
        match
          One_relation.rebuild ~meet
            ~for_const:(relation_for_const relation)
            canonical_demotions one_relation aliases
        with
        | Bottom -> raise Bottom_relation
        | Ok (one_relation, aliases) ->
          let db =
            Incremental.set (Final.set_relation relation) one_relation db
          in
          db, aliases)
      relations (!db_ref, aliases0)
  in
  let db =
    TG.Relation.Set.fold
      (fun relation db ->
        let one_switch =
          Incremental.get (Final.get_switches_on_relation relation) db
        in
        match
          Final.rebuild_switches ~meet:Final.meet_continuation_uses
            ~apply_coercion:(fun row_like coercion ->
              assert (Coercion.is_id coercion);
              row_like)
            canonical_demotions aliases one_switch
        with
        | Bottom -> raise Bottom_relation
        | Ok one_switch ->
          Incremental.set
            (Final.set_switches_on_relation relation)
            one_switch db)
      relation_switches db
  in
  let switches_on_names = Incremental.get Final.get_switches_on_names db in
  let db =
    match
      Final.rebuild_switches ~meet:Final.meet_continuation_uses
        ~apply_coercion:(fun row_like coercion ->
          assert (Coercion.is_id coercion);
          row_like)
        canonical_demotions aliases switches_on_names
    with
    | Bottom -> raise Bottom_relation
    | Ok switches_on_names ->
      Incremental.set Final.set_switches_on_names switches_on_names db
  in
  db, aliases

let rebuild ~demotions ~binding_time_resolver ~binding_times_and_modes aliases0
    db : _ Or_bottom.t =
  let meet = Aliases0.meet ~binding_time_resolver ~binding_times_and_modes in
  try Ok (rebuild_exn ~meet ~demotions aliases0 db)
  with Bottom_relation -> Bottom

let add_relation ~binding_time_resolver ~binding_times_and_modes aliases0
    database relation ~scrutinee value =
  Format.eprintf "add %a(%a) = %a@." TG.Relation.print relation Simple.print
    scrutinee Simple.print value;
  Final.add_relation
    ~meet:(Aliases0.meet ~binding_time_resolver ~binding_times_and_modes)
    relation ~scrutinee value aliases0 database

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
  (* THIS IS WRONG!!! Must add separately, not concat. *)
  let current = concat_extension ~earlier:t.current ~later:extension in
  let difference = concat_extension ~earlier:t.difference ~later:extension in
  { current; difference }

let make_demotions t types =
  let types =
    Name.Map.inter (fun _ _locs ty -> ty) t.current.Final.free_names types
  in
  Name.Map.filter_map (fun _ ty -> Type_grammar.get_alias_opt ty) types

let interreduce ~previous ~current ~difference aliases =
  let open Or_bottom.Let_syntax in
  let<+ db =
    Final.interredox ~previous ~current:current.current ~difference current
      aliases
  in
  TG.Relation.Map.fold
    (fun relation one_relation db ->
      let rels = Incremental.get (Final.get_relation relation) db in
      let rels =
        One_relation.interreduce ~difference:one_relation rels aliases
      in
      Incremental.set (Final.set_relation relation) rels db)
    difference.Final.relations db

type snapshot = difference
