[@@@warning "-32-60-34"]

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

module V4 = struct
  module Function = ZRel2 (Name) (Simple)
  module Inverse = ZRel2 (Name) (Name)

  type t =
    { values : Function.t;
      inverse : Inverse.t
    }

  let empty = { values = Function.empty; inverse = Inverse.empty }

  let find_opt key t =
    match Name.Map.find_opt key t.values with
    | None -> None
    | Some simples -> (
      match Simple.Map.get_singleton simples with
      | Some (simple, 1) -> Some simple
      | _ -> Misc.fatal_error "Ill-formed.")

  let remove key value t =
    let values = Function.remove (key, value) t.values in
    let inverse =
      Simple.pattern_match value
        ~const:(fun _ -> t.inverse)
        ~name:(fun name ~coercion ->
          assert (Coercion.is_id coercion);
          Inverse.remove (name, key) t.inverse)
    in
    { values; inverse }

  let add key value t =
    let values = Function.add (key, value) t.values in
    let inverse =
      Simple.pattern_match value
        ~const:(fun _ -> t.inverse)
        ~name:(fun name ~coercion ->
          assert (Coercion.is_id coercion);
          Inverse.add (name, key) t.inverse)
    in
    { values; inverse }

  let replace key ~existing_value value t =
    let t = remove key existing_value t in
    add key value t

  let concat ~earlier ~later =
    let values = Function.union earlier.values later.values in
    let inverse = Inverse.union earlier.inverse later.inverse in
    { values; inverse }
end

type 'a incremental =
  { current : 'a;
    difference : 'a
  }

module Incremental0 = struct
  let find_opt ~find_opt key t = find_opt key t.current

  let remove ~find_opt ~remove key t =
    match find_opt key t.current with
    | None -> t
    | Some value ->
      let current = remove key value t.current in
      let difference = remove key value t.difference in
      { current; difference }

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

module Or_gone = struct
  let find_opt ~find_opt key t =
    match find_opt key t with
    | None | Some Gone -> None
    | Some (There value) -> Some value

  let remove ~add ~remove key t =
    let current = remove key t.current in
    let difference = add key Gone t.difference in
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

module V5 = struct
  type t =
    { relations : V4.t TG.Relation.Map.t;
      cached_free_names : unit Name.Map.t
          (* We store these as a [Name.Map.t] rather than a [Name.Set.t] so that
             we can use [diff_domain] with the demotions. *)
    }

  let get_relation relation t =
    try TG.Relation.Map.find relation t.relations with Not_found -> V4.empty

  let set_relation relation table t =
    { t with relations = TG.Relation.Map.add relation table t.relations }

  let add_free_names_of_name name t =
    { t with cached_free_names = Name.Map.add name () t.cached_free_names }

  let add_free_names_of_simple simple t =
    match Simple.must_be_name simple with
    | None -> t
    | Some (name, _coercion) -> add_free_names_of_name name t

  let add_relation ~meet relation key value env t : _ Or_bottom.t =
    let current = get_relation relation t.current in
    let difference = get_relation relation t.difference in
    match
      generic_add
        ~find_opt:(Incremental0.find_opt ~find_opt:V4.find_opt)
        ~replace:
          (Incremental0.replace ~find_opt:V4.find_opt ~add:V4.add
             ~replace:V4.replace)
        ~meet key value env { current; difference }
    with
    | Bottom -> Bottom
    | Ok ({ current; difference }, env) ->
      let current = set_relation relation current t.current in
      let current = add_free_names_of_name key current in
      let current = add_free_names_of_simple value current in
      let difference = set_relation relation difference t.difference in
      let difference = add_free_names_of_name key difference in
      let difference = add_free_names_of_simple value difference in
      Ok ({ current; difference }, env)
end

let did_demote = ref 0

let did_not_demote = ref 0

let print_info () =
  Format.eprintf "demoted %d/%d@." !did_demote (!did_demote + !did_not_demote)

let generic_demote ~find_opt ~replace ~remove ~to_be_demoted ~canonical_key
    ~meet env t : _ Or_bottom.t =
  match find_opt to_be_demoted t with
  | None ->
    incr did_not_demote;
    Ok (t, env)
  | Some value_of_to_be_demoted -> (
    incr did_demote;
    let t = remove to_be_demoted t in
    match find_opt canonical_key t with
    | None ->
      let t = replace canonical_key value_of_to_be_demoted t in
      Ok (t, env)
    | Some value_of_canonical_key ->
      generic_meet_then_add ~replace ~meet
        ~existing_value:value_of_canonical_key canonical_key
        value_of_to_be_demoted env t)

module V2 = struct
  module Inverse = ZRel2 (Simple) (Name)

  (* The [inverse] is a Z-relation that records all of the additions and
     deletions of entries that have been made to the function since it was
     [empty].

     It satisfies the following invariants:

     - The [inverse] map only contains entries exactly equal to [1];

     - For any argument [arg], there is at most one [simple] such that the pair
     [(simple, arg)] is in [inverse]. This is the case if, and only if, [f(arg)
     = simple] is recorded in [values].

     The [difference] field is a Z-relation that records all of the additions
     and deletions of entries that have been made to the function since an
     arbitrary point in the past.

     The [difference] field satisfies the following invariants:

     - The [difference] map only contains entries exactly equal to [-1] or [1];

     - For any argument [arg], there is at most one [simple] such that the pair
     [(simple, arg)] is in [difference] with a positive (hence equal to [1])
     weight, in which case the entry [f(arg) = simple] is recorded in [values].

     Positive entries in the [difference] and [inverse] fields only contain
     canonical names. *)
  type t =
    { values : Simple.t Name.Map.t;
      inverse : Inverse.t;
      difference : Inverse.t
    }

  let apply_renaming_inverse inverse renaming =
    Simple.Map.fold
      (fun simple args inverse ->
        Simple.Map.add
          (Renaming.apply_simple renaming simple)
          (Name.Map.map_keys (Renaming.apply_name renaming) args)
          inverse)
      inverse Simple.Map.empty

  let apply_renaming t renaming =
    let inverse = apply_renaming_inverse t.inverse renaming in
    let difference = apply_renaming_inverse t.difference renaming in
    let values =
      Name.Map.fold
        (fun name value values ->
          Name.Map.add
            (Renaming.apply_name renaming name)
            (Renaming.apply_simple renaming value)
            values)
        t.values Name.Map.empty
    in
    { values; inverse; difference }

  (* We only need to keep track of the inverses for extensions, as we can
     recompute the changes to the function from the changes to the inverses. *)
  type extension = Inverse.t

  let apply_renaming_extension = apply_renaming_inverse

  let tick t = { t with difference = Inverse.empty }, t.difference

  let extension_bindings (extension : extension) =
    Simple.Map.fold
      (fun simple args bindings ->
        Name.Map.fold
          (fun arg count bindings ->
            if count > 0 then (arg, simple) :: bindings else bindings)
          args bindings)
      extension []

  let print_extension ppf (extension : extension) =
    if Inverse.is_empty extension
    then Format.fprintf ppf "{}"
    else
      Format.fprintf ppf "@[<hov 1>{%a}@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
           (fun ppf (key, datum) ->
             Format.fprintf ppf "@[<hov 1>(%a@ %a)@]" Name.print key
               Simple.print datum))
        (extension_bindings extension)

  let add_extension ext t =
    let inverse = Inverse.union t.inverse ext in
    let difference = Inverse.union t.difference ext in
    (* We could make this part a bit simpler by dropping information related to
       demoted elements through another mechanism, at the cost of increasing the
       complexity of the interface. *)
    let added, removed =
      Simple.Map.fold
        (fun value args (added, removed) ->
          Name.Map.fold
            (fun arg cnt (added, removed) ->
              if cnt > 0
              then Name.Map.add arg value added, removed
              else added, Name.Map.add arg () removed)
            args (added, removed))
        ext
        (Name.Map.empty, Name.Map.empty)
    in
    let removed = Name.Map.diff_domains removed added in
    let values = Name.Map.diff_domains t.values removed in
    let values =
      Name.Map.union (fun _ _old_value value -> Some value) values added
    in
    { values; inverse; difference }

  let concat_extension ~earlier ~later = Inverse.union earlier later

  let empty =
    { values = Name.Map.empty;
      inverse = Inverse.empty;
      difference = Inverse.empty
    }

  let find_opt key { values; _ } = Name.Map.find_opt key values

  let replace_existing key value ~existing t =
    let t =
      match existing with
      | None -> t
      | Some existing_value ->
        let inverse = Inverse.remove (existing_value, key) t.inverse in
        let difference = Inverse.remove (existing_value, key) t.difference in
        { t with inverse; difference }
    in
    let values = Name.Map.add key value t.values in
    let inverse = Inverse.add (value, key) t.inverse in
    let difference = Inverse.add (value, key) t.difference in
    { values; inverse; difference }

  let replace key value t =
    replace_existing key value ~existing:(Name.Map.find_opt key t.values) t

  let remove_existing key ~existing t =
    match existing with
    | None -> t
    | Some existing_value ->
      let values = Name.Map.remove key t.values in
      let inverse = Inverse.remove (existing_value, key) t.inverse in
      let difference = Inverse.remove (existing_value, key) t.difference in
      { values; inverse; difference }

  let remove key t =
    remove_existing key ~existing:(Name.Map.find_opt key t.values) t

  let add ~meet key value env t =
    generic_add ~find_opt ~replace ~meet key value env t

  let demote ~for_const ~to_be_demoted ~canonical_element ~meet env t =
    (* First demote in values. Make sure we don't add names with coercions to
       the mix, as we wouldn't properly keep track of them. *)
    let t =
      let to_be_demoted_simple = Simple.name to_be_demoted in
      match Simple.Map.find_opt to_be_demoted_simple t.inverse with
      | None -> t
      | Some args ->
        let has_coercion =
          not (Coercion.is_id (Simple.coercion canonical_element))
        in
        Name.Map.fold
          (fun name count t ->
            if count > 0
            then
              if has_coercion
              then remove_existing name ~existing:(Some to_be_demoted_simple) t
              else
                replace_existing name canonical_element
                  ~existing:(Some to_be_demoted_simple) t
            else t)
          args t
    in
    (* Next demote in arguments. *)
    Simple.pattern_match canonical_element
      ~const:(fun const ->
        match find_opt to_be_demoted t with
        | None ->
          incr did_not_demote;
          Or_bottom.Ok (t, env)
        | Some existing_value ->
          incr did_demote;
          let open Or_bottom.Let_syntax in
          let<* value_for_const = for_const const in
          let<+ _, env =
            meet env existing_value (Simple.const value_for_const)
          in
          remove to_be_demoted t, env)
      ~name:(fun name ~coercion ->
        (* Supporting coercions here would require applying them to the value
           during [meet], but we don't expect meaningful relations for names
           with coercions anyways. *)
        if not (Coercion.is_id coercion)
        then Or_bottom.Ok (remove to_be_demoted t, env)
        else
          generic_demote ~find_opt ~replace ~remove ~to_be_demoted
            ~canonical_key:name ~meet env t)
end

module Unfunc = V2

(* TODO: also store switches.
 * is_int : 'a Reg_width_const.Map.t Name.Map.t
 *)

module Continuation_uses = struct
  include ZRel2 (Continuation) (Apply_cont_rewrite_id)

  let apply_renaming t renaming =
    Continuation.Map.map_keys (Renaming.apply_continuation renaming) t

  let concat ~earlier ~later = union earlier later
end

module type S = sig
  type t

  val empty : t

  val apply_renaming : t -> Renaming.t -> t

  val concat : earlier:t -> later:t -> t
end

module type Lattice = sig
  type t

  val apply_renaming : t -> Renaming.t -> t
end

module type Incremental_lattice = sig
  include Lattice

  val concat : earlier:t -> later:t -> t
end

module Incremental_simple = struct
  include Simple

  let concat ~earlier:_ ~later = later
end

module Set_of_uses = struct
  type t = Apply_cont_rewrite_id.Set.t

  let apply_renaming t _renaming = t

  let concat ~earlier:_ ~later = later
end

module Unary_function (Value : Incremental_lattice) = struct
  type t = Value.t Name.Map.t

  let concat ~earlier ~later =
    Name.Map.union
      (fun _ earlier later -> Some (Value.concat ~earlier ~later))
      earlier later

  let remove_demoted_names (t : t) demoted_names : t =
    Name.Map.diff_domains t demoted_names

  let apply_renaming t renaming =
    Name.Map.fold
      (fun name value t ->
        Name.Map.add
          (Renaming.apply_name renaming name)
          (Value.apply_renaming value renaming)
          t)
      t Name.Map.empty
end

module Relation = Unary_function (Incremental_simple)

module Extension = struct
  module Id = struct
    include Numeric_types.Int

    let fresh =
      let cnt = ref 0 in
      fun () ->
        incr cnt;
        !cnt
  end

  type t =
    { relations : Relation.t TG.Relation.Map.t;
      continuation_uses : Continuation_uses.t
    }

  let apply_renaming { relations; continuation_uses } renaming =
    let relations =
      TG.Relation.Map.map
        (fun relation -> Relation.apply_renaming relation renaming)
        relations
    in
    { relations; continuation_uses }
end

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

  let empty =
    { known = Reg_width_const.Map.empty; other = Ok Extension.Id.Set.empty }

  let find const { known; other } =
    match Reg_width_const.Map.find_opt const known with
    | None -> other
    | Some case -> Or_bottom.Ok case
end

module Switch = struct
  type t =
    { current : Extension.Id.Set.t Row_like.t or_gone Name.Map.t;
      difference : Extension.Id.Set.t Row_like.t or_gone Name.Map.t
    }

  let print_extension ppf extension =
    Name.Map.print
      (print_or_gone (Row_like.print Extension.Id.Set.print))
      ppf extension

  let empty = { current = Name.Map.empty; difference = Name.Map.empty }

  let is_empty { current; _ } = Name.Map.is_empty current

  let find_opt name { current; _ } =
    match Name.Map.find_opt name current with
    | None | Some Gone -> None
    | Some (There row_like) -> Some row_like

  let remove name { current; difference } =
    let current = Name.Map.remove name current in
    let difference = Name.Map.add name Gone difference in
    { current; difference }

  let replace name row_like { current; difference } =
    let current = Name.Map.add name (There row_like) current in
    let difference = Name.Map.add name (There row_like) difference in
    { current; difference }

  type extension = Extension.Id.Set.t Row_like.t or_gone Name.Map.t

  let empty_extension = Name.Map.empty

  let is_empty_extension = Name.Map.is_empty

  let concat_extension ~earlier ~later =
    Name.Map.union (fun _ _row_like1 row_like2 -> Some row_like2) earlier later

  let add_extension t extension =
    let current =
      Name.Map.fold
        (fun name row_like current ->
          match row_like with
          | Gone -> Name.Map.remove name current
          | There row_like -> Name.Map.add name (There row_like) current)
        extension t.current
    in
    let difference = concat_extension ~earlier:t.difference ~later:extension in
    { current; difference }

  let apply_renaming_extension extension renaming =
    Name.Map.map_keys (Renaming.apply_name renaming) extension

  let apply_renaming { current; difference } renaming =
    let current = Name.Map.map_keys (Renaming.apply_name renaming) current in
    let difference =
      Name.Map.map_keys (Renaming.apply_name renaming) difference
    in
    { current; difference }

  let tick t = { t with difference = Name.Map.empty }, t.difference

  let meet_row_like ~meet row_like1 row_like2 env =
    Or_bottom.Ok (Row_like.meet ~meet row_like1 row_like2 env)

  let meet_extension_id_set env set1 set2 : _ Or_bottom.t =
    match
      Extension.Id.Set.subset set1 set2, Extension.Id.Set.subset set2 set1
    with
    | true, true -> Ok (Both_inputs, env)
    | true, false -> Ok (Right_input, env)
    | false, true -> Ok (Left_input, env)
    | false, false ->
      let set = Extension.Id.Set.union set1 set2 in
      Ok (New_result set, env)

  let demote ~for_const ~to_be_demoted ~canonical_element env t =
    Simple.pattern_match canonical_element
      ~const:(fun const ->
        match find_opt to_be_demoted t with
        | None -> Or_bottom.Ok (t, env)
        | Some row_like ->
          let open Or_bottom.Let_syntax in
          let<* const = for_const const in
          let<+ extensions = Row_like.find const row_like in
          t, Extension.Id.Set.union extensions env)
      ~name:(fun name ~coercion ->
        if not (Coercion.is_id coercion)
        then Or_bottom.Ok (remove to_be_demoted t, env)
        else
          generic_demote ~find_opt ~replace ~remove ~to_be_demoted
            ~canonical_key:name
            ~meet:(meet_row_like ~meet:meet_extension_id_set)
            env t)
end

module Switches = struct
  type t =
    { on_names : Switch.t;
      on_relations : Switch.t TG.Relation.Map.t
    }

  type extension =
    { on_names_extension : Switch.extension;
      on_relations_extension : Switch.extension TG.Relation.Map.t
    }

  let empty_extension =
    { on_names_extension = Switch.empty_extension;
      on_relations_extension = TG.Relation.Map.empty
    }

  let tick { on_names; on_relations } =
    let on_names, on_names_extension = Switch.tick on_names in
    let on_relations, on_relations_extension =
      TG.Relation.Map.fold
        (fun relation switch (on_relations, on_relations_extension) ->
          let switch, switch_extension = Switch.tick switch in
          let on_relations = TG.Relation.Map.add relation switch on_relations in
          let on_relations_extension =
            if Switch.is_empty_extension switch_extension
            then on_relations_extension
            else
              TG.Relation.Map.add relation switch_extension
                on_relations_extension
          in
          on_relations, on_relations_extension)
        on_relations
        (TG.Relation.Map.empty, TG.Relation.Map.empty)
    in
    { on_names; on_relations }, { on_names_extension; on_relations_extension }

  let empty = { on_names = Switch.empty; on_relations = TG.Relation.Map.empty }

  let is_empty { on_names; on_relations } =
    Switch.is_empty on_names && TG.Relation.Map.is_empty on_relations

  let is_empty_extension { on_names_extension; on_relations_extension } =
    Switch.is_empty_extension on_names_extension
    && TG.Relation.Map.is_empty on_relations_extension

  let apply_renaming_extension { on_names_extension; on_relations_extension }
      renaming =
    let on_names_extension =
      Switch.apply_renaming_extension on_names_extension renaming
    in
    let on_relations_extension =
      TG.Relation.Map.map
        (fun switch -> Switch.apply_renaming_extension switch renaming)
        on_relations_extension
    in
    { on_names_extension; on_relations_extension }

  let apply_renaming { on_names; on_relations } renaming =
    let on_names = Switch.apply_renaming on_names renaming in
    let on_relations =
      TG.Relation.Map.map
        (fun switch -> Switch.apply_renaming switch renaming)
        on_relations
    in
    { on_names; on_relations }

  let concat_extension ~earlier ~later =
    let on_names_extension =
      Switch.concat_extension ~earlier:earlier.on_names_extension
        ~later:later.on_names_extension
    in
    let on_relations_extension =
      TG.Relation.Map.union
        (fun _ earlier later -> Some (Switch.concat_extension ~earlier ~later))
        earlier.on_relations_extension later.on_relations_extension
    in
    { on_names_extension; on_relations_extension }

  let add_extension { on_names; on_relations }
      { on_names_extension; on_relations_extension } =
    let on_names = Switch.add_extension on_names on_names_extension in
    let on_relations =
      TG.Relation.Map.fold
        (fun relation switch_extension on_relations ->
          TG.Relation.Map.update relation
            (function
              | None -> None
              | Some switch ->
                let switch = Switch.add_extension switch switch_extension in
                if Switch.is_empty switch then None else Some switch)
            on_relations)
        on_relations_extension on_relations
    in
    { on_names; on_relations }

  exception Bottom_equation

  let demote ~to_be_demoted ~canonical_element env t =
    let open Or_bottom.Let_syntax in
    let<* on_names, env =
      Switch.demote
        ~for_const:(fun const -> Or_bottom.Ok const)
        ~to_be_demoted ~canonical_element env t.on_names
    in
    match
      TG.Relation.Map.fold
        (fun relation switch (on_relations, env) ->
          match
            Switch.demote
              ~for_const:(relation_for_const relation)
              ~to_be_demoted ~canonical_element env switch
          with
          | Ok (switch, env) ->
            TG.Relation.Map.add relation switch on_relations, env
          | Bottom -> raise Bottom_equation)
        t.on_relations
        (TG.Relation.Map.empty, env)
    with
    | on_relations, env -> Ok ({ on_names; on_relations }, env)
    | exception Bottom_equation -> Bottom
end

module Incremental = struct
  module Make (Full : S) = struct
    type t =
      { current : Full.t;
        difference : Full.t
      }

    type extension = Full.t

    let empty = { current = Full.empty; difference = Full.empty }

    let apply_renaming { current; difference } renaming =
      { current = Full.apply_renaming current renaming;
        difference = Full.apply_renaming difference renaming
      }

    let tick { current; difference } =
      { current; difference = Full.empty }, difference

    let add_extension ext t =
      { current = Full.concat ~earlier:t.current ~later:ext;
        difference = Full.concat ~earlier:t.difference ~later:ext
      }
  end

  module Continuation_uses = Make (Continuation_uses)
end

type ('a, 'b, 'c) relations =
  { is_int : 'a;
    get_tag : 'a;
    is_null : 'a;
    where : unit Name.Map.t;
    continuation_uses : 'b;
    extensions : legacy_extension Or_unknown_or_bottom.t Extension.Id.Map.t;
    switches : 'c
  }

and legacy = (Unfunc.t, Incremental.Continuation_uses.t, Switches.t) relations

and legacy_extension =
  (Unfunc.extension, Continuation_uses.t, Switches.extension) relations

let invariant t =
  let inverse_invariant (inverse : Unfunc.Inverse.t) =
    Simple.Map.for_all
      (fun _ args -> Name.Map.for_all (fun _ cnt -> cnt = 1) args)
      inverse
  in
  inverse_invariant t.is_int.Unfunc.inverse
  && inverse_invariant t.get_tag.Unfunc.inverse
  && inverse_invariant t.is_null.Unfunc.inverse

let extension_invariant t =
  let inverse_invariant (inverse : Unfunc.Inverse.t) =
    Simple.Map.for_all
      (fun _ args -> Name.Map.for_all (fun _ cnt -> cnt = 1 || cnt = -1) args)
      inverse
  in
  inverse_invariant t.is_int
  && inverse_invariant t.get_tag
  && inverse_invariant t.is_null

let empty_extension =
  { is_int = Unfunc.Inverse.empty;
    get_tag = Unfunc.Inverse.empty;
    is_null = Unfunc.Inverse.empty;
    where = Name.Map.empty;
    continuation_uses = Continuation_uses.empty;
    extensions = Extension.Id.Map.empty;
    switches = Switches.empty_extension
  }

let rec apply_renaming_extension
    { is_int; get_tag; is_null; where; continuation_uses; extensions; switches }
    renaming =
  let is_int = Unfunc.apply_renaming_extension is_int renaming in
  let get_tag = Unfunc.apply_renaming_extension get_tag renaming in
  let is_null = Unfunc.apply_renaming_extension is_null renaming in
  let where = Name.Map.map_keys (Renaming.apply_name renaming) where in
  let continuation_uses =
    Continuation_uses.apply_renaming continuation_uses renaming
  in
  let extensions =
    Extension.Id.Map.map
      (fun extension ->
        Or_unknown_or_bottom.map extension ~f:(fun extension ->
            apply_renaming_extension extension renaming))
      extensions
  in
  let switches = Switches.apply_renaming_extension switches renaming in
  { is_int; get_tag; is_null; where; continuation_uses; extensions; switches }

let apply_renaming
    { is_int; get_tag; is_null; where; continuation_uses; extensions; switches }
    renaming =
  let is_int = Unfunc.apply_renaming is_int renaming in
  let get_tag = Unfunc.apply_renaming get_tag renaming in
  let is_null = Unfunc.apply_renaming is_null renaming in
  let where = Name.Map.map_keys (Renaming.apply_name renaming) where in
  let continuation_uses =
    Incremental.Continuation_uses.apply_renaming continuation_uses renaming
  in
  let extensions =
    Extension.Id.Map.map
      (fun extension ->
        Or_unknown_or_bottom.map extension ~f:(fun extension ->
            apply_renaming_extension extension renaming))
      extensions
  in
  let switches = Switches.apply_renaming switches renaming in
  { is_int; get_tag; is_null; where; continuation_uses; extensions; switches }

let is_empty_extension
    { is_int;
      get_tag;
      is_null;
      continuation_uses;
      extensions;
      switches;
      where = _
    } =
  Unfunc.Inverse.is_empty is_int
  && Unfunc.Inverse.is_empty get_tag
  && Unfunc.Inverse.is_empty is_null
  && Continuation_uses.is_empty continuation_uses
  && Extension.Id.Map.is_empty extensions
  && Switches.is_empty_extension switches

let tick (t : legacy) =
  let is_int, is_int_extension = Unfunc.tick t.is_int in
  let get_tag, get_tag_extension = Unfunc.tick t.get_tag in
  let is_null, is_null_extension = Unfunc.tick t.is_null in
  let continuation_uses, continuation_uses_extension =
    Incremental.Continuation_uses.tick t.continuation_uses
  in
  let where = t.where in
  let switches, switches_extension = Switches.tick t.switches in
  ( { is_int;
      get_tag;
      is_null;
      continuation_uses;
      where;
      extensions = t.extensions;
      switches
    },
    { is_int = is_int_extension;
      get_tag = get_tag_extension;
      is_null = is_null_extension;
      continuation_uses = continuation_uses_extension;
      extensions = Extension.Id.Map.empty;
      where;
      switches = switches_extension
    } )

let print ppf (ext : legacy) =
  Format.fprintf ppf "@[<hov 1>(is_int@ %a)@]" Unfunc.print_extension
    ext.is_int.inverse;
  Format.fprintf ppf "@[<hov 1>(get_tag@ %a)@]" Unfunc.print_extension
    ext.get_tag.inverse;
  Format.fprintf ppf "@[<hov 1>(continuation_uses@ %a)@]"
    Continuation_uses.print ext.continuation_uses.current

let print_extension ppf (ext : legacy_extension) =
  Format.fprintf ppf "@[<hov 1>(is_int@ %a)@]" Unfunc.print_extension ext.is_int;
  Format.fprintf ppf "@[<hov 1>(get_tag@ %a)@]" Unfunc.print_extension
    ext.get_tag;
  Format.fprintf ppf "@[<hov 1>(is_null@ %a)@]" Unfunc.print_extension
    ext.is_null;
  Format.fprintf ppf "@[<hov 1>(continuation_uses@ %a)@]"
    Continuation_uses.print ext.continuation_uses

let concat_extension ~earlier ~later =
  { is_int = Unfunc.concat_extension ~earlier:earlier.is_int ~later:later.is_int;
    get_tag =
      Unfunc.concat_extension ~earlier:earlier.get_tag ~later:later.get_tag;
    is_null =
      Unfunc.concat_extension ~earlier:earlier.is_null ~later:later.is_null;
    continuation_uses =
      Continuation_uses.union earlier.continuation_uses later.continuation_uses;
    extensions =
      Extension.Id.Map.union
        (fun _ _ext1 ext2 -> Some ext2)
        earlier.extensions later.extensions;
    switches =
      Switches.concat_extension ~earlier:earlier.switches ~later:later.switches;
    where = later.where
  }

let add_extension t ext =
  { is_int = Unfunc.add_extension ext.is_int t.is_int;
    get_tag = Unfunc.add_extension ext.get_tag t.get_tag;
    is_null = Unfunc.add_extension ext.is_null t.is_null;
    continuation_uses =
      Incremental.Continuation_uses.add_extension ext.continuation_uses
        t.continuation_uses;
    extensions =
      Extension.Id.Map.union
        (fun _ _ext1 ext2 -> Some ext2)
        t.extensions ext.extensions;
    switches = Switches.add_extension t.switches ext.switches;
    where = ext.where
  }

let empty =
  { is_int = Unfunc.empty;
    get_tag = Unfunc.empty;
    is_null = Unfunc.empty;
    continuation_uses = Incremental.Continuation_uses.empty;
    extensions = Extension.Id.Map.empty;
    where = Name.Map.empty;
    switches = Switches.empty
  }

let add_to_where key value where =
  Name.Map.add key ()
  @@ Simple.pattern_match value
       ~const:(fun _ -> where)
       ~name:(fun name ~coercion:_ -> Name.Map.add name () where)

let add_is_int ~meet key value env t =
  let open Or_bottom.Let_syntax in
  let<+ is_int, env = Unfunc.add ~meet key value env t.is_int in
  let where = add_to_where key value t.where in
  { t with is_int; where }, env

let add_get_tag ~meet key value env t =
  let open Or_bottom.Let_syntax in
  let<+ get_tag, env = Unfunc.add ~meet key value env t.get_tag in
  let where = add_to_where key value t.where in
  { t with get_tag; where }, env

let add_is_null ~meet key value env t =
  let open Or_bottom.Let_syntax in
  let<+ is_null, env = Unfunc.add ~meet key value env t.is_null in
  let where = add_to_where key value t.where in
  { t with is_null; where }, env

let add_continuation_use cont id (t : legacy) =
  let current = t.continuation_uses.current in
  if Continuation_uses.mem (cont, id) current
  then t
  else
    let current = Continuation_uses.add (cont, id) current in
    let difference = t.continuation_uses.difference in
    let difference = Continuation_uses.add (cont, id) difference in
    let continuation_uses =
      { Incremental.Continuation_uses.current; difference }
    in
    { t with continuation_uses }

let activate eid (t : legacy) : legacy Or_bottom.t =
  match Extension.Id.Map.find_opt eid t.extensions with
  | None -> Ok t
  | Some extension -> (
    match extension with
    | Bottom -> Bottom
    | Unknown -> Ok t
    | Ok extension ->
      (* XXX: need to canonicalise etc. *)
      let extensions =
        Extension.Id.Map.add eid Or_unknown_or_bottom.Unknown t.extensions
      in
      let t = { t with extensions } in
      Ok (add_extension t extension))

let demote ~to_be_demoted ~canonical_element ~meet env t =
  let open Or_bottom.Let_syntax in
  let<* is_int, env =
    Unfunc.demote
      ~for_const:(fun const ->
        match Reg_width_const.is_tagged_immediate const with
        | None -> Or_bottom.Bottom
        | Some _ ->
          Or_bottom.Ok (Reg_width_const.naked_immediate Targetint_31_63.one))
      ~to_be_demoted ~canonical_element ~meet env t.is_int
  in
  let<* is_null, env =
    Unfunc.demote
      ~for_const:(fun const ->
        match Reg_width_const.is_tagged_immediate const with
        | None -> Or_bottom.Bottom
        | Some _ ->
          Or_bottom.Ok (Reg_width_const.naked_immediate Targetint_31_63.zero))
      ~to_be_demoted ~canonical_element ~meet env t.is_null
  in
  let<* get_tag, env =
    Unfunc.demote
      ~for_const:(fun _ -> Or_bottom.Bottom)
      ~to_be_demoted ~canonical_element ~meet env t.get_tag
  in
  let<* switches, to_activate =
    Switches.demote ~to_be_demoted ~canonical_element Extension.Id.Set.empty
      t.switches
  in
  let where =
    Name.Map.remove to_be_demoted
    @@ Simple.pattern_match canonical_element
         ~const:(fun _ -> t.where)
         ~name:(fun name ~coercion:_ -> Name.Map.add name () t.where)
  in
  let continuation_uses = t.continuation_uses in
  let extensions = t.extensions in
  let t =
    { is_int; get_tag; is_null; where; continuation_uses; extensions; switches }
  in
  let<+ t =
    Extension.Id.Set.fold
      (fun extension_id t ->
        let<* t = t in
        activate extension_id t)
      to_activate (Or_bottom.Ok t)
  in
  t, env

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

  let rebuild ~binding_time_resolver ~binding_times_and_modes f t acc =
    let meet = meet ~binding_time_resolver ~binding_times_and_modes in
    let rec rebuild all_demotions t acc =
      if Name.Map.is_empty t.demotions
      then Or_bottom.Ok (acc, { t with demotions = all_demotions })
      else
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
            t.demotions
            (acc, { t with demotions = Name.Map.empty })
        with
        | acc, t ->
          let all_demotions =
            Name.Map.union
              (fun _ _simple1 simple2 -> Some simple2)
              all_demotions t.demotions
          in
          rebuild all_demotions t acc
        | exception Bottom_equation -> Or_bottom.Bottom
    in
    rebuild Name.Map.empty t acc
end

module Final = struct
  type 'a t =
    { relations : Function.t TG.Relation.Map.t;
      inverse_relations : Inverse.t TG.Relation.Map.t;
      switches_on_names : 'a Row_like.t or_gone Name.Map.t;
      switches_on_relations :
        'a Row_like.t or_gone Name.Map.t TG.Relation.Map.t;
      continuation_uses : Apply_cont_rewrite_id.Set.t Continuation.Map.t;
      free_names : unit Name.Map.t
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

  let get_relations t = t.relations

  let create_switch ~default ~arms:known =
    let other : _ Or_bottom.t =
      match default with None -> Bottom | Some other -> Ok other
    in
    Row_like.{ known; other }

  let add_switch0 ~meet name row_like env t =
    let open Or_bottom.Let_syntax in
    let meet env case1 case2 =
      let meet env case1 case2 =
        Or_bottom.map ~f:(fun case -> case, env) (meet env case1 case2)
      in
      Or_bottom.Ok (Row_like.meet ~meet env case1 case2)
    in
    let find_opt name switches =
      match Name.Map.find_opt name switches with
      | None | Some Gone -> None
      | Some (There value) -> Some value
    in
    let add name value switches = Name.Map.add name (There value) switches in
    let replace name ~existing_value:_ value switches =
      add name value switches
    in
    let<+ t, new_env =
      generic_add
        ~find_opt:(Incremental0.find_opt ~find_opt)
        ~replace:
          (Incremental0.replace ~find_opt:Name.Map.find_opt ~add ~replace)
        ~meet name row_like env t
    in
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

  let find_relation_on_name relation name t =
    Option.bind
      (TG.Relation.Map.find_opt relation t.relations)
      (Function.find_opt name)

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

  let add_free_name name t =
    { t with free_names = Name.Map.add name () t.free_names }

  let remove_free_name name t =
    { t with free_names = Name.Map.remove name t.free_names }

  let add_free_names_of_simple simple t =
    Simple.pattern_match simple
      ~const:(fun _ -> t)
      ~name:(fun name ~coercion:_ -> add_free_name name t)

  let add_switch_on_relation relation name ?default ~arms t =
    let t = map_incremental (add_free_name name) t in
    add_switch_on_relation ~meet:meet_continuation_uses relation name ?default
      ~arms t

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
      | Gone, _ -> Misc.fatal_error "Already gone! What?"
    in
    let switches_on_names =
      Name.Map.union
        (fun _ earlier later -> concat_or_gone ~earlier ~later)
        earlier.switches_on_names later.switches_on_names
    in
    (* Switches on relations are moved to switches on expressions.

       Note that we do not need to remove the [demoted_names] because those are
       included in the [relations] already. *)
    let earlier_switches_on_relations =
      TG.Relation.Map.merge
        (fun _ earlier_switches later ->
          match earlier_switches, later with
          | None, _ | _, None -> earlier_switches
          | Some earlier_switches, Some later ->
            Some (Name.Map.diff_domains earlier_switches later))
        earlier.switches_on_relations later.relations
    in
    let switches_on_relations =
      TG.Relation.Map.union
        (fun _ earlier later ->
          Some
            (Name.Map.union
               (fun _ earlier later -> concat_or_gone ~earlier ~later)
               earlier later))
        earlier_switches_on_relations later.switches_on_relations
    in
    { relations;
      inverse_relations;
      switches_on_names;
      switches_on_relations;
      continuation_uses = later.continuation_uses;
      free_names =
        Name.Map.union
          (fun _ () () -> Some ())
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
    let t = map_incremental (add_free_name key) t in
    let t = map_incremental (add_free_names_of_simple value) t in
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

module Old_api = struct
  type t = Set_of_uses.t Continuation.Map.t Final.t incremental

  let print ppf t =
    Final.print
      (Continuation.Map.print Apply_cont_rewrite_id.Set.print)
      ppf t.current

  let empty = { current = Final.empty; difference = Final.empty }

  let apply_renaming t renaming =
    Final.map_incremental (fun t -> Final.apply_renaming t renaming) t

  type extension = Set_of_uses.t Continuation.Map.t Final.t

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

  let tick { current; difference } =
    { current; difference = Final.empty }, difference

  let concat_extension = Final.concat

  let demote_in_function ~to_be_demoted ~canonical_element ~meet aliases (t : t)
      =
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

  let demote_in_inverse ~to_be_demoted ~canonical_element ~meet aliases (t : t)
      =
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
                  Final.remove_relation relation key
                    (Simple.name to_be_demoted)
                    t
                in
                Final.add_relation ~meet relation key canonical_element aliases
                  t)
            keys result)
      t.current.inverse_relations
      (Or_bottom.Ok (t, aliases))

  let demote ~to_be_demoted ~canonical_element ~meet aliases t =
    let open Or_bottom.Let_syntax in
    let<* t, aliases =
      demote_in_function ~to_be_demoted ~canonical_element ~meet aliases t
    in
    let<+ t, aliases =
      demote_in_inverse ~to_be_demoted ~canonical_element ~meet aliases t
    in
    let t =
      match Name.Map.find_opt to_be_demoted t.current.Final.free_names with
      | None -> t
      | Some () ->
        let t =
          Final.map_incremental (Final.remove_free_name to_be_demoted) t
        in
        Final.map_incremental
          (Final.add_free_names_of_simple canonical_element)
          t
    in
    t, aliases

  let rebuild ~binding_time_resolver ~binding_times_and_modes aliases0 database
      =
    Aliases0.rebuild ~binding_time_resolver ~binding_times_and_modes demote
      aliases0 database

  let add_relation ~binding_time_resolver ~binding_times_and_modes aliases0
      database relation name value =
    Final.add_relation
      ~meet:(Aliases0.meet ~binding_time_resolver ~binding_times_and_modes)
      relation name value aliases0 database

  let add_continuation_use cont use t = Final.add_continuation_use cont use t

  let continuation_uses = Final.continuation_uses

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
end

include Old_api

let make_demotions t types =
  let types =
    Name.Map.inter (fun _ () ty -> ty) t.current.Final.free_names types
  in
  Name.Map.filter_map (fun _ ty -> Type_grammar.get_alias_opt ty) types

let interreduce ~previous ~current ~difference =
  Final.interredox ~previous:previous.current ~current:current.current
    ~difference current
