module TE = Typing_env
module TEE = Typing_env_extension
module TG = Type_grammar
module ET = Expand_head.Expanded_type

module Equal_types = struct
  type env =
    { left_env : TE.t;
      right_env : TE.t;
      meet_type : TE.meet_type
    }

  let equal_row_like_index_domain ~equal_lattice
      (t1 : _ TG.row_like_index_domain) (t2 : _ TG.row_like_index_domain) =
    match t1, t2 with
    | Known t1, Known t2 -> equal_lattice t1 t2
    | Known _, At_least _ | At_least _, Known _ -> false
    | At_least t1, At_least t2 -> equal_lattice t1 t2

  let equal_row_like_index ~equal_lattice ~equal_shape
      (t1 : (_, _) TG.row_like_index) (t2 : (_, _) TG.row_like_index) =
    equal_row_like_index_domain ~equal_lattice t1.domain t2.domain
    && equal_shape t1.shape t2.shape

  let equal_env_extension ~equal_type env (ext1 : TG.env_extension)
      (ext2 : TG.env_extension) =
    let shared_names =
      Name.Map.merge
        (fun name ty1 ty2 ->
          match ty1, ty2 with
          | None, None -> None
          | Some ty1, Some _ -> Some (TG.kind ty1)
          | Some ty1, None ->
            if TE.mem ~min_name_mode:Name_mode.in_types env.right_env name
            then Some (TG.kind ty1)
            else None
          | None, Some ty2 ->
            if TE.mem ~min_name_mode:Name_mode.in_types env.left_env name
            then Some (TG.kind ty2)
            else None)
        (TEE.to_map ext1) (TEE.to_map ext2)
    in
    let left_env =
      TE.add_env_extension env.left_env ext1 ~meet_type:env.meet_type
    in
    let right_env =
      TE.add_env_extension env.left_env ext1 ~meet_type:env.meet_type
    in
    let env = { env with left_env; right_env } in
    Name.Map.for_all
      (fun name kind ->
        let left_canonical =
          TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types
            env.left_env (Simple.name name)
        in
        let left_ty =
          Simple.pattern_match left_canonical
            ~const:(fun _ -> TG.alias_type_of kind left_canonical)
            ~name:(fun name ~coercion ->
              TG.apply_coercion (TE.find env.left_env name (Some kind)) coercion)
        in
        let right_canonical =
          TE.get_canonical_simple_exn ~min_name_mode:Name_mode.in_types
            env.right_env (Simple.name name)
        in
        let right_ty =
          Simple.pattern_match right_canonical
            ~const:(fun _ -> TG.alias_type_of kind right_canonical)
            ~name:(fun name ~coercion ->
              TG.apply_coercion
                (TE.find env.right_env name (Some kind))
                coercion)
        in
        let is_equal = equal_type env left_ty right_ty in
        if (not is_equal) && Flambda_features.debug_flambda2 ()
        then Format.eprintf "NOT equal: %a@." Name.print name;
        is_equal)
      shared_names

  let equal_row_like_case ~equal_type ~equal_maps_to ~equal_lattice ~equal_shape
      env (t1 : (_, _, _) TG.row_like_case) (t2 : (_, _, _) TG.row_like_case) =
    match
      ( TE.add_env_extension_strict env.left_env t1.env_extension
          ~meet_type:env.meet_type,
        TE.add_env_extension_strict env.right_env t2.env_extension
          ~meet_type:env.meet_type )
    with
    | Or_bottom.Bottom, Or_bottom.Bottom -> true
    | Or_bottom.Ok _, Or_bottom.Bottom | Or_bottom.Bottom, Or_bottom.Ok _ ->
      false
    | Or_bottom.Ok left_env, Or_bottom.Ok right_env ->
      let both_env = { env with left_env; right_env } in
      equal_row_like_index ~equal_lattice ~equal_shape t1.index t2.index
      && equal_maps_to both_env t1.maps_to t2.maps_to
      && equal_env_extension ~equal_type both_env t1.env_extension
           t2.env_extension

  let equal_array eq a1 a2 =
    Array.length a1 = Array.length a2 && Array.for_all2 eq a1 a2

  let equal_row_like_block_case ~equal_type env (t1 : TG.row_like_block_case)
      (t2 : TG.row_like_block_case) =
    equal_row_like_case ~equal_type ~equal_lattice:TG.Block_size.equal
      ~equal_shape:Flambda_kind.Block_shape.equal
      ~equal_maps_to:(fun env -> equal_array (equal_type env))
      env t1 t2

  let equal_row_like_for_blocks ~equal_type env (t1 : TG.row_like_for_blocks)
      (t2 : TG.row_like_for_blocks) =
    Tag.Map.equal
      (Or_unknown.equal (equal_row_like_block_case ~equal_type env))
      t1.known_tags t2.known_tags
    && (match t1.other_tags, t2.other_tags with
       | Bottom, Bottom -> true
       | Bottom, Ok _ | Ok _, Bottom -> false
       | Ok t1, Ok t2 -> equal_row_like_block_case ~equal_type env t1 t2)
    && Alloc_mode.For_types.equal t1.alloc_mode t2.alloc_mode

  let equal_function_slot_indexed_product ~equal_type env
      (t1 : TG.function_slot_indexed_product)
      (t2 : TG.function_slot_indexed_product) =
    Function_slot.Map.equal (equal_type env)
      t1.function_slot_components_by_index t2.function_slot_components_by_index

  let equal_value_slot_indexed_product ~equal_type env
      (t1 : TG.value_slot_indexed_product) (t2 : TG.value_slot_indexed_product)
      =
    Value_slot.Map.equal (equal_type env) t1.value_slot_components_by_index
      t2.value_slot_components_by_index

  let equal_function_type ~equal_type env (t1 : TG.function_type)
      (t2 : TG.function_type) =
    Code_id.equal t1.code_id t2.code_id
    && equal_type env t1.rec_info t2.rec_info

  let equal_closures_entry ~equal_type env (t1 : TG.closures_entry)
      (t2 : TG.closures_entry) =
    Function_slot.Map.equal
      (Or_unknown_or_bottom.equal (equal_function_type ~equal_type env))
      t1.function_types t2.function_types
    && equal_function_slot_indexed_product ~equal_type env t1.closure_types
         t2.closure_types
    && equal_value_slot_indexed_product ~equal_type env t1.value_slot_types
         t2.value_slot_types

  let equal_row_like_for_closures ~equal_type env
      (t1 : TG.row_like_for_closures) (t2 : TG.row_like_for_closures) =
    let equal_row_like_case =
      equal_row_like_case ~equal_type env
        ~equal_lattice:Set_of_closures_contents.equal
        ~equal_shape:(fun () () -> true)
        ~equal_maps_to:(equal_closures_entry ~equal_type)
    in
    Function_slot.Map.equal equal_row_like_case t1.known_closures
      t2.known_closures
    &&
    match t1.other_closures, t2.other_closures with
    | Bottom, Bottom -> true
    | Bottom, Ok _ | Ok _, Bottom -> false
    | Ok case1, Ok case2 -> equal_row_like_case case1 case2

  let equal_array_contents ~equal_type env (t1 : TG.array_contents)
      (t2 : TG.array_contents) =
    match t1, t2 with
    | Mutable, Mutable -> true
    | Mutable, Immutable _ | Immutable _, Mutable -> false
    | Immutable { fields = f1 }, Immutable { fields = f2 } ->
      equal_array (equal_type env) f1 f2

  let add_extension env left_extension right_extension =
    let left_env =
      TE.add_env_extension_strict env.left_env left_extension
        ~meet_type:env.meet_type
    in
    let right_env =
      TE.add_env_extension_strict env.right_env right_extension
        ~meet_type:env.meet_type
    in
    match left_env, right_env with
    | Bottom, Bottom -> Some Or_bottom.Bottom
    | Bottom, Ok _ | Ok _, Bottom -> None
    | Ok left_env, Ok right_env ->
      Some (Or_bottom.Ok { env with left_env; right_env })

  let equal_head_of_kind_value_non_null ~equal_type env
      (t1 : TG.head_of_kind_value_non_null)
      (t2 : TG.head_of_kind_value_non_null) =
    match[@warning "-fragile-match"] t1, t2 with
    | Variant t1, Variant t2 -> (
      Bool.equal t1.is_unique t2.is_unique
      &&
      let envs_immediate, envs_block =
        match t1.extensions, t2.extensions with
        | No_extensions, No_extensions ->
          Some (Or_bottom.Ok env), Some (Or_bottom.Ok env)
        | Ext { when_immediate; when_block }, No_extensions ->
          ( add_extension env when_immediate TEE.empty,
            add_extension env when_block TEE.empty )
        | No_extensions, Ext { when_immediate; when_block } ->
          ( add_extension env TEE.empty when_immediate,
            add_extension env TEE.empty when_block )
        | ( Ext { when_immediate = when_immediate1; when_block = when_block1 },
            Ext { when_immediate = when_immediate2; when_block = when_block2 } )
          ->
          ( add_extension env when_immediate1 when_immediate2,
            add_extension env when_block1 when_block2 )
      in
      match envs_immediate, envs_block with
      | None, _ | _, None -> false
      | Some env_immediate, Some env_blocks -> (
        (match env_immediate with
        | Bottom -> true
        | Ok env_immediate ->
          Or_unknown.equal (equal_type env_immediate) t1.immediates
            t2.immediates)
        &&
        match env_blocks with
        | Bottom -> true
        | Ok env_blocks ->
          Or_unknown.equal
            (equal_row_like_for_blocks ~equal_type env_blocks)
            t1.blocks t2.blocks))
    | Mutable_block t1, Mutable_block t2 ->
      Alloc_mode.For_types.equal t1.alloc_mode t2.alloc_mode
    | Boxed_float32 (t1, a1), Boxed_float32 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_float (t1, a1), Boxed_float (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_int32 (t1, a1), Boxed_int32 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_int64 (t1, a1), Boxed_int64 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_nativeint (t1, a1), Boxed_nativeint (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Boxed_vec128 (t1, a1), Boxed_vec128 (t2, a2) ->
      equal_type env t1 t2 && Alloc_mode.For_types.equal a1 a2
    | Closures c1, Closures c2 ->
      equal_row_like_for_closures ~equal_type env c1.by_function_slot
        c2.by_function_slot
      && Alloc_mode.For_types.equal c1.alloc_mode c2.alloc_mode
    | String t1, String t2 -> String_info.Set.equal t1 t2
    | Array t1, Array t2 ->
      Or_unknown_or_bottom.equal Flambda_kind.With_subkind.equal t1.element_kind
        t2.element_kind
      && equal_type env t1.length t2.length
      && Or_unknown.equal
           (equal_array_contents ~equal_type env)
           t1.contents t2.contents
      && Alloc_mode.For_types.equal t1.alloc_mode t2.alloc_mode
    | _, _ -> false

  let equal_head_of_kind_value ~equal_type env (t1 : TG.head_of_kind_value)
      (t2 : TG.head_of_kind_value) =
    match t1.is_null, t2.is_null with
    | Not_null, Maybe_null | Maybe_null, Not_null -> false
    | Not_null, Not_null | Maybe_null, Maybe_null ->
      Or_unknown_or_bottom.equal
        (equal_head_of_kind_value_non_null ~equal_type env)
        t1.non_null t2.non_null

  let equal_head_of_kind_naked_immediate ~equal_type env
      (t1 : TG.head_of_kind_naked_immediate)
      (t2 : TG.head_of_kind_naked_immediate) =
    match t1, t2 with
    | Naked_immediates is1, Naked_immediates is2 ->
      Targetint_31_63.Set.equal is1 is2
    | Is_int t1, Is_int t2 -> equal_type env t1 t2
    | Get_tag t1, Get_tag t2 -> equal_type env t1 t2
    | Is_null t1, Is_null t2 -> equal_type env t1 t2
    | ( (Naked_immediates _ | Is_int _ | Get_tag _ | Is_null _),
        (Naked_immediates _ | Is_int _ | Get_tag _ | Is_null _) ) ->
      false

  let equal_head_of_kind_naked_float32 (t1 : TG.head_of_kind_naked_float32)
      (t2 : TG.head_of_kind_naked_float32) =
    Numeric_types.Float32_by_bit_pattern.Set.equal
      (t1 :> Numeric_types.Float32_by_bit_pattern.Set.t)
      (t2 :> Numeric_types.Float32_by_bit_pattern.Set.t)

  let equal_head_of_kind_naked_float (t1 : TG.head_of_kind_naked_float)
      (t2 : TG.head_of_kind_naked_float) =
    Numeric_types.Float_by_bit_pattern.Set.equal
      (t1 :> Numeric_types.Float_by_bit_pattern.Set.t)
      (t2 :> Numeric_types.Float_by_bit_pattern.Set.t)

  let equal_head_of_kind_naked_int32 (t1 : TG.head_of_kind_naked_int32)
      (t2 : TG.head_of_kind_naked_int32) =
    Numeric_types.Int32.Set.equal
      (t1 :> Numeric_types.Int32.Set.t)
      (t2 :> Numeric_types.Int32.Set.t)

  let equal_head_of_kind_naked_int64 (t1 : TG.head_of_kind_naked_int64)
      (t2 : TG.head_of_kind_naked_int64) =
    Numeric_types.Int64.Set.equal
      (t1 :> Numeric_types.Int64.Set.t)
      (t2 :> Numeric_types.Int64.Set.t)

  let equal_head_of_kind_naked_nativeint (t1 : TG.head_of_kind_naked_nativeint)
      (t2 : TG.head_of_kind_naked_nativeint) =
    Targetint_32_64.Set.equal
      (t1 :> Targetint_32_64.Set.t)
      (t2 :> Targetint_32_64.Set.t)

  let equal_head_of_kind_naked_vec128 (t1 : TG.head_of_kind_naked_vec128)
      (t2 : TG.head_of_kind_naked_vec128) =
    Vector_types.Vec128.Bit_pattern.Set.equal
      (t1 :> Vector_types.Vec128.Bit_pattern.Set.t)
      (t2 :> Vector_types.Vec128.Bit_pattern.Set.t)

  let equal_head_of_kind_rec_info (t1 : TG.head_of_kind_rec_info)
      (t2 : TG.head_of_kind_rec_info) =
    Rec_info_expr.equal t1 t2

  let equal_head_of_kind_region (t1 : TG.head_of_kind_region)
      (t2 : TG.head_of_kind_region) =
    let () = (t1 :> unit) and () = (t2 :> unit) in
    true

  let equal_expanded_head ~equal_type env (t1 : ET.t) (t2 : ET.t) =
    match ET.descr t1, ET.descr t2 with
    | Unknown, Unknown -> true
    | Unknown, (Ok _ | Bottom) | (Ok _ | Bottom), Unknown -> false
    | Bottom, Bottom -> true
    | Ok _, Bottom | Bottom, Ok _ -> false
    | Ok t1, Ok t2 -> (
      match[@warning "-fragile-match"] t1, t2 with
      | Value t1, Value t2 -> equal_head_of_kind_value ~equal_type env t1 t2
      | Naked_immediate t1, Naked_immediate t2 ->
        equal_head_of_kind_naked_immediate ~equal_type env t1 t2
      | Naked_float32 t1, Naked_float32 t2 ->
        equal_head_of_kind_naked_float32 t1 t2
      | Naked_float t1, Naked_float t2 -> equal_head_of_kind_naked_float t1 t2
      | Naked_int32 t1, Naked_int32 t2 -> equal_head_of_kind_naked_int32 t1 t2
      | Naked_int64 t1, Naked_int64 t2 -> equal_head_of_kind_naked_int64 t1 t2
      | Naked_nativeint t1, Naked_nativeint t2 ->
        equal_head_of_kind_naked_nativeint t1 t2
      | Naked_vec128 t1, Naked_vec128 t2 ->
        equal_head_of_kind_naked_vec128 t1 t2
      | Rec_info t1, Rec_info t2 -> equal_head_of_kind_rec_info t1 t2
      | Region t1, Region t2 -> equal_head_of_kind_region t1 t2
      | _, _ -> false)
end

let equal_type env t1 t2 =
  let renaming = ref Variable.Map.empty in
  let rec equal_type env t1 t2 =
    let is_equal =
      t1 == t2
      ||
      match
        ( TE.get_alias_then_canonical_simple_exn
            ~min_name_mode:Name_mode.in_types env.Equal_types.left_env t1,
          TE.get_alias_then_canonical_simple_exn
            ~min_name_mode:Name_mode.in_types env.Equal_types.right_env t2 )
      with
      | simple1, simple2 ->
        let is_equal =
          match Simple.must_be_var simple1, Simple.must_be_var simple2 with
          | None, None -> Simple.equal simple1 simple2
          | None, Some _ | Some _, None -> false
          | Some (var1, coercion1), Some (var2, coercion2) ->
            let coercion =
              Coercion.compose_exn coercion1 ~then_:(Coercion.inverse coercion2)
            in
            if Coercion.is_id coercion
            then (
              Variable.equal var1 var2
              ||
              match Variable.Map.find_opt var1 !renaming with
              | Some var1' -> Variable.equal var1' var2
              | None ->
                renaming := Variable.Map.add var1 var2 !renaming;
                true)
            else
              Equal_types.equal_expanded_head ~equal_type env
                (Expand_head.expand_head0 env.Equal_types.left_env t1
                   ~known_canonical_simple_at_in_types_mode:(Some simple1))
                (Expand_head.expand_head0 env.Equal_types.right_env t2
                   ~known_canonical_simple_at_in_types_mode:(Some simple2))
        in
        if not is_equal
        then
          Format.eprintf "%a <> %a@." Simple.print simple1 Simple.print simple2;
        is_equal
      | exception Not_found ->
        Equal_types.equal_expanded_head ~equal_type env
          (Expand_head.expand_head env.Equal_types.left_env t1)
          (Expand_head.expand_head env.Equal_types.right_env t2)
    in
    if (not is_equal) && Flambda_features.debug_flambda2 ()
    then Format.eprintf "NOT equal: %a <> %a@." TG.print t1 TG.print t2;
    is_equal
  in
  equal_type env t1 t2

let equal_type ~meet_type left_env right_env t1 t2 =
  equal_type { Equal_types.left_env; right_env; meet_type } t1 t2
