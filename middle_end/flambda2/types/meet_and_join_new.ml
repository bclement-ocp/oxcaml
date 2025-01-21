(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module ET = Expand_head.Expanded_type
module K = Flambda_kind
module MTC = More_type_creators
module TG = Type_grammar
module TE = Typing_env
module TEE = Typing_env_extension
module TEL = Typing_env_level
module Vec128 = Vector_types.Vec128.Bit_pattern

let depth = ref 0

type 'a meet_return_value = 'a TE.meet_return_value =
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

type 'a meet_result =
  | Bottom of unit meet_return_value
  | Ok of 'a meet_return_value * TE.t

type 'a join_result = 'a Or_unknown.t * Join_env.Binary.t

let map_join_result ~f (v, env) = Or_unknown.map ~f v, env

let ( let>+ ) x f = map_join_result ~f x

let add_equation (simple : Simple.t) ty_of_simple env ~meet_type :
    unit meet_result =
  let name name ~coercion:coercion_from_name_to_simple =
    let coercion_from_simple_to_name =
      Coercion.inverse coercion_from_name_to_simple
    in
    let ty_of_name =
      TG.apply_coercion ty_of_simple coercion_from_simple_to_name
    in
    match
      TE.add_equation_strict env name ty_of_name ~meet_type:(TE.New meet_type)
    with
    | Ok env -> Ok (New_result (), env)
    | Bottom -> Bottom (New_result ())
  in
  Simple.pattern_match simple ~name ~const:(fun const ->
      (* A constant is its own most precise type, but we still need to check
         that is matches the assigned type. *)
      if Flambda_features.check_light_invariants ()
      then assert (TG.get_alias_opt ty_of_simple == None);
      let expanded =
        Expand_head.expand_head0 env (MTC.type_for_const const)
          ~known_canonical_simple_at_in_types_mode:(Some simple)
      in
      match meet_type env (ET.to_type expanded) ty_of_simple with
      | Or_bottom.Ok (_, env) -> Ok (New_result (), env)
      | Or_bottom.Bottom -> Bottom (New_result ()))

let map_result ~f = function
  | Bottom r -> Bottom r
  | Ok (Left_input, env) -> Ok (Left_input, env)
  | Ok (Right_input, env) -> Ok (Right_input, env)
  | Ok (Both_inputs, env) -> Ok (Both_inputs, env)
  | Ok (New_result x, env) -> Ok (New_result (f x), env)

let map_env ~f = function
  | Bottom r -> Bottom r
  | Ok (r, env) -> (
    match (f env : _ Or_bottom.t) with
    | Bottom -> Bottom (map_return_value (fun _ -> ()) r)
    | Ok env -> Ok (r, env))

let extract_value res left right =
  match res with
  | Left_input -> left
  | Right_input -> right
  | Both_inputs -> left
  | New_result value -> value

let combine_meet_return_values a b compute_value =
  match a, b with
  | Both_inputs, Both_inputs -> Both_inputs
  | (Left_input | Both_inputs), (Left_input | Both_inputs) -> Left_input
  | (Right_input | Both_inputs), (Right_input | Both_inputs) -> Right_input
  | New_result _, _
  | _, New_result _
  | Left_input, Right_input
  | Right_input, Left_input ->
    New_result (compute_value ())

let set_meet (type a b) (module S : Container_types_intf.Set with type t = a)
    ~(of_set : a -> b) env (s1 : a) (s2 : a) : b meet_result =
  match S.subset s1 s2, S.subset s2 s1 with
  | true, true -> Ok (Both_inputs, env)
  | true, false -> Ok (Left_input, env)
  | false, true -> Ok (Right_input, env)
  | false, false ->
    let s = S.inter s1 s2 in
    if S.is_empty s
    then Bottom (New_result ())
    else Ok (New_result (of_set s), env)

type ('key, 'data, 'mapping) fold2 =
  { fold2 :
      'acc.
      ('key -> 'data option -> 'data option -> 'acc -> 'acc) ->
      'mapping ->
      'mapping ->
      'acc ->
      'acc
  }

let meet_mapping (type key data mapping)
    ~(meet_data : TE.t -> data -> data -> data meet_result)
    ~(fold2 : (key, data, mapping) fold2) ~env ~(left : mapping)
    ~(right : mapping) ~(rebuild : (key * data) list -> mapping) :
    mapping meet_result =
  let { fold2 } = fold2 in
  let open struct
    type t =
      { all_left : bool;
        all_right : bool;
        mapping : (key * data) list;
        env : TE.t
      }

    exception Bottom_result
  end in
  try
    let res =
      fold2
        (fun key data_left_opt data_right_opt
             { all_left; all_right; mapping; env } ->
          match data_left_opt, data_right_opt with
          | None, None -> assert false
          | Some data_left, None ->
            { all_left;
              all_right = false;
              mapping = (key, data_left) :: mapping;
              env
            }
          | None, Some data_right ->
            { all_left = false;
              all_right;
              mapping = (key, data_right) :: mapping;
              env
            }
          | Some data_left, Some data_right -> (
            match meet_data env data_left data_right with
            | Bottom _ -> raise Bottom_result
            | Ok (res, env) -> (
              let[@local] result ~all_left ~all_right data =
                { all_left; all_right; mapping = (key, data) :: mapping; env }
              in
              match res with
              | Both_inputs -> result ~all_left ~all_right data_left
              | Left_input -> result ~all_left ~all_right:false data_left
              | Right_input -> result ~all_left:false ~all_right data_right
              | New_result data -> result ~all_left:false ~all_right:false data)
            ))
        left right
        { all_left = true; all_right = true; mapping = []; env }
    in
    let result =
      match res.all_left, res.all_right with
      | true, true -> Both_inputs
      | true, false -> Left_input
      | false, true -> Right_input
      | false, false -> New_result (rebuild res.mapping)
    in
    Ok (result, res.env)
  with Bottom_result -> Bottom (New_result ())

module Map_meet (M : Container_types_intf.Map) = struct
  let meet ~(meet_data : TE.t -> 'a -> 'a -> 'a meet_result) env (left : 'a M.t)
      (right : 'a M.t) : 'a M.t meet_result =
    let fold2 f m1 m2 init =
      let r = ref init in
      let _m =
        M.merge
          (fun key left right ->
            r := f key left right !r;
            None)
          m1 m2
      in
      !r
    in
    let rebuild l =
      List.fold_left (fun m (key, data) -> M.add key data m) M.empty l
    in
    let fold2 = { fold2 } in
    meet_mapping ~meet_data ~fold2 ~env ~left ~right ~rebuild
end

module Function_slot_map_meet = Map_meet (Function_slot.Map)
module Value_slot_map_meet = Map_meet (Value_slot.Map)

module Combine_results_meet_ops = struct
  type _ t =
    | [] : unit t
    | ( :: ) : ((TE.t -> 'a -> 'a -> 'a meet_result) * 'b t) -> ('a * 'b) t
end

module Combine_results_inputs = struct
  type _ t =
    | [] : unit t
    | ( :: ) : ('a * 'b t) -> ('a * 'b) t
end

let rec build_values : type a. a Combine_results_inputs.t -> a = function
  | input :: next -> input, build_values next
  | [] -> ()

let extract_values res left right =
  match res with
  | Left_input -> build_values left
  | Right_input -> build_values right
  | Both_inputs -> build_values left
  | New_result value -> value

let combine_results env ~(meet_ops : 'a Combine_results_meet_ops.t)
    ~(left_inputs : 'a Combine_results_inputs.t)
    ~(right_inputs : 'a Combine_results_inputs.t) ~(rebuild : 'a -> 'b) :
    'b meet_result =
  let rec do_meets :
      type a.
      TE.t ->
      a Combine_results_meet_ops.t ->
      a Combine_results_inputs.t ->
      a Combine_results_inputs.t ->
      a meet_result =
   fun env meet_ops left right : a meet_result ->
    match meet_ops, left, right with
    | [], [], [] -> Ok (Both_inputs, env)
    | meet :: next_meet, left_input :: next_left, right_input :: next_right -> (
      match meet env left_input right_input with
      | Bottom r -> Bottom r
      | Ok (result_hd, env) -> (
        match do_meets env next_meet next_left next_right with
        | Bottom r -> Bottom r
        | Ok (result_tl, env) ->
          let return_value =
            combine_meet_return_values result_hd result_tl (fun () ->
                let result_hd =
                  extract_value result_hd left_input right_input
                in
                let result_tl = extract_values result_tl next_left next_right in
                result_hd, result_tl)
          in
          Ok (return_value, env)))
  in
  map_result ~f:rebuild (do_meets env meet_ops left_inputs right_inputs)

let combine_results2 env ~meet_a ~meet_b ~left_a ~right_a ~left_b ~right_b
    ~rebuild =
  combine_results env ~meet_ops:[meet_a; meet_b] ~left_inputs:[left_a; left_b]
    ~right_inputs:[right_a; right_b] ~rebuild:(fun (a, (b, ())) -> rebuild a b)

type ext =
  | No_extensions
  | Ext of
      { when_a : TEE.t;
        when_b : TEE.t
      }

let meet_disjunction ~meet_a ~meet_b ~bottom_a ~bottom_b ~meet_type ~join_ty
    initial_env val_a1 val_b1 extensions1 val_a2 val_b2 extensions2 =
  let join_scope = TE.current_scope initial_env in
  let env = TE.increment_scope initial_env in
  let direct_return r =
    map_env r ~f:(fun scoped_env ->
        let level = TE.cut scoped_env ~cut_after:join_scope in
        let initial_env =
          TEL.fold_on_defined_vars
            (fun var kind env ->
              TE.add_definition env
                (Bound_name.create_var
                   (Bound_var.create var Name_mode.in_types))
                kind)
            level initial_env
        in
        let ext = (TEL.as_extension_without_bindings level).TG.equations in
        let ext = TG.Env_extension.create ~equations:ext in
        TE.add_env_extension_strict initial_env ext ~meet_type:(New meet_type))
  in
  let env_a, env_b = Or_bottom.Ok env, Or_bottom.Ok env in
  let env_a, env_b =
    match extensions1 with
    | No_extensions -> env_a, env_b
    | Ext { when_a; when_b } ->
      ( Or_bottom.bind env_a ~f:(fun env ->
            TE.add_env_extension_strict env when_a ~meet_type:(New meet_type)),
        Or_bottom.bind env_b ~f:(fun env ->
            TE.add_env_extension_strict env when_b ~meet_type:(New meet_type)) )
  in
  let env_a, env_b =
    match extensions2 with
    | No_extensions -> env_a, env_b
    | Ext { when_a; when_b } ->
      ( Or_bottom.bind env_a ~f:(fun env ->
            TE.add_env_extension_strict env when_a ~meet_type:(New meet_type)),
        Or_bottom.bind env_b ~f:(fun env ->
            if false then Format.eprintf "add: %a@." TEE.print when_b;
            TE.add_env_extension_strict env when_b ~meet_type:(New meet_type)) )
  in
  let a_result : _ meet_result =
    match env_a with
    | Bottom -> Bottom (New_result ())
    | Ok env -> meet_a env val_a1 val_a2
  in
  let b_result : _ meet_result =
    match env_b with
    | Bottom -> Bottom (New_result ())
    | Ok env -> meet_b env val_b1 val_b2
  in
  match a_result, b_result with
  | Bottom r1, Bottom r2 ->
    Bottom (combine_meet_return_values r1 r2 (fun () -> ()))
  | Ok (a_result, env), Bottom b ->
    let result =
      combine_meet_return_values a_result b (fun () ->
          let val_a = extract_value a_result val_a1 val_a2 in
          let val_b = bottom_b () in
          val_a, val_b, No_extensions)
    in
    direct_return (Ok (result, env))
  | Bottom a, Ok (b_result, env) ->
    let result =
      combine_meet_return_values a b_result (fun () ->
          let val_b = extract_value b_result val_b1 val_b2 in
          let val_a = bottom_a () in
          val_a, val_b, No_extensions)
    in
    direct_return (Ok (result, env))
  | Ok (a_result, env_a), Ok (b_result, env_b) ->
    let when_a_level = TE.cut env_a ~cut_after:join_scope in
    let when_b_level = TE.cut env_b ~cut_after:join_scope in
    let env =
      TEL.fold_on_defined_vars
        (fun var kind env ->
          TE.add_definition env
            (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
            kind)
        when_a_level env
    in
    let env =
      TEL.fold_on_defined_vars
        (fun var kind env ->
          TE.add_definition env
            (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
            kind)
        when_b_level env
    in
    let when_a = (TEL.as_extension when_a_level).TG.equations in
    let when_a = TG.Env_extension.create ~equations:when_a in
    let when_b = (TEL.as_extension when_b_level).TG.equations in
    let when_b = TG.Env_extension.create ~equations:when_b in
    let extensions =
      if TEE.is_empty when_a && TEE.is_empty when_b
      then
        No_extensions
        (* CR vlaviron: If both extensions have equations in common, the join
           below will add them to the result environment. Keeping those common
           equations in the variant extensions then becomes redundant, but we
           don't have an easy way to detect redundancy. *)
      else Ext { when_a; when_b }
    in
    let env_extension_result =
      (* We only catch the cases where empty extensions are preserved *)
      match extensions, extensions1, extensions2 with
      | No_extensions, No_extensions, No_extensions -> Both_inputs
      | No_extensions, No_extensions, Ext _ -> Left_input
      | No_extensions, Ext _, No_extensions -> Right_input
      | (No_extensions | Ext _), _, _ ->
        (* This goes through combine_meet_return_values, so the value is not
           needed *)
        New_result ()
    in
    let result =
      combine_meet_return_values
        (combine_meet_return_values a_result b_result (fun () -> ()))
        env_extension_result
        (fun () ->
          let val_a = extract_value a_result val_a1 val_a2 in
          let val_b = extract_value b_result val_b1 val_b2 in
          val_a, val_b, extensions)
    in
    (* NB: we might get new variables! *)
    let result_env, _result_extension =
      Join_env.Superjoin.join_env_extensions ~meet_type:(TE.New meet_type)
        ~join_ty env
        [env_a, when_a; env_b, when_b]
    in
    if false
    then (
      Format.eprintf "when a: %a@." TEE.print when_a;
      Format.eprintf "when b: %a@." TEE.print when_b;
      Format.eprintf "result: %a@." TEE.print _result_extension);
    let result_level = TE.cut result_env ~cut_after:join_scope in
    let initial_env =
      TEL.fold_on_defined_vars
        (fun var kind env ->
          TE.add_definition env
            (Bound_name.create_var (Bound_var.create var Name_mode.in_types))
            kind)
        result_level initial_env
    in
    let result_extension = (TEL.as_extension result_level).TG.equations in
    let result_extension =
      TG.Env_extension.create ~equations:result_extension
    in
    if false then Format.eprintf "TRUE result: %a@." TEE.print result_extension;
    let result_env =
      (* Not strict, as we don't expect to be able to get bottom equations from
         joining non-bottom ones *)
      TE.add_env_extension initial_env result_extension
        ~meet_type:(New meet_type)
    in
    Ok (result, result_env)

let meet_code_id (env : TE.t) (code_id1 : Code_id.t) (code_id2 : Code_id.t) :
    Code_id.t meet_result =
  if Code_id.equal code_id1 code_id2
  then Ok (Both_inputs, env)
  else
    match
      Code_age_relation.meet (TE.code_age_relation env)
        ~resolver:(TE.code_age_relation_resolver env)
        code_id1 code_id2
    with
    | Bottom -> Bottom (New_result ())
    | Ok code_id ->
      if Code_id.equal code_id code_id1
      then Ok (Left_input, env)
      else if Code_id.equal code_id code_id2
      then Ok (Right_input, env)
      else Ok (New_result code_id, env)

type meet_keep_side =
  | Left
  | Right

(* type meet_expanded_head_result =
 *   | Left_head_unchanged
 *   | Right_head_unchanged
 *   | New_head of ET.t * TEE.t *)

let meet_alloc_mode env (alloc_mode1 : Alloc_mode.For_types.t)
    (alloc_mode2 : Alloc_mode.For_types.t) : Alloc_mode.For_types.t meet_result
    =
  match alloc_mode1, alloc_mode2 with
  | (Heap_or_local | Local), (Heap_or_local | Local) | Heap, Heap ->
    Ok (Both_inputs, env)
  | (Heap_or_local | Local), _ -> Ok (Right_input, env)
  | _, (Heap_or_local | Local) -> Ok (Left_input, env)

let join_alloc_mode (alloc_mode1 : Alloc_mode.For_types.t)
    (alloc_mode2 : Alloc_mode.For_types.t) : Alloc_mode.For_types.t =
  match alloc_mode1, alloc_mode2 with
  | (Heap_or_local | Local), _ | _, (Heap_or_local | Local) ->
    Alloc_mode.For_types.unknown ()
  | Heap, Heap -> Alloc_mode.For_types.heap

let[@inline always] meet_unknown meet_contents ~contents_is_bottom env
    (or_unknown1 : _ Or_unknown.t) (or_unknown2 : _ Or_unknown.t) :
    _ Or_unknown.t meet_result =
  match or_unknown1, or_unknown2 with
  | Unknown, Unknown -> Ok (Both_inputs, env)
  | Known contents1, Known contents2
    when contents_is_bottom contents1 && contents_is_bottom contents2 ->
    Bottom Both_inputs
  | Known contents, _ when contents_is_bottom contents -> Bottom Left_input
  | _, Known contents when contents_is_bottom contents -> Bottom Right_input
  | _, Unknown -> Ok (Left_input, env)
  | Unknown, _ -> Ok (Right_input, env)
  | Known contents1, Known contents2 ->
    map_result ~f:Or_unknown.known (meet_contents env contents1 contents2)

let[@inline always] join_unknown join_contents (env : Join_env.Binary.t)
    (or_unknown1 : _ Or_unknown.t) (or_unknown2 : _ Or_unknown.t) :
    _ join_result =
  match or_unknown1, or_unknown2 with
  | _, Unknown | Unknown, _ -> Unknown, env
  | Known contents1, Known contents2 -> join_contents env contents1 contents2

(* Note: Bottom is a valid element kind for empty arrays, so this function never
   leads to a general Bottom result *)
let meet_array_element_kinds (element_kind1 : _ Or_unknown_or_bottom.t)
    (element_kind2 : _ Or_unknown_or_bottom.t) : _ Or_unknown_or_bottom.t =
  match element_kind1, element_kind2 with
  | Unknown, Unknown -> Unknown
  | Bottom, _ | _, Bottom -> Bottom
  | Unknown, Ok kind | Ok kind, Unknown -> Ok kind
  | Ok element_kind1, Ok element_kind2 ->
    if Flambda_kind.With_subkind.compatible element_kind1
         ~when_used_at:element_kind2
    then Ok element_kind1
    else if Flambda_kind.With_subkind.compatible element_kind2
              ~when_used_at:element_kind1
    then Ok element_kind2
    else Bottom

let join_array_element_kinds (element_kind1 : _ Or_unknown_or_bottom.t)
    (element_kind2 : _ Or_unknown_or_bottom.t) : _ Or_unknown_or_bottom.t =
  match element_kind1, element_kind2 with
  | Unknown, _ | _, Unknown -> Unknown
  | Bottom, element_kind | element_kind, Bottom -> element_kind
  | Ok element_kind1, Ok element_kind2 ->
    if Flambda_kind.With_subkind.compatible element_kind1
         ~when_used_at:element_kind2
    then Ok element_kind2
    else if Flambda_kind.With_subkind.compatible element_kind2
              ~when_used_at:element_kind1
    then Ok element_kind1
    else Unknown

let rec meet env (t1 : TG.t) (t2 : TG.t) : TG.t meet_result =
  if not (K.equal (TG.kind t1) (TG.kind t2))
  then
    Misc.fatal_errorf "Kind mismatch upon meet:@ %a@ versus@ %a" TG.print t1
      TG.print t2;
  let kind = TG.kind t1 in
  let simple1 =
    match
      TE.get_alias_then_canonical_simple_exn env t1
        ~min_name_mode:Name_mode.in_types
    with
    | exception Not_found -> None
    | exception _ -> assert false
    | canonical_simple -> Some canonical_simple
  in
  let simple2 =
    match
      TE.get_alias_then_canonical_simple_exn env t2
        ~min_name_mode:Name_mode.in_types
    with
    | exception Not_found -> None
    | canonical_simple -> Some canonical_simple
  in
  match simple1 with
  | None -> (
    let expanded1 =
      Expand_head.expand_head0 env t1
        ~known_canonical_simple_at_in_types_mode:simple1
    in
    match simple2 with
    | None ->
      let expanded2 =
        Expand_head.expand_head0 env t2
          ~known_canonical_simple_at_in_types_mode:simple2
      in
      map_result ~f:ET.to_type (meet_expanded_head env expanded1 expanded2)
    | Some simple2 -> (
      (* Here we are meeting a non-alias type on the left with an alias on the
         right. In all cases, the return type is the alias, so we will always
         return [Right_input]; the interesting part will be the environment.

         [add_equation] will meet [expanded1] with the existing type of
         [simple2]. *)
      let env : unit meet_result =
        add_equation simple2 (ET.to_type expanded1) env ~meet_type
      in
      match env with
      | Ok (_, env) -> Ok (Right_input, env)
      | Bottom r -> Bottom r))
  | Some simple1 -> (
    match simple2 with
    | None -> (
      let expanded2 =
        Expand_head.expand_head0 env t2
          ~known_canonical_simple_at_in_types_mode:simple2
      in
      (* We always return [Left_input] (see comment above) *)
      let env : unit meet_result =
        add_equation simple1 (ET.to_type expanded2) env ~meet_type
      in
      match env with
      | Ok (_, env) -> Ok (Left_input, env)
      | Bottom r -> Bottom r)
    | Some simple2 -> (
      if (* We are doing a meet between two alias types. Whatever happens, the
            resulting environment will contain an alias equation between the two
            inputs, so both the left-hand alias and the right-hand alias are
            correct results for the meet, allowing us to return [Both_inputs] in
            all cases. *)
         Simple.equal simple1 simple2
      then
        (* The alias is already present; no need to add any equation here *)
        Ok (Both_inputs, env)
      else
        let env =
          Simple.pattern_match simple2
            ~name:(fun _ ~coercion:_ ->
              add_equation simple2
                (TG.alias_type_of kind simple1)
                env ~meet_type)
            ~const:(fun const2 ->
              Simple.pattern_match simple1
                ~name:(fun _ ~coercion:_ ->
                  add_equation simple1
                    (TG.alias_type_of kind simple2)
                    env ~meet_type)
                ~const:(fun const1 : unit meet_result ->
                  if Reg_width_const.equal const1 const2
                  then Ok (New_result (), env)
                  else Bottom (New_result ())))
        in
        (* [add_equation] will have called [meet] on the underlying types, so
           [env] now contains all extra equations arising from meeting the
           expanded heads. *)
        match env with
        | Ok (_, env) -> Ok (Both_inputs, env)
        | Bottom r -> Bottom r))

and meet_or_unknown_or_bottom :
    type a b.
    (TE.t -> a -> a -> b meet_result) ->
    TE.t ->
    a Or_unknown_or_bottom.t ->
    a Or_unknown_or_bottom.t ->
    b meet_result =
 fun meet_elt env (input1 : a Or_unknown_or_bottom.t)
     (input2 : a Or_unknown_or_bottom.t) ->
  match input1, input2 with
  | Unknown, Unknown -> Ok (Both_inputs, env)
  | _, Unknown -> Ok (Left_input, env)
  | Unknown, _ -> Ok (Right_input, env)
  | Bottom, Bottom -> Bottom Both_inputs
  | Bottom, _ -> Bottom Left_input
  | _, Bottom -> Bottom Right_input
  | Ok elt1, Ok elt2 -> meet_elt env elt1 elt2

and meet_expanded_head env (expanded1 : ET.t) (expanded2 : ET.t) :
    ET.t meet_result =
  meet_or_unknown_or_bottom meet_expanded_head0 env (ET.descr expanded1)
    (ET.descr expanded2)

and meet_expanded_head0 env (descr1 : ET.descr) (descr2 : ET.descr) :
    ET.t meet_result =
  match descr1, descr2 with
  | Value head1, Value head2 ->
    map_result ~f:ET.create_value (meet_head_of_kind_value env head1 head2)
  | Naked_immediate head1, Naked_immediate head2 ->
    map_result ~f:ET.create_naked_immediate
      (meet_head_of_kind_naked_immediate env head1 head2)
  | Naked_float32 head1, Naked_float32 head2 ->
    map_result ~f:ET.create_naked_float32
      (meet_head_of_kind_naked_float32 env head1 head2)
  | Naked_float head1, Naked_float head2 ->
    map_result ~f:ET.create_naked_float
      (meet_head_of_kind_naked_float env head1 head2)
  | Naked_int32 head1, Naked_int32 head2 ->
    map_result ~f:ET.create_naked_int32
      (meet_head_of_kind_naked_int32 env head1 head2)
  | Naked_int64 head1, Naked_int64 head2 ->
    map_result ~f:ET.create_naked_int64
      (meet_head_of_kind_naked_int64 env head1 head2)
  | Naked_nativeint head1, Naked_nativeint head2 ->
    map_result ~f:ET.create_naked_nativeint
      (meet_head_of_kind_naked_nativeint env head1 head2)
  | Naked_vec128 head1, Naked_vec128 head2 ->
    map_result ~f:ET.create_naked_vec128
      (meet_head_of_kind_naked_vec128 env head1 head2)
  | Rec_info head1, Rec_info head2 ->
    map_result ~f:ET.create_rec_info
      (meet_head_of_kind_rec_info env head1 head2)
  | Region head1, Region head2 ->
    map_result ~f:ET.create_region (meet_head_of_kind_region env head1 head2)
  | ( ( Value _ | Naked_immediate _ | Naked_float _ | Naked_float32 _
      | Naked_int32 _ | Naked_vec128 _ | Naked_int64 _ | Naked_nativeint _
      | Rec_info _ | Region _ ),
      _ ) ->
    assert false

and meet_head_of_kind_value env
    ({ non_null = non_null1; is_null = is_null1 } : TG.head_of_kind_value)
    ({ non_null = non_null2; is_null = is_null2 } : TG.head_of_kind_value) :
    TG.head_of_kind_value meet_result =
  let meet_a =
    let meet_elt env elt1 elt2 =
      map_result
        ~f:(fun x -> Or_unknown_or_bottom.Ok x)
        (meet_head_of_kind_value_non_null env elt1 elt2)
    in
    meet_or_unknown_or_bottom meet_elt
  in
  let meet_b env (is_null1 : TG.is_null) (is_null2 : TG.is_null) =
    match is_null1, is_null2 with
    | Not_null, Not_null -> Bottom Both_inputs
    | Maybe_null, Maybe_null -> Ok (Both_inputs, env)
    | Not_null, Maybe_null -> Bottom Left_input
    | Maybe_null, Not_null -> Bottom Right_input
  in
  let bottom_a () = Or_unknown_or_bottom.Bottom in
  let bottom_b () : TG.is_null = Not_null in
  map_result
    ~f:(fun (non_null, is_null, _extensions) : TG.head_of_kind_value ->
      { non_null; is_null })
    (meet_disjunction ~meet_a ~meet_b ~bottom_a ~bottom_b ~meet_type
       ~join_ty:(join ?bound_name:None) env non_null1 is_null1 No_extensions
       non_null2 is_null2 No_extensions)

and meet_head_of_kind_value_non_null env
    (head1 : TG.head_of_kind_value_non_null)
    (head2 : TG.head_of_kind_value_non_null) :
    TG.head_of_kind_value_non_null meet_result =
  match head1, head2 with
  | ( Variant
        { blocks = blocks1;
          immediates = imms1;
          extensions = extensions1;
          is_unique = is_unique1
        },
      Variant
        { blocks = blocks2;
          immediates = imms2;
          extensions = extensions2;
          is_unique = is_unique2
        } ) ->
    (* Uniqueness tracks whether duplication/lifting is allowed. It must always
       be propagated, both for meet and join. *)
    let is_unique = is_unique1 || is_unique2 in
    map_result
      ~f:(fun (blocks, immediates, extensions) ->
        TG.Head_of_kind_value_non_null.create_variant ~is_unique ~blocks
          ~immediates ~extensions)
      (meet_variant env ~blocks1 ~imms1 ~blocks2 ~imms2 ~extensions1
         ~extensions2)
  | ( Mutable_block { alloc_mode = alloc_mode1 },
      Mutable_block { alloc_mode = alloc_mode2 } ) ->
    map_result
      ~f:(fun alloc_mode ->
        TG.Head_of_kind_value_non_null.create_mutable_block alloc_mode)
      (meet_alloc_mode env alloc_mode1 alloc_mode2)
  | Variant { blocks; _ }, Mutable_block { alloc_mode = alloc_mode_right } -> (
    match blocks with
    | Unknown -> Ok (Right_input, env)
    | Known { alloc_mode = alloc_mode_left; _ } -> (
      (* CR vlaviron: This is not nice. We're more or less treating
         [Mutable_block] as more precise than [Variant], while losing precision
         on the way (the row_like equations on known immutable fields). Here is
         an example where it matters: *)
      (* type r = { a : int; mutable b : int }
       * let f r =
       *   let a1 = r.a in
       *   let a2 = r.a in
       *   (a1, a2)
       *
       * let g a =
       *   let r = { a; b = 0 } in
       *   let a1 = r.a in
       *   let a2 = r.a in
       *   (a1, a2) *)
      (* In [f], the two accesses will be shared because the type for those
         loads is [Variant]. But in [g], we get a more precise type
         ([Mutable_block]), and this prevents us from sharing the immutable
         loads.

         I have several ideas to fix this, but none of them are simple so we
         will need to have a proper discussion before I commit to implementing
         one. *)
      match meet_alloc_mode env alloc_mode_left alloc_mode_right with
      | Bottom r -> Bottom r
      | Ok ((Both_inputs | Right_input), env) -> Ok (Right_input, env)
      | Ok (Left_input, env) ->
        Ok
          ( New_result
              (TG.Head_of_kind_value_non_null.create_mutable_block
                 alloc_mode_left),
            env )
      | Ok (New_result alloc_mode, env) ->
        Ok
          ( New_result
              (TG.Head_of_kind_value_non_null.create_mutable_block alloc_mode),
            env )))
  | Mutable_block { alloc_mode = alloc_mode_left }, Variant { blocks; _ } -> (
    match blocks with
    | Unknown -> Ok (Left_input, env)
    | Known { alloc_mode = alloc_mode_right; _ } -> (
      (* CR vlaviron: see symmetric case above *)
      match meet_alloc_mode env alloc_mode_left alloc_mode_right with
      | Bottom r -> Bottom r
      | Ok ((Both_inputs | Left_input), env) -> Ok (Left_input, env)
      | Ok (Right_input, env) ->
        Ok
          ( New_result
              (TG.Head_of_kind_value_non_null.create_mutable_block
                 alloc_mode_right),
            env )
      | Ok (New_result alloc_mode, env) ->
        Ok
          ( New_result
              (TG.Head_of_kind_value_non_null.create_mutable_block alloc_mode),
            env )))
  | Boxed_float32 (n1, alloc_mode1), Boxed_float32 (n2, alloc_mode2) ->
    combine_results2 env
      ~rebuild:TG.Head_of_kind_value_non_null.create_boxed_float32 ~meet_a:meet
      ~meet_b:meet_alloc_mode ~left_a:n1 ~right_a:n2 ~left_b:alloc_mode1
      ~right_b:alloc_mode2
  | Boxed_float (n1, alloc_mode1), Boxed_float (n2, alloc_mode2) ->
    combine_results2 env
      ~rebuild:TG.Head_of_kind_value_non_null.create_boxed_float ~meet_a:meet
      ~meet_b:meet_alloc_mode ~left_a:n1 ~right_a:n2 ~left_b:alloc_mode1
      ~right_b:alloc_mode2
  | Boxed_int32 (n1, alloc_mode1), Boxed_int32 (n2, alloc_mode2) ->
    combine_results2 env
      ~rebuild:TG.Head_of_kind_value_non_null.create_boxed_int32 ~meet_a:meet
      ~meet_b:meet_alloc_mode ~left_a:n1 ~right_a:n2 ~left_b:alloc_mode1
      ~right_b:alloc_mode2
  | Boxed_int64 (n1, alloc_mode1), Boxed_int64 (n2, alloc_mode2) ->
    combine_results2 env
      ~rebuild:TG.Head_of_kind_value_non_null.create_boxed_int64 ~meet_a:meet
      ~meet_b:meet_alloc_mode ~left_a:n1 ~right_a:n2 ~left_b:alloc_mode1
      ~right_b:alloc_mode2
  | Boxed_nativeint (n1, alloc_mode1), Boxed_nativeint (n2, alloc_mode2) ->
    combine_results2 env
      ~rebuild:TG.Head_of_kind_value_non_null.create_boxed_nativeint
      ~meet_a:meet ~meet_b:meet_alloc_mode ~left_a:n1 ~right_a:n2
      ~left_b:alloc_mode1 ~right_b:alloc_mode2
  | Boxed_vec128 (n1, alloc_mode1), Boxed_vec128 (n2, alloc_mode2) ->
    combine_results2 env
      ~rebuild:TG.Head_of_kind_value_non_null.create_boxed_vec128 ~meet_a:meet
      ~meet_b:meet_alloc_mode ~left_a:n1 ~right_a:n2 ~left_b:alloc_mode1
      ~right_b:alloc_mode2
  | ( Closures { by_function_slot = by_function_slot1; alloc_mode = alloc_mode1 },
      Closures
        { by_function_slot = by_function_slot2; alloc_mode = alloc_mode2 } ) ->
    combine_results2 env ~rebuild:TG.Head_of_kind_value_non_null.create_closures
      ~meet_a:meet_row_like_for_closures ~meet_b:meet_alloc_mode
      ~left_a:by_function_slot1 ~right_a:by_function_slot2 ~left_b:alloc_mode1
      ~right_b:alloc_mode2
  | String strs1, String strs2 ->
    map_result ~f:TG.Head_of_kind_value_non_null.create_string
      (set_meet (module String_info.Set) env strs1 strs2 ~of_set:Fun.id)
  | ( Array
        { element_kind = element_kind1;
          length = length1;
          contents = contents1;
          alloc_mode = alloc_mode1
        },
      Array
        { element_kind = element_kind2;
          length = length2;
          contents = contents2;
          alloc_mode = alloc_mode2
        } ) ->
    meet_array_type env
      (element_kind1, length1, contents1, alloc_mode1)
      (element_kind2, length2, contents2, alloc_mode2)
  | ( ( Variant _ | Mutable_block _ | Boxed_float _ | Boxed_float32 _
      | Boxed_int32 _ | Boxed_vec128 _ | Boxed_int64 _ | Boxed_nativeint _
      | Closures _ | String _ | Array _ ),
      _ ) ->
    (* This assumes that all the different constructors are incompatible. This
       could break very hard for dubious uses of Obj. *)
    Bottom (New_result ())

and meet_array_type env (element_kind1, length1, contents1, alloc_mode1)
    (element_kind2, length2, contents2, alloc_mode2) =
  let element_kind = meet_array_element_kinds element_kind1 element_kind2 in
  combine_results env
    ~rebuild:(fun (length, (contents, (alloc_mode, ()))) ->
      TG.Head_of_kind_value_non_null.create_array_with_contents ~element_kind
        ~length contents alloc_mode)
    ~meet_ops:
      [ meet;
        meet_array_contents ~meet_element_kind:element_kind;
        meet_alloc_mode ]
    ~left_inputs:[length1; contents1; alloc_mode1]
    ~right_inputs:[length2; contents2; alloc_mode2]

and meet_array_contents env (array_contents1 : TG.array_contents Or_unknown.t)
    (array_contents2 : TG.array_contents Or_unknown.t)
    ~(meet_element_kind : _ Or_unknown_or_bottom.t) =
  meet_unknown
    (fun env (array_contents1 : TG.array_contents)
         (array_contents2 : TG.array_contents) : TG.array_contents meet_result ->
      match array_contents1, array_contents2 with
      | Mutable, Mutable -> Ok (Both_inputs, env)
      | Mutable, Immutable _ | Immutable _, Mutable -> Bottom (New_result ())
      | Immutable { fields = fields1 }, Immutable { fields = fields2 } -> (
        if Array.length fields1 <> Array.length fields2
        then Bottom (New_result ())
        else
          match meet_element_kind with
          | Bottom ->
            if Array.length fields1 = 0
            then
              (* Both empty arrays. Returning [Both_inputs] would be correct but
                 may not propagate the Bottom element kind as far as we can.
                 Using a New_result might lead us to extra work is one or both
                 of the inputs already have Bottom kind. We choose the
                 New_result solution because it's a case that is unlikely to
                 happen, so the extra cost is likely very small (while losing
                 precision might be noticeable). *)
              Ok (New_result (Immutable { fields = [||] }), env)
            else Bottom (New_result ())
          | Unknown ->
            (* vlaviron: If the meet of the kinds is Unknown, then both inputs
               had Unknown kinds. I don't see how we could end up with an array
               type where the contents are known but we don't know the kind, but
               in that case we wouldn't be able to call meet because the two
               sides may have different kinds. So we'll just return the first
               input, which is guaranteed to be a correct approximation of the
               meet. *)
            Ok (Left_input, env)
          | Ok _ ->
            map_result
              ~f:(fun fields : TG.array_contents -> Immutable { fields })
              (meet_array_of_types env fields1 fields2
                 ~length:(Array.length fields1))))
    ~contents_is_bottom:(fun (array_contents : TG.array_contents) ->
      match array_contents with
      | Mutable -> false
      | Immutable { fields } -> Array.exists TG.is_obviously_bottom fields)
    env array_contents1 array_contents2

and meet_variant env ~(blocks1 : TG.Row_like_for_blocks.t Or_unknown.t)
    ~(imms1 : TG.t Or_unknown.t)
    ~(blocks2 : TG.Row_like_for_blocks.t Or_unknown.t)
    ~(imms2 : TG.t Or_unknown.t) ~(extensions1 : TG.variant_extensions)
    ~(extensions2 : TG.variant_extensions) :
    (TG.Row_like_for_blocks.t Or_unknown.t
    * TG.t Or_unknown.t
    * TG.variant_extensions)
    meet_result =
  let meet_a = meet_unknown meet ~contents_is_bottom:TG.is_obviously_bottom in
  let meet_b =
    meet_unknown meet_row_like_for_blocks
      ~contents_is_bottom:TG.Row_like_for_blocks.is_bottom
  in
  let bottom_a () = Or_unknown.Known TG.bottom_naked_immediate in
  let bottom_b () = Or_unknown.Known TG.Row_like_for_blocks.bottom in
  let extensions1 =
    match extensions1 with
    | No_extensions -> No_extensions
    | Ext { when_immediate; when_block } ->
      Ext { when_a = when_immediate; when_b = when_block }
  in
  let extensions2 =
    match extensions2 with
    | No_extensions -> No_extensions
    | Ext { when_immediate; when_block } ->
      Ext { when_a = when_immediate; when_b = when_block }
  in
  map_result
    ~f:(fun (imms, blocks, extensions) ->
      let extensions : TG.variant_extensions =
        match extensions with
        | No_extensions -> No_extensions
        | Ext { when_a = when_immediate; when_b = when_block } ->
          Ext { when_immediate; when_block }
      in
      blocks, imms, extensions)
    (meet_disjunction ~meet_a ~meet_b ~bottom_a ~bottom_b ~meet_type
       ~join_ty:(join ?bound_name:None) env imms1 blocks1 extensions1 imms2
       blocks2 extensions2)

and meet_head_of_kind_naked_immediate env (t1 : TG.head_of_kind_naked_immediate)
    (t2 : TG.head_of_kind_naked_immediate) :
    TG.head_of_kind_naked_immediate meet_result =
  let module I = Targetint_31_63 in
  let keep_side side : _ meet_result =
    match side with
    | Left -> Ok (Left_input, env)
    | Right -> Ok (Right_input, env)
  in
  let bottom_other_side side : _ meet_result =
    match side with Left -> Bottom Right_input | Right -> Bottom Left_input
  in
  let meet_with_shape ~rebuild ty shape side =
    map_result ~f:rebuild
      (match side with Left -> meet env ty shape | Right -> meet env shape ty)
  in
  let is_int_immediate ~is_int_ty ~immediates ~is_int_side =
    if I.Set.is_empty immediates
    then bottom_other_side is_int_side
    else
      let rebuild = TG.Head_of_kind_naked_immediate.create_is_int in
      match I.Set.mem I.zero immediates, I.Set.mem I.one immediates with
      | false, false -> Bottom (New_result ())
      | true, true -> keep_side is_int_side
      | true, false ->
        meet_with_shape ~rebuild is_int_ty MTC.any_block is_int_side
      | false, true ->
        meet_with_shape ~rebuild is_int_ty MTC.any_tagged_immediate is_int_side
  in
  let is_null_immediate ~is_null_ty ~immediates ~is_null_side =
    if I.Set.is_empty immediates
    then bottom_other_side is_null_side
    else
      let rebuild = TG.Head_of_kind_naked_immediate.create_is_null in
      match I.Set.mem I.zero immediates, I.Set.mem I.one immediates with
      | false, false -> Bottom (New_result ())
      | true, true -> keep_side is_null_side
      | true, false ->
        meet_with_shape ~rebuild is_null_ty TG.any_non_null_value is_null_side
      | false, true -> meet_with_shape ~rebuild is_null_ty TG.null is_null_side
  in
  let get_tag_immediate ~get_tag_ty ~immediates ~get_tag_side =
    if I.Set.is_empty immediates
    then bottom_other_side get_tag_side
    else
      let tags =
        I.Set.fold
          (fun tag tags ->
            match Tag.create_from_targetint tag with
            | Some tag -> Tag.Set.add tag tags
            | None -> tags (* No blocks exist with this tag *))
          immediates Tag.Set.empty
      in
      if Tag.Set.is_empty tags
      then Bottom (New_result ())
      else
        match
          MTC.blocks_with_these_tags tags (Alloc_mode.For_types.unknown ())
        with
        | Known shape ->
          meet_with_shape
            ~rebuild:TG.Head_of_kind_naked_immediate.create_get_tag get_tag_ty
            shape get_tag_side
        | Unknown -> keep_side get_tag_side
  in
  match t1, t2 with
  | Naked_immediates is1, Naked_immediates is2 ->
    map_result
      ~f:TG.Head_of_kind_naked_immediate.create_naked_immediates_non_empty
      (set_meet (module I.Set) env is1 is2 ~of_set:Fun.id)
  | Is_int is_int_ty, Naked_immediates immediates ->
    is_int_immediate ~is_int_ty ~immediates ~is_int_side:Left
  | Naked_immediates immediates, Is_int is_int_ty ->
    is_int_immediate ~is_int_ty ~immediates ~is_int_side:Right
  | Get_tag get_tag_ty, Naked_immediates immediates ->
    get_tag_immediate ~get_tag_ty ~immediates ~get_tag_side:Left
  | Naked_immediates immediates, Get_tag get_tag_ty ->
    get_tag_immediate ~get_tag_ty ~immediates ~get_tag_side:Right
  | Is_null is_null_ty, Naked_immediates immediates ->
    is_null_immediate ~is_null_ty ~immediates ~is_null_side:Left
  | Naked_immediates immediates, Is_null is_null_ty ->
    is_null_immediate ~is_null_ty ~immediates ~is_null_side:Right
  | (Is_int _ | Get_tag _ | Is_null _), (Is_int _ | Get_tag _ | Is_null _) ->
    (* CR mshinwell: introduce improved handling for
     *   Is_int meet Is_int
     *   Get_tag meet Get_tag
     * i.e. a better fix for PR1515, at which point we might also be able
     * to consider improving:
     *   Is_int meet Get_tag
     * and vice-versa. *)
    (* We can't return Bottom, as it would be unsound, so we need to either do
       the actual meet with Naked_immediates, or just give up and return one of
       the arguments. *)
    Ok (Left_input, env)

and meet_head_of_kind_naked_float32 env t1 t2 =
  set_meet
    (module Numeric_types.Float32_by_bit_pattern.Set)
    env
    (t1
      : TG.head_of_kind_naked_float32
      :> Numeric_types.Float32_by_bit_pattern.Set.t)
    (t2
      : TG.head_of_kind_naked_float32
      :> Numeric_types.Float32_by_bit_pattern.Set.t)
    ~of_set:TG.Head_of_kind_naked_float32.create_non_empty_set

and meet_head_of_kind_naked_float env t1 t2 =
  set_meet
    (module Numeric_types.Float_by_bit_pattern.Set)
    env
    (t1
      : TG.head_of_kind_naked_float
      :> Numeric_types.Float_by_bit_pattern.Set.t)
    (t2
      : TG.head_of_kind_naked_float
      :> Numeric_types.Float_by_bit_pattern.Set.t)
    ~of_set:TG.Head_of_kind_naked_float.create_non_empty_set

and meet_head_of_kind_naked_int32 env t1 t2 =
  set_meet
    (module Numeric_types.Int32.Set)
    env
    (t1 : TG.head_of_kind_naked_int32 :> Numeric_types.Int32.Set.t)
    (t2 : TG.head_of_kind_naked_int32 :> Numeric_types.Int32.Set.t)
    ~of_set:TG.Head_of_kind_naked_int32.create_non_empty_set

and meet_head_of_kind_naked_int64 env t1 t2 =
  set_meet
    (module Numeric_types.Int64.Set)
    env
    (t1 : TG.head_of_kind_naked_int64 :> Numeric_types.Int64.Set.t)
    (t2 : TG.head_of_kind_naked_int64 :> Numeric_types.Int64.Set.t)
    ~of_set:TG.Head_of_kind_naked_int64.create_non_empty_set

and meet_head_of_kind_naked_nativeint env t1 t2 =
  set_meet
    (module Targetint_32_64.Set)
    env
    (t1 : TG.head_of_kind_naked_nativeint :> Targetint_32_64.Set.t)
    (t2 : TG.head_of_kind_naked_nativeint :> Targetint_32_64.Set.t)
    ~of_set:TG.Head_of_kind_naked_nativeint.create_non_empty_set

and meet_head_of_kind_naked_vec128 env t1 t2 =
  set_meet
    (module Vec128.Set)
    env
    (t1 : TG.head_of_kind_naked_vec128 :> Vec128.Set.t)
    (t2 : TG.head_of_kind_naked_vec128 :> Vec128.Set.t)
    ~of_set:TG.Head_of_kind_naked_vec128.create_non_empty_set

and meet_head_of_kind_rec_info env _t1 _t2 =
  (* CR-someday lmaurer: This could be doing things like discovering two depth
     variables are equal *)
  (* CR vlaviron: This looks awfully wrong. I think we'll need to remove it at
     some point; it is only reachable from function types, and we should already
     have any relevant coercion from closure types. *)
  Ok (Both_inputs, env)

and meet_head_of_kind_region env () () : _ meet_result = Ok (Both_inputs, env)

and meet_row_like :
      'lattice 'shape 'maps_to 'row_tag 'known.
      meet_maps_to:(TE.t -> 'maps_to -> 'maps_to -> 'maps_to meet_result) ->
      equal_index:('lattice -> 'lattice -> bool) ->
      subset_index:('lattice -> 'lattice -> bool) ->
      union_index:('lattice -> 'lattice -> 'lattice) ->
      meet_shape:('shape -> 'shape -> 'shape Or_bottom.t) ->
      is_empty_map_known:('known -> bool) ->
      get_singleton_map_known:
        ('known ->
        ('row_tag * ('lattice, 'shape, 'maps_to) TG.Row_like_case.t) option) ->
      merge_map_known:
        (('row_tag ->
         ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option ->
         ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option ->
         ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option) ->
        'known ->
        'known ->
        'known) ->
      TE.t ->
      known1:'known ->
      known2:'known ->
      other1:('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t ->
      other2:('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t ->
      ('known * ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t)
      meet_result =
 fun ~meet_maps_to ~equal_index ~subset_index ~union_index ~meet_shape
     ~is_empty_map_known ~get_singleton_map_known ~merge_map_known initial_env
     ~known1 ~known2 ~other1 ~other2 ->
  let common_scope = TE.current_scope initial_env in
  let base_env = TE.increment_scope initial_env in
  let extract_extension scoped_env =
    TE.cut scoped_env ~cut_after:common_scope
  in
  let open struct
    type result_env =
      | No_result
      | Extension of TE.t * TEL.t
  end in
  let result_env = ref No_result in
  let need_join =
    (* The returned env_extension is the join of the env_extension produced by
       each non bottom cases. Therefore there is some loss of precision in that
       case and we need to store the one produced for each tag. But when only
       one tag is kept it would be wasteful (but correct) to store it.

       We consider that the result of the meet between t1 and t2 will have only
       one tag when t1 (or t2) has exactly one tag (one that and no 'other'
       cases).

       This is an overapproximation because the result could have only one tag
       for instance if

       t1 = [Tag 1 | Tag 2] and t2 = [Tag 2 | Tag 3], or if

       t1 = [Tag 1 | Tag 2] and t2 = [Tag 1 | Tag 2]

       but the meet between some combinations result in a bottom. *)
    match
      ( other1,
        get_singleton_map_known known1,
        other2,
        get_singleton_map_known known2 )
    with
    | Bottom, Some _, _, _ | _, _, Bottom, Some _ -> false
    | (Ok _ | Bottom), _, (Ok _ | Bottom), _ ->
      if is_empty_map_known known1 && is_empty_map_known known2
      then false
      else true
  in
  let result_is_t1 = ref true in
  let result_is_t2 = ref true in
  let update_refs = function
    | Both_inputs -> ()
    | Left_input -> result_is_t2 := false
    | Right_input -> result_is_t1 := false
    | New_result _ ->
      result_is_t1 := false;
      result_is_t2 := false
  in
  let join_result_env scoped_env =
    let new_result_env =
      match !result_env with
      | No_result -> Extension (scoped_env, extract_extension scoped_env)
      | Extension (env1, ext1) ->
        assert need_join;
        let ext2 = extract_extension scoped_env in
        let join_env =
          Join_env.Superjoin.dodoblahdo ~meet_type:(TE.New meet_type)
            ~join_ty:(join ?bound_name:None) base_env
            [env1, ext1; scoped_env, ext2]
        in
        let extension = extract_extension join_env in
        Extension (join_env, extension)
    in
    result_env := new_result_env
  in
  let meet_index env (i1 : ('lattice, 'shape) TG.row_like_index)
      (i2 : ('lattice, 'shape) TG.row_like_index) :
      ('lattice, 'shape) TG.row_like_index meet_result =
    match meet_shape i1.shape i2.shape with
    | Bottom -> Bottom (New_result ())
    | Ok shape -> (
      match i1.domain, i2.domain with
      | Known i1', Known i2' ->
        if equal_index i1' i2'
        then Ok (Both_inputs, env)
        else Bottom (New_result ())
      | Known known, At_least at_least ->
        if subset_index at_least known
        then
          (* [at_least] is included in [known] hence [Known known] is included
             in [At_least at_least], hence [Known known] \inter [At_least
             at_least] = [Known known] *)
          Ok (Left_input, env)
        else Bottom (New_result ())
      | At_least at_least, Known known ->
        if subset_index at_least known
        then Ok (Right_input, env)
        else Bottom (New_result ())
      | At_least i1', At_least i2' ->
        if subset_index i1' i2'
        then
          if subset_index i2' i1'
          then Ok (Both_inputs, env)
          else Ok (Right_input, env)
        else if subset_index i2' i1'
        then Ok (Left_input, env)
        else
          let domain =
            TG.Row_like_index_domain.at_least (union_index i1' i2')
          in
          Ok (New_result (TG.Row_like_index.create ~domain ~shape), env))
  in
  let bottom_case r =
    update_refs r;
    None
  in
  let meet_case env (case1 : ('lattice, 'shape, 'maps_to) TG.Row_like_case.t)
      (case2 : ('lattice, 'shape, 'maps_to) TG.Row_like_case.t) =
    match meet_index env case1.index case2.index with
    | Bottom r -> bottom_case r
    | Ok (index_result, env) -> (
      match meet_maps_to env case1.maps_to case2.maps_to with
      | Bottom r -> bottom_case r
      | Ok (maps_to_result, env) -> (
        let env : _ Or_bottom.t =
          match
            TE.add_env_extension_strict env case1.env_extension
              ~meet_type:(New meet_type)
          with
          | Bottom -> Bottom
          | Ok env ->
            TE.add_env_extension_strict env case2.env_extension
              ~meet_type:(New meet_type)
        in
        match env with
        | Bottom -> bottom_case (New_result ())
        | Ok env ->
          join_result_env env;
          update_refs index_result;
          update_refs maps_to_result;
          let index = extract_value index_result case1.index case2.index in
          let maps_to =
            extract_value maps_to_result case1.maps_to case2.maps_to
          in
          let env_extension =
            if need_join then extract_extension env else TEL.empty
          in
          if TEL.is_empty env_extension
          then ()
          else (
            result_is_t1 := false;
            result_is_t2 := false);
          let env_extension = TEL.as_extension_without_bindings env_extension in
          Some
            (Or_unknown.Known
               (TG.Row_like_case.create ~maps_to ~index ~env_extension))))
  in
  let meet_knowns
      (case1 :
        ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option)
      (case2 :
        ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option) :
      ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option =
    match case1, case2 with
    | None, None -> None
    | Some case1, None -> (
      match other2 with
      | Bottom ->
        result_is_t1 := false;
        None
      | Ok other_case -> (
        match case1 with
        | Unknown -> (
          match
            TE.add_env_extension_strict base_env other_case.env_extension
              ~meet_type:(New meet_type)
          with
          | Bottom -> None
          | Ok env ->
            join_result_env env;
            result_is_t1 := false;
            result_is_t2 := false;
            Some (Known other_case))
        | Known case1 -> meet_case base_env case1 other_case))
    | None, Some case2 -> (
      match other1 with
      | Bottom ->
        result_is_t2 := false;
        None
      | Ok other_case -> (
        match case2 with
        | Unknown -> (
          match
            TE.add_env_extension_strict base_env other_case.env_extension
              ~meet_type:(New meet_type)
          with
          | Bottom -> None
          | Ok env ->
            join_result_env env;
            result_is_t1 := false;
            result_is_t2 := false;
            Some (Known other_case))
        | Known case2 -> meet_case base_env other_case case2))
    | Some case1, Some case2 -> (
      match case1, case2 with
      | Unknown, Unknown ->
        join_result_env base_env;
        Some Unknown
      | Known case, Unknown -> (
        match
          TE.add_env_extension_strict base_env case.env_extension
            ~meet_type:(New meet_type)
        with
        | Bottom -> None
        | Ok env ->
          join_result_env env;
          result_is_t2 := false;
          Some (Known case))
      | Unknown, Known case -> (
        match
          TE.add_env_extension_strict base_env case.env_extension
            ~meet_type:(New meet_type)
        with
        | Bottom -> None
        | Ok env ->
          join_result_env env;
          result_is_t1 := false;
          Some (Known case))
      | Known case1, Known case2 -> meet_case base_env case1 case2)
  in
  let known =
    merge_map_known
      (fun _tag case1 case2 -> meet_knowns case1 case2)
      known1 known2
  in
  let other : ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t =
    match other1, other2 with
    | Bottom, Bottom -> Bottom
    | Bottom, _ ->
      result_is_t2 := false;
      Bottom
    | _, Bottom ->
      result_is_t1 := false;
      Bottom
    | Ok other1, Ok other2 -> (
      match meet_case base_env other1 other2 with
      | None -> Bottom
      | Some Unknown -> Misc.fatal_error "meet_case should not produce Unknown"
      | Some (Known r) -> Ok r)
  in
  if is_empty_map_known known
     && match other with Bottom -> true | Ok _ -> false
  then Bottom (New_result ())
  else
    let env : _ Or_bottom.t =
      match !result_env with
      | No_result -> Bottom
      | Extension (shared, ext) -> (
        try
          (* XXX: strict *)
          Or_bottom.Ok
            (TE.add_env_extension_from_level initial_env ext
               ~meet_type:(New meet_type))
        with Misc.Fatal_error ->
          let bt = Printexc.get_raw_backtrace () in
          let level = TE.cut shared ~cut_after:common_scope in
          let new_variables = Typing_env_level.defined_names level in
          Format.eprintf
            "@[<v>@ %tContext is:%t adding env extension:@ %a@ with new \
             variables:@ %a@]@ "
            Flambda_colours.error Flambda_colours.pop TEL.print ext
            Name.Set.print new_variables;
          Printexc.raise_with_backtrace Misc.Fatal_error bt)
    in
    let match_with_input v =
      match !result_is_t1, !result_is_t2 with
      | true, true -> Both_inputs
      | true, false -> Left_input
      | false, true -> Right_input
      | false, false -> New_result v
    in
    match env with
    | Bottom -> Bottom (match_with_input ())
    | Ok env -> Ok (match_with_input (known, other), env)

and meet_row_like_for_blocks env
    ({ known_tags = known1; other_tags = other1; alloc_mode = alloc_mode1 } :
      TG.Row_like_for_blocks.t)
    ({ known_tags = known2; other_tags = other2; alloc_mode = alloc_mode2 } :
      TG.Row_like_for_blocks.t) : TG.Row_like_for_blocks.t meet_result =
  let meet_shape shape1 shape2 : _ Or_bottom.t =
    if K.Block_shape.equal shape1 shape2 then Ok shape1 else Bottom
  in
  let get_singleton_map_known known =
    match (Tag.Map.get_singleton known : (_ * _ Or_unknown.t) option) with
    | Some (tag, Known case) -> Some (tag, case)
    | Some (_, Unknown) | None -> None
  in
  combine_results2 env
    ~rebuild:(fun (known_tags, other_tags) alloc_mode ->
      TG.Row_like_for_blocks.create_raw ~known_tags ~other_tags ~alloc_mode)
    ~meet_a:(fun env (known1, other1) (known2, other2) ->
      meet_row_like ~meet_maps_to:meet_int_indexed_product
        ~equal_index:TG.Block_size.equal ~subset_index:TG.Block_size.subset
        ~union_index:TG.Block_size.union ~meet_shape
        ~is_empty_map_known:Tag.Map.is_empty ~get_singleton_map_known
        ~merge_map_known:Tag.Map.merge env ~known1 ~known2 ~other1 ~other2)
    ~meet_b:meet_alloc_mode ~left_a:(known1, other1) ~right_a:(known2, other2)
    ~left_b:alloc_mode1 ~right_b:alloc_mode2

and meet_row_like_for_closures env
    ({ known_closures = known1; other_closures = other1 } :
      TG.Row_like_for_closures.t)
    ({ known_closures = known2; other_closures = other2 } :
      TG.Row_like_for_closures.t) : TG.Row_like_for_closures.t meet_result =
  let meet_shape () () : _ Or_bottom.t = Ok () in
  let merge_map_known merge_case known1 known2 =
    Function_slot.Map.merge
      (fun fslot case1 case2 ->
        let case1 = Option.map Or_unknown.known case1 in
        let case2 = Option.map Or_unknown.known case2 in
        match merge_case fslot case1 case2 with
        | None -> None
        | Some (Or_unknown.Known case) -> Some case
        | Some Or_unknown.Unknown ->
          Misc.fatal_error "Unknown case in closure meet")
      known1 known2
  in
  map_result
    ~f:(fun (known_closures, other_closures) ->
      TG.Row_like_for_closures.create_raw ~known_closures ~other_closures)
    (meet_row_like ~meet_maps_to:meet_closures_entry
       ~equal_index:Set_of_closures_contents.equal
       ~subset_index:Set_of_closures_contents.subset
       ~union_index:Set_of_closures_contents.union ~meet_shape
       ~is_empty_map_known:Function_slot.Map.is_empty
       ~get_singleton_map_known:Function_slot.Map.get_singleton ~merge_map_known
       env ~known1 ~known2 ~other1 ~other2)

and meet_closures_entry (env : TE.t)
    ({ function_types = function_types1;
       closure_types = closure_types1;
       value_slot_types = value_slot_types1
     } :
      TG.Closures_entry.t)
    ({ function_types = function_types2;
       closure_types = closure_types2;
       value_slot_types = value_slot_types2
     } :
      TG.Closures_entry.t) : TG.Closures_entry.t meet_result =
  combine_results env
    ~meet_ops:
      [ Function_slot_map_meet.meet ~meet_data:meet_function_type;
        meet_product_function_slot_indexed;
        meet_product_value_slot_indexed ]
    ~left_inputs:[function_types1; closure_types1; value_slot_types1]
    ~right_inputs:[function_types2; closure_types2; value_slot_types2]
    ~rebuild:(fun (function_types, (closure_types, (value_slot_types, ()))) ->
      TG.Closures_entry.create ~function_types ~closure_types ~value_slot_types)

and meet_product_function_slot_indexed env
    ({ function_slot_components_by_index = components_by_index1 } :
      TG.Product.Function_slot_indexed.t)
    ({ function_slot_components_by_index = components_by_index2 } :
      TG.Product.Function_slot_indexed.t) :
    TG.Product.Function_slot_indexed.t meet_result =
  map_result ~f:TG.Product.Function_slot_indexed.create
    (Function_slot_map_meet.meet ~meet_data:meet env components_by_index1
       components_by_index2)

and meet_product_value_slot_indexed env
    ({ value_slot_components_by_index = components_by_index1 } :
      TG.Product.Value_slot_indexed.t)
    ({ value_slot_components_by_index = components_by_index2 } :
      TG.Product.Value_slot_indexed.t) :
    TG.Product.Value_slot_indexed.t meet_result =
  map_result ~f:TG.Product.Value_slot_indexed.create
    (Value_slot_map_meet.meet ~meet_data:meet env components_by_index1
       components_by_index2)

and meet_int_indexed_product env (fields1 : TG.Product.Int_indexed.t)
    (fields2 : TG.Product.Int_indexed.t) : _ meet_result =
  let length = max (Array.length fields1) (Array.length fields2) in
  map_result ~f:TG.Product.Int_indexed.create_from_array
    (meet_array_of_types env fields1 fields2 ~length)

and meet_array_of_types env fields1 fields2 ~length =
  let fold2 f left right init =
    let r = ref init in
    for i = 0 to length - 1 do
      let left_data = if i >= Array.length left then None else Some left.(i) in
      let right_data =
        if i >= Array.length right then None else Some right.(i)
      in
      r := f i left_data right_data !r
    done;
    !r
  in
  let rebuild l =
    match l with
    | [] -> [||]
    | (_key, data) :: _ ->
      let result = Array.make length data in
      List.iter (fun (key, data) -> result.(key) <- data) l;
      result
  in
  let fold2 = { fold2 } in
  meet_mapping ~meet_data:meet ~fold2 ~env ~left:fields1 ~right:fields2 ~rebuild

and meet_function_type (env : TE.t)
    (func_type1 : TG.Function_type.t Or_unknown_or_bottom.t)
    (func_type2 : TG.Function_type.t Or_unknown_or_bottom.t) :
    TG.Function_type.t Or_unknown_or_bottom.t meet_result =
  match func_type1, func_type2 with
  | Bottom, Bottom | Unknown, Unknown -> Ok (Both_inputs, env)
  | Bottom, _ | _, Unknown -> Ok (Left_input, env)
  | _, Bottom | Unknown, _ -> Ok (Right_input, env)
  | ( Ok { code_id = code_id1; rec_info = rec_info1 },
      Ok { code_id = code_id2; rec_info = rec_info2 } ) ->
    let rebuild code_id rec_info =
      (* It's possible that [code_id] corresponds to deleted code. In that case,
         any attempt to inline will fail, as the code will not be found in the
         simplifier's environment -- see
         [Simplify_apply_expr.simplify_direct_function_call]. *)
      Or_unknown_or_bottom.Ok (TG.Function_type.create code_id ~rec_info)
    in
    combine_results2 env ~rebuild ~meet_a:meet_code_id ~left_a:code_id1
      ~right_a:code_id2 ~meet_b:meet ~left_b:rec_info1 ~right_b:rec_info2

and meet_type env t1 t2 : _ Or_bottom.t =
  incr depth;
  if !depth >= 100
  then (
    let bt = Printexc.get_callstack 100_000 in
    Format.eprintf "@[<v>trace:@ %s@]@." (Printexc.raw_backtrace_to_string bt);
    assert false);
  let out : _ Or_bottom.t =
    if TE.is_bottom env
    then Bottom
    else
      match meet env t1 t2 with
      | Ok (res, env) -> Ok (res, env)
      | Bottom _ -> Bottom
  in
  decr depth;
  out

and mark_for_join env t1 t2 : TG.t join_result =
  if not (K.equal (TG.kind t1) (TG.kind t2))
  then
    Misc.fatal_errorf "Kind mismatch upon join:@ %a@ versus@ %a" TG.print t1
      TG.print t2;
  let kind = TG.kind t1 in
  let t1 = TG.recover_some_aliases t1 in
  let t2 = TG.recover_some_aliases t2 in
  if TG.is_obviously_bottom t2
  then
    ( Known t1,
      import_names
        ~from_env:(Join_env.Binary.left_join_env env)
        env (TG.free_names t1) )
  else if TG.is_obviously_bottom t1
  then
    ( Known t2,
      import_names
        ~from_env:(Join_env.Binary.right_join_env env)
        env (TG.free_names t2) )
  else
    let canonical_simple1 =
      match
        TE.get_alias_then_canonical_simple_exn
          (Join_env.Binary.left_join_env env)
          t1 ~min_name_mode:Name_mode.in_types
      with
      | exception Not_found -> None
      | canonical_simple -> Some canonical_simple
    in
    let canonical_simple2 =
      match
        TE.get_alias_then_canonical_simple_exn
          (Join_env.Binary.right_join_env env)
          t2 ~min_name_mode:Name_mode.in_types
      with
      | exception Not_found -> None
      | canonical_simple -> Some canonical_simple
    in
    match canonical_simple1, canonical_simple2 with
    | Some canonical_simple1, None when TG.is_obviously_bottom t2 ->
      ( Known (TG.alias_type_of kind canonical_simple1),
        Simple.pattern_match canonical_simple1
          ~const:(fun _ -> env)
          ~name:(fun name ~coercion:_ ->
            Join_env.Binary.import_name ~meet_type:(New meet_type) env kind name)
      )
    | None, Some canonical_simple2 when TG.is_obviously_bottom t1 ->
      ( Known (TG.alias_type_of kind canonical_simple2),
        Simple.pattern_match canonical_simple2
          ~const:(fun _ -> env)
          ~name:(fun name ~coercion:_ ->
            Join_env.Binary.import_name ~meet_type:(New meet_type) env kind name)
      )
    | None, None -> join env t1 t2
    | Some _, None | None, Some _ ->
      let ty, env =
        Join_env.Binary.now_joining_types env kind t1 t2
          ~meet_type:(New meet_type)
      in
      if Flambda_features.debug_flambda2 ()
      then (
        let expanded1 =
          Expand_head.expand_head (Join_env.Binary.left_join_env env) t1
        in
        let expanded2 =
          Expand_head.expand_head (Join_env.Binary.right_join_env env) t2
        in
        (* TODO: doing the join now is not OK because we do not necessarily have
           the proper join value for the other identifiers (in the right env) --
           they might be added at a later depth if they are themselves created
           from a join. *)
        Format.eprintf "@[<v>expanded join:@ %a@ and@ %a]@." TG.print
          (ET.to_type expanded1) TG.print (ET.to_type expanded2);
        Format.eprintf
          "@[<v>loss of precision; unnamed join:@ %a@ and@ %a@ is:@ %a@]@."
          TG.print t1 TG.print t2
          (Or_unknown.print TG.print)
          ty);
      ty, env
    | Some canonical_simple1, Some canonical_simple2 -> (
      let joined_simple, env =
        Join_env.Binary.now_joining_simple env kind canonical_simple1
          canonical_simple2 ~meet_type:(New meet_type)
      in
      match joined_simple with
      | Unknown -> Unknown, env
      | Known simple -> Known (TG.alias_type_of kind simple), env)

and join ?bound_name:_ env (t1 : TG.t) (t2 : TG.t) : TG.t join_result =
  if not (K.equal (TG.kind t1) (TG.kind t2))
  then
    Misc.fatal_errorf "Kind mismatch upon join:@ %a@ versus@ %a" TG.print t1
      TG.print t2;
  let kind = TG.kind t1 in
  let canonical_simple1 =
    match
      TE.get_alias_then_canonical_simple_exn
        (Join_env.Binary.left_join_env env)
        t1 ~min_name_mode:Name_mode.in_types
    with
    | exception Not_found -> None
    | canonical_simple -> Some canonical_simple
  in
  let canonical_simple2 =
    match
      TE.get_alias_then_canonical_simple_exn
        (Join_env.Binary.right_join_env env)
        t2 ~min_name_mode:Name_mode.in_types
    with
    | exception Not_found -> None
    | canonical_simple -> Some canonical_simple
  in
  let already_known, env =
    match canonical_simple1, canonical_simple2 with
    | Some canonical_simple1, Some canonical_simple2 ->
      Join_env.Binary.now_joining_simple env kind canonical_simple1
        canonical_simple2 ~meet_type:(New meet_type)
    | _, _ -> Or_unknown.Unknown, env
  in
  match already_known with
  | Known simple -> Known (TG.alias_type_of kind simple), env
  | Unknown ->
    let expanded1 =
      Expand_head.expand_head0
        (Join_env.Binary.left_join_env env)
        t1 ~known_canonical_simple_at_in_types_mode:canonical_simple1
    in
    let expanded2 =
      Expand_head.expand_head0
        (Join_env.Binary.right_join_env env)
        t2 ~known_canonical_simple_at_in_types_mode:canonical_simple2
    in
    (* CR vlaviron: Fix this to return Unknown when Product can handle it *)
    map_join_result ~f:ET.to_type
      (join_expanded_head env kind expanded1 expanded2)

and import_names ~from_env env names =
  Name_occurrences.fold_names names ~init:env ~f:(fun env name ->
      if not (TE.mem ~min_name_mode:Name_mode.in_types from_env name)
      then env
      else
        let kind = TG.kind (TE.find from_env name None) in
        (* XXX: importing is broken if the name is not canonical!!! use a
           specific mechanism? *)
        Join_env.Binary.import_name env kind name ~meet_type:(New meet_type))

and join_expanded_head env kind (expanded1 : ET.t) (expanded2 : ET.t) :
    ET.t join_result =
  match ET.descr expanded1, ET.descr expanded2 with
  | Bottom, Bottom -> Known (ET.create_bottom kind), env
  | Ok _, Bottom ->
    let free_names = TG.free_names (ET.to_type expanded1) in
    let left_env = Join_env.Binary.left_join_env env in
    Known expanded1, import_names ~from_env:left_env env free_names
  | Bottom, Ok _ ->
    let free_names = TG.free_names (ET.to_type expanded2) in
    let right_env = Join_env.Binary.right_join_env env in
    Known expanded2, import_names ~from_env:right_env env free_names
  | Unknown, _ | _, Unknown -> Known (ET.create_unknown kind), env
  | Ok descr1, Ok descr2 -> (
    let expanded_or_unknown, env =
      match descr1, descr2 with
      | Value head1, Value head2 ->
        let>+ head = join_head_of_kind_value env head1 head2 in
        ET.create_value head
      | Naked_immediate head1, Naked_immediate head2 ->
        let>+ head = join_head_of_kind_naked_immediate env head1 head2 in
        ET.create_naked_immediate head
      | Naked_float32 head1, Naked_float32 head2 ->
        let>+ head = join_head_of_kind_naked_float32 env head1 head2 in
        ET.create_naked_float32 head
      | Naked_float head1, Naked_float head2 ->
        let>+ head = join_head_of_kind_naked_float env head1 head2 in
        ET.create_naked_float head
      | Naked_int32 head1, Naked_int32 head2 ->
        let>+ head = join_head_of_kind_naked_int32 env head1 head2 in
        ET.create_naked_int32 head
      | Naked_int64 head1, Naked_int64 head2 ->
        let>+ head = join_head_of_kind_naked_int64 env head1 head2 in
        ET.create_naked_int64 head
      | Naked_nativeint head1, Naked_nativeint head2 ->
        let>+ head = join_head_of_kind_naked_nativeint env head1 head2 in
        ET.create_naked_nativeint head
      | Naked_vec128 head1, Naked_vec128 head2 ->
        let>+ head = join_head_of_kind_naked_vec128 env head1 head2 in
        ET.create_naked_vec128 head
      | Rec_info head1, Rec_info head2 ->
        let>+ head = join_head_of_kind_rec_info env head1 head2 in
        ET.create_rec_info head
      | Region head1, Region head2 ->
        let>+ head = join_head_of_kind_region env head1 head2 in
        ET.create_region head
      | ( ( Value _ | Naked_immediate _ | Naked_float _ | Naked_float32 _
          | Naked_int32 _ | Naked_vec128 _ | Naked_int64 _ | Naked_nativeint _
          | Rec_info _ | Region _ ),
          _ ) ->
        assert false
    in
    match expanded_or_unknown with
    | Known expanded -> Known expanded, env
    | Unknown -> Known (ET.unknown_like expanded1), env)

and join_head_of_kind_value env (head1 : TG.head_of_kind_value)
    (head2 : TG.head_of_kind_value) : TG.head_of_kind_value join_result =
  let non_null : _ Or_unknown_or_bottom.t * _ =
    match head1.non_null, head2.non_null with
    | Unknown, _ | _, Unknown -> Or_unknown_or_bottom.Unknown, env
    | Bottom, Bottom -> Bottom, env
    | Bottom, Ok x ->
      let env =
        import_names
          ~from_env:(Join_env.Binary.right_join_env env)
          env
          (TG.Head_of_kind_value_non_null.free_names x)
      in
      Ok x, env
    | Ok x, Bottom ->
      let env =
        import_names
          ~from_env:(Join_env.Binary.left_join_env env)
          env
          (TG.Head_of_kind_value_non_null.free_names x)
      in
      Ok x, env
    | Ok head1, Ok head2 -> (
      match join_head_of_kind_value_non_null env head1 head2 with
      | Unknown, env -> Or_unknown_or_bottom.Unknown, env
      | Known head, env -> Or_unknown_or_bottom.Ok head, env)
  in
  let is_null : TG.is_null =
    match head1.is_null, head2.is_null with
    | Maybe_null, _ | _, Maybe_null -> Maybe_null
    | Not_null, Not_null -> Not_null
  in
  match[@warning "-4"] non_null, is_null with
  | (Unknown, env), Maybe_null -> Unknown, env
  | (non_null, env), _ -> Known { non_null; is_null }, env

and join_head_of_kind_value_non_null env
    (head1 : TG.head_of_kind_value_non_null)
    (head2 : TG.head_of_kind_value_non_null) :
    TG.head_of_kind_value_non_null join_result =
  match head1, head2 with
  | ( Variant
        { blocks = blocks1;
          immediates = imms1;
          extensions = extensions1;
          is_unique = is_unique1
        },
      Variant
        { blocks = blocks2;
          immediates = imms2;
          extensions = extensions2;
          is_unique = is_unique2
        } ) ->
    let>+ blocks, immediates, extensions =
      join_variant env ~blocks1 ~imms1 ~extensions1 ~blocks2 ~imms2 ~extensions2
    in
    (* Uniqueness tracks whether duplication/lifting is allowed. It must always
       be propagated, both for meet and join. *)
    let is_unique = is_unique1 || is_unique2 in
    TG.Head_of_kind_value_non_null.create_variant ~is_unique ~blocks ~immediates
      ~extensions
  | ( Mutable_block { alloc_mode = alloc_mode1 },
      Mutable_block { alloc_mode = alloc_mode2 } ) ->
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    Known (TG.Head_of_kind_value_non_null.create_mutable_block alloc_mode), env
  | Boxed_float32 (n1, alloc_mode1), Boxed_float32 (n2, alloc_mode2) ->
    let>+ n = mark_for_join env n1 n2 in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    TG.Head_of_kind_value_non_null.create_boxed_float32 n alloc_mode
  | Boxed_float (n1, alloc_mode1), Boxed_float (n2, alloc_mode2) ->
    let>+ n = mark_for_join env n1 n2 in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    TG.Head_of_kind_value_non_null.create_boxed_float n alloc_mode
  | Boxed_int32 (n1, alloc_mode1), Boxed_int32 (n2, alloc_mode2) ->
    let>+ n = mark_for_join env n1 n2 in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    TG.Head_of_kind_value_non_null.create_boxed_int32 n alloc_mode
  | Boxed_int64 (n1, alloc_mode1), Boxed_int64 (n2, alloc_mode2) ->
    let>+ n = mark_for_join env n1 n2 in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    TG.Head_of_kind_value_non_null.create_boxed_int64 n alloc_mode
  | Boxed_nativeint (n1, alloc_mode1), Boxed_nativeint (n2, alloc_mode2) ->
    let>+ n = mark_for_join env n1 n2 in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    TG.Head_of_kind_value_non_null.create_boxed_nativeint n alloc_mode
  | Boxed_vec128 (n1, alloc_mode1), Boxed_vec128 (n2, alloc_mode2) ->
    let>+ n = mark_for_join env n1 n2 in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    TG.Head_of_kind_value_non_null.create_boxed_vec128 n alloc_mode
  | ( Closures { by_function_slot = by_function_slot1; alloc_mode = alloc_mode1 },
      Closures
        { by_function_slot = by_function_slot2; alloc_mode = alloc_mode2 } ) ->
    let by_function_slot, env =
      join_row_like_for_closures env by_function_slot1 by_function_slot2
    in
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    ( Known
        (TG.Head_of_kind_value_non_null.create_closures by_function_slot
           alloc_mode),
      env )
  | String strs1, String strs2 ->
    let strs = String_info.Set.union strs1 strs2 in
    Known (TG.Head_of_kind_value_non_null.create_string strs), env
  | ( Array
        { element_kind = element_kind1;
          length = length1;
          contents = array_contents1;
          alloc_mode = alloc_mode1
        },
      Array
        { element_kind = element_kind2;
          length = length2;
          contents = array_contents2;
          alloc_mode = alloc_mode2
        } ) ->
    let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
    let element_kind = join_array_element_kinds element_kind1 element_kind2 in
    let contents, env =
      join_array_contents env array_contents1 array_contents2
        ~joined_element_kind:element_kind
    in
    let>+ length = mark_for_join env length1 length2 in
    TG.Head_of_kind_value_non_null.create_array_with_contents ~element_kind
      ~length contents alloc_mode
  | ( ( Variant _ | Mutable_block _ | Boxed_float _ | Boxed_float32 _
      | Boxed_int32 _ | Boxed_vec128 _ | Boxed_int64 _ | Boxed_nativeint _
      | Closures _ | String _ | Array _ ),
      _ ) ->
    Unknown, env

and join_array_contents env (array_contents1 : TG.array_contents Or_unknown.t)
    (array_contents2 : TG.array_contents Or_unknown.t)
    ~(joined_element_kind : _ Or_unknown_or_bottom.t) : _ join_result =
  join_unknown
    (fun env (array_contents1 : TG.array_contents)
         (array_contents2 : TG.array_contents) : TG.array_contents join_result ->
      match array_contents1, array_contents2 with
      | Mutable, Mutable -> Known TG.Mutable, env
      | Mutable, Immutable _ | Immutable _, Mutable -> Unknown, env
      | Immutable { fields = fields1 }, Immutable { fields = fields2 } -> (
        if Array.length fields1 <> Array.length fields2
        then Unknown, env
        else
          match joined_element_kind with
          | Bottom | Unknown -> Unknown, env
          | Ok _ -> (
            let exception Unknown_result in
            try
              let env_ref = ref env in
              let fields =
                Array.init (Array.length fields1) (fun idx ->
                    match
                      mark_for_join !env_ref fields1.(idx) fields2.(idx)
                    with
                    | Unknown, _ -> raise Unknown_result
                    | Known ty, env ->
                      env_ref := env;
                      ty)
              in
              Known (TG.Immutable { fields }), !env_ref
            with Unknown_result -> Unknown, env)))
    env array_contents1 array_contents2

and join_variant env ~(blocks1 : TG.Row_like_for_blocks.t Or_unknown.t)
    ~(imms1 : TG.t Or_unknown.t) ~(extensions1 : TG.variant_extensions)
    ~(blocks2 : TG.Row_like_for_blocks.t Or_unknown.t)
    ~(imms2 : TG.t Or_unknown.t) ~(extensions2 : TG.variant_extensions) :
    (TG.Row_like_for_blocks.t Or_unknown.t
    * TG.t Or_unknown.t
    * TG.variant_extensions)
    join_result =
  let blocks, env = join_unknown join_row_like_for_blocks env blocks1 blocks2 in
  let imms, env = join_unknown mark_for_join env imms1 imms2 in
  let (env, extensions) : _ * TG.variant_extensions =
    match extensions1, extensions2 with
    | No_extensions, Ext _ | Ext _, No_extensions | No_extensions, No_extensions
      ->
      env, No_extensions
    | ( Ext { when_immediate = when_immediate1; when_block = when_block1 },
        Ext { when_immediate = when_immediate2; when_block = when_block2 } ) ->
      let env0 = env in
      let env, when_immediate =
        join_env_extension env when_immediate1 when_immediate2
      in
      let env, when_block = join_env_extension env when_block1 when_block2 in
      if TEE.is_empty when_immediate && TEE.is_empty when_block
      then env0, No_extensions
      else env, Ext { when_immediate; when_block }
  in
  match blocks, imms, extensions with
  | Unknown, Unknown, No_extensions -> Unknown, env
  | (Unknown | Known _), (Unknown | Known _), (No_extensions | Ext _) ->
    Known (blocks, imms, extensions), env

and join_head_of_kind_naked_immediate env
    (head1 : TG.Head_of_kind_naked_immediate.t)
    (head2 : TG.Head_of_kind_naked_immediate.t) :
    TG.Head_of_kind_naked_immediate.t join_result =
  let module I = Targetint_31_63 in
  match head1, head2 with
  | Naked_immediates is1, Naked_immediates is2 -> (
    assert (not (Targetint_31_63.Set.is_empty is1));
    assert (not (Targetint_31_63.Set.is_empty is2));
    let is = I.Set.union is1 is2 in
    let head = TG.Head_of_kind_naked_immediate.create_naked_immediates is in
    match head with
    | Ok head -> Known head, env
    | Bottom ->
      Misc.fatal_error "Did not expect [Bottom] from [create_naked_immediates]")
  | Is_int ty1, Is_int ty2 ->
    let>+ ty = mark_for_join env ty1 ty2 in
    TG.Head_of_kind_naked_immediate.create_is_int ty
  | Get_tag ty1, Get_tag ty2 ->
    let>+ ty = mark_for_join env ty1 ty2 in
    TG.Head_of_kind_naked_immediate.create_get_tag ty
  | Is_null ty1, Is_null ty2 ->
    let>+ ty = mark_for_join env ty1 ty2 in
    TG.Head_of_kind_naked_immediate.create_is_null ty
  (* From now on: Irregular cases *)
  (* CR vlaviron: There could be improvements based on reduction (trying to
     reduce the is_int and get_tag cases to naked_immediate sets, then joining
     those) but this looks unlikely to be useful and could end up begin quite
     expensive. *)
  | Is_int ty, Naked_immediates is_int | Naked_immediates is_int, Is_int ty -> (
    if I.Set.is_empty is_int
    then Known (TG.Head_of_kind_naked_immediate.create_is_int ty), env
    else
      (* Slightly better than Unknown *)
      let head =
        TG.Head_of_kind_naked_immediate.create_naked_immediates
          (I.Set.add I.zero (I.Set.add I.one is_int))
      in
      match head with
      | Ok head -> Known head, env
      | Bottom ->
        Misc.fatal_error
          "Did not expect [Bottom] from [create_naked_immediates]")
  | Get_tag ty, Naked_immediates tags | Naked_immediates tags, Get_tag ty ->
    if I.Set.is_empty tags
    then Known (TG.Head_of_kind_naked_immediate.create_get_tag ty), env
    else Unknown, env
  | Is_null ty, Naked_immediates is_null | Naked_immediates is_null, Is_null ty
    -> (
    if I.Set.is_empty is_null
    then Known (TG.Head_of_kind_naked_immediate.create_is_null ty), env
    else
      (* Slightly better than Unknown *)
      let head =
        TG.Head_of_kind_naked_immediate.create_naked_immediates
          (I.Set.add I.zero (I.Set.add I.one is_null))
      in
      match head with
      | Ok head -> Known head, env
      | Bottom ->
        Misc.fatal_error
          "Did not expect [Bottom] from [create_naked_immediates]")
  | (Is_int _ | Get_tag _ | Is_null _), (Is_int _ | Get_tag _ | Is_null _) ->
    Unknown, env

and join_head_of_kind_naked_float32 env t1 t2 : _ join_result =
  Known (TG.Head_of_kind_naked_float32.union t1 t2), env

and join_head_of_kind_naked_float env t1 t2 : _ join_result =
  Known (TG.Head_of_kind_naked_float.union t1 t2), env

and join_head_of_kind_naked_int32 env t1 t2 : _ join_result =
  Known (TG.Head_of_kind_naked_int32.union t1 t2), env

and join_head_of_kind_naked_int64 env t1 t2 : _ join_result =
  Known (TG.Head_of_kind_naked_int64.union t1 t2), env

and join_head_of_kind_naked_nativeint env t1 t2 : _ join_result =
  Known (TG.Head_of_kind_naked_nativeint.union t1 t2), env

and join_head_of_kind_naked_vec128 env t1 t2 : _ join_result =
  Known (TG.Head_of_kind_naked_vec128.union t1 t2), env

and join_head_of_kind_rec_info env t1 t2 : _ join_result =
  if Rec_info_expr.equal t1 t2 then Known t1, env else Unknown, env

and join_head_of_kind_region env () () : _ join_result = Known (), env

(* Note that unlike the [join] function on types, for structures (closures
   entry, row-like, etc.) the return type is [t] (and not [t Or_unknown.t]).
   This simplifies some parts of the code a bit that cannot handle the Unknown
   case gracefully. All join functions for structures can handle [Unknown]
   results from generic [join]s without needing to propagate them. *)

and join_row_like :
      'lattice 'shape 'maps_to 'row_tag 'known.
      free_names_maps_to:('maps_to -> Name_occurrences.t) ->
      free_names_index:('lattice -> Name_occurrences.t) ->
      free_names_shape:('shape -> Name_occurrences.t) ->
      join_maps_to:
        (Join_env.Binary.t ->
        'shape ->
        'maps_to ->
        'maps_to ->
        'maps_to * Join_env.Binary.t) ->
      equal_index:('lattice -> 'lattice -> bool) ->
      inter_index:('lattice -> 'lattice -> 'lattice) ->
      join_shape:('shape -> 'shape -> 'shape Or_unknown.t) ->
      merge_map_known:
        (('row_tag ->
         ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option ->
         ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option ->
         ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option) ->
        'known ->
        'known ->
        'known) ->
      Join_env.Binary.t ->
      known1:'known ->
      known2:'known ->
      other1:('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t ->
      other2:('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t ->
      ('known * ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t)
      join_result =
 fun ~free_names_maps_to ~free_names_index ~free_names_shape ~join_maps_to
     ~equal_index ~inter_index ~join_shape ~merge_map_known join_env ~known1
     ~known2 ~other1 ~other2 ->
  let join_index (i1 : ('lattice, 'shape) TG.row_like_index)
      (i2 : ('lattice, 'shape) TG.row_like_index) :
      ('lattice, 'shape) TG.row_like_index Or_unknown.t =
    match join_shape i1.shape i2.shape with
    | Unknown -> Unknown
    | Known shape -> (
      let return_index domain =
        Or_unknown.Known (TG.Row_like_index.create ~domain ~shape)
      in
      match i1.domain, i2.domain with
      | Known i1', Known i2' ->
        if equal_index i1' i2'
        then return_index i1.domain
        else
          (* We can't represent exactly the union, This is the best
             approximation *)
          return_index (TG.Row_like_index_domain.at_least (inter_index i1' i2'))
      | Known i1', At_least i2'
      | At_least i1', Known i2'
      | At_least i1', At_least i2' ->
        return_index (TG.Row_like_index_domain.at_least (inter_index i1' i2')))
  in
  let free_names_index (index : ('lattice, 'shape) TG.row_like_index) =
    let free_names_domain =
      match index.domain with
      | Known domain -> free_names_index domain
      | At_least domain -> free_names_index domain
    in
    Name_occurrences.union free_names_domain (free_names_shape index.shape)
  in
  let join_case join_env
      (case1 : ('lattice, 'shape, 'maps_to) TG.Row_like_case.t)
      (case2 : ('lattice, 'shape, 'maps_to) TG.Row_like_case.t) : _ join_result
      =
    let index = join_index case1.index case2.index in
    match index with
    | Known index ->
      let maps_to, join_env =
        join_maps_to join_env index.shape case1.maps_to case2.maps_to
      in
      let join_env, env_extension =
        join_env_extension join_env case1.env_extension case2.env_extension
      in
      Known (TG.Row_like_case.create ~maps_to ~index ~env_extension), join_env
    | Unknown -> Unknown, join_env
  in
  let free_names_case (case : ('lattice, 'shape, 'maps_to) TG.Row_like_case.t) =
    Name_occurrences.union_list
      [ free_names_index case.index;
        free_names_maps_to case.maps_to;
        TEE.free_names case.env_extension ]
  in
  let join_knowns join_env
      (case1 :
        ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option)
      (case2 :
        ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_unknown.t option) :
      ('lattice, 'shape, 'maps_to) TG.Row_like_case.t join_result option =
    match case1, case2 with
    | None, None -> None
    | Some Unknown, _ | _, Some Unknown -> Some (Unknown, join_env)
    | Some (Known case1), None -> (
      match other2 with
      | Bottom ->
        let join_env =
          import_names
            ~from_env:(Join_env.Binary.left_join_env join_env)
            join_env (free_names_case case1)
        in
        Some (Known case1, join_env)
      | Ok other_case -> Some (join_case join_env case1 other_case))
    | None, Some (Known case2) -> (
      match other1 with
      | Bottom ->
        let join_env =
          (* try *)
          import_names
            ~from_env:(Join_env.Binary.right_join_env join_env)
            join_env (free_names_case case2)
          (* with Misc.Fatal_error -> Format.eprintf "Right env: %a@." TE.print
             (Join_env.Binary.right_join_env join_env); Format.eprintf "Free
             names: %a" Name_occurrences.print (free_names_case case2); assert
             false *)
        in
        Some (Known case2, join_env)
      | Ok other_case -> Some (join_case join_env other_case case2))
    | Some (Known case1), Some (Known case2) ->
      Some (join_case join_env case1 case2)
  in
  let known, join_env =
    let join_env_ref = ref join_env in
    let known =
      merge_map_known
        (fun _tag case1 case2 ->
          match join_knowns !join_env_ref case1 case2 with
          | Some (case, join_env) ->
            join_env_ref := join_env;
            Some case
          | None -> None)
        known1 known2
    in
    known, !join_env_ref
  in
  let other :
      ('lattice, 'shape, 'maps_to) TG.Row_like_case.t Or_bottom.t join_result =
    match other1, other2 with
    | Bottom, Bottom -> Known Bottom, join_env
    | Ok other1, Bottom ->
      let join_env =
        import_names
          ~from_env:(Join_env.Binary.left_join_env join_env)
          join_env (free_names_case other1)
      in
      Known (Ok other1), join_env
    | Bottom, Ok other2 ->
      let join_env =
        import_names
          ~from_env:(Join_env.Binary.right_join_env join_env)
          join_env (free_names_case other2)
      in
      Known (Ok other2), join_env
    | Ok other1, Ok other2 ->
      map_join_result (join_case join_env other1 other2) ~f:(fun case ->
          Or_bottom.Ok case)
  in
  match other with
  | Known other, join_env -> Known (known, other), join_env
  | Unknown, join_env -> Unknown, join_env

and join_row_like_for_blocks env
    ({ known_tags = known1; other_tags = other1; alloc_mode = alloc_mode1 } :
      TG.Row_like_for_blocks.t)
    ({ known_tags = known2; other_tags = other2; alloc_mode = alloc_mode2 } :
      TG.Row_like_for_blocks.t) : _ join_result =
  let join_shape shape1 shape2 : _ Or_unknown.t =
    if K.Block_shape.equal shape1 shape2 then Known shape1 else Unknown
  in
  map_join_result
    (join_row_like ~free_names_maps_to:TG.Product.Int_indexed.free_names
       ~free_names_index:(fun _ -> Name_occurrences.empty)
       ~free_names_shape:(fun _ -> Name_occurrences.empty)
       ~join_maps_to:join_int_indexed_product ~equal_index:TG.Block_size.equal
       ~inter_index:TG.Block_size.inter ~join_shape
       ~merge_map_known:Tag.Map.merge env ~known1 ~known2 ~other1 ~other2)
    ~f:(fun (known_tags, other_tags) ->
      let alloc_mode = join_alloc_mode alloc_mode1 alloc_mode2 in
      TG.Row_like_for_blocks.create_raw ~known_tags ~other_tags ~alloc_mode)

and join_row_like_for_closures env
    ({ known_closures = known1; other_closures = other1 } :
      TG.Row_like_for_closures.t)
    ({ known_closures = known2; other_closures = other2 } :
      TG.Row_like_for_closures.t) : TG.Row_like_for_closures.t * _ =
  let merge_map_known join_case known1 known2 =
    Function_slot.Map.merge
      (fun function_slot case1 case2 ->
        let case1 = Option.map Or_unknown.known case1 in
        let case2 = Option.map Or_unknown.known case2 in
        match (join_case function_slot case1 case2 : _ Or_unknown.t option) with
        | None -> None
        | Some (Known case) -> Some case
        | Some Unknown ->
          Misc.fatal_error "Join row_like case for closures returned Unknown")
      known1 known2
  in
  match
    join_row_like ~free_names_maps_to:TG.Closures_entry.free_names
      ~free_names_index:Set_of_closures_contents.free_names
      ~free_names_shape:(fun () -> Name_occurrences.empty)
      ~join_maps_to:(fun env () x y -> join_closures_entry env x y)
      ~equal_index:Set_of_closures_contents.equal
      ~inter_index:Set_of_closures_contents.inter
      ~join_shape:(fun () () -> Or_unknown.Known ())
      ~merge_map_known env ~known1 ~known2 ~other1 ~other2
  with
  | Known (known_closures, other_closures), env ->
    TG.Row_like_for_closures.create_raw ~known_closures ~other_closures, env
  | Unknown, _ ->
    Misc.fatal_error "Join row_like case for closures returned Unknown"

and join_closures_entry env
    ({ function_types = function_types1;
       closure_types = closure_types1;
       value_slot_types = value_slot_types1
     } :
      TG.Closures_entry.t)
    ({ function_types = function_types2;
       closure_types = closure_types2;
       value_slot_types = value_slot_types2
     } :
      TG.Closures_entry.t) : TG.Closures_entry.t * _ =
  let function_types, env =
    let env_ref = ref env in
    let function_types =
      Function_slot.Map.merge
        (fun _function_slot func_type1 func_type2 ->
          match func_type1, func_type2 with
          | None, None | Some _, None | None, Some _ -> None
          | Some func_type1, Some func_type2 ->
            let func_type, env = join_function_type env func_type1 func_type2 in
            env_ref := env;
            Some func_type)
        function_types1 function_types2
    in
    function_types, !env_ref
  in
  let closure_types, env =
    join_function_slot_indexed_product env closure_types1 closure_types2
  in
  let value_slot_types, env =
    join_value_slot_indexed_product env value_slot_types1 value_slot_types2
  in
  TG.Closures_entry.create ~function_types ~closure_types ~value_slot_types, env

and join_generic_product :
      'key 'key_map.
      Join_env.Binary.t ->
      components_by_index1:'key_map ->
      components_by_index2:'key_map ->
      merge:
        (('key -> TG.t option -> TG.t option -> TG.t option) ->
        'key_map ->
        'key_map ->
        'key_map) ->
      'key_map * Join_env.Binary.t =
 fun env ~components_by_index1 ~components_by_index2 ~merge ->
  let env_ref = ref env in
  let components_by_index =
    merge
      (fun _index ty1_opt ty2_opt ->
        match ty1_opt, ty2_opt with
        | None, _ | _, None -> None
        | Some ty1, Some ty2 -> (
          match mark_for_join !env_ref ty1 ty2 with
          | Known ty, env ->
            env_ref := env;
            Some ty
          | Unknown, env ->
            env_ref := env;
            None))
      components_by_index1 components_by_index2
  in
  components_by_index, !env_ref

and join_function_slot_indexed_product env
    ({ function_slot_components_by_index = components_by_index1 } :
      TG.Product.Function_slot_indexed.t)
    ({ function_slot_components_by_index = components_by_index2 } :
      TG.Product.Function_slot_indexed.t) :
    TG.Product.Function_slot_indexed.t * _ =
  let function_slot_components_by_index, env =
    join_generic_product env ~components_by_index1 ~components_by_index2
      ~merge:Function_slot.Map.merge
  in
  TG.Product.Function_slot_indexed.create function_slot_components_by_index, env

and join_value_slot_indexed_product env
    ({ value_slot_components_by_index = components_by_index1 } :
      TG.Product.Value_slot_indexed.t)
    ({ value_slot_components_by_index = components_by_index2 } :
      TG.Product.Value_slot_indexed.t) : TG.Product.Value_slot_indexed.t * _ =
  let value_slot_components_by_index, env =
    join_generic_product env ~components_by_index1 ~components_by_index2
      ~merge:Value_slot.Map.merge
  in
  TG.Product.Value_slot_indexed.create value_slot_components_by_index, env

and join_int_indexed_product env shape (fields1 : TG.Product.Int_indexed.t)
    (fields2 : TG.Product.Int_indexed.t) :
    TG.Product.Int_indexed.t * Join_env.Binary.t =
  let length1 = Array.length fields1 in
  let length2 = Array.length fields2 in
  let length = min length1 length2 in
  let exception Exit in
  let all_phys_equal =
    try
      for index = 0 to length - 1 do
        if fields1.(index) != fields2.(index) then raise Exit
      done;
      true
    with Exit -> false
  in
  let fields, env =
    if false && all_phys_equal
    then
      if Int.equal length1 length
      then fields1, env
      else (
        assert (Int.equal length2 length);
        fields2, env)
    else
      let env_ref = ref env in
      let fields =
        Array.init length (fun index ->
            if false && fields1.(index) == fields2.(index)
            then fields1.(index)
            else
              match mark_for_join !env_ref fields1.(index) fields2.(index) with
              | Unknown, env ->
                env_ref := env;
                MTC.unknown_from_shape shape index
              | Known ty, env ->
                env_ref := env;
                ty)
      in
      fields, !env_ref
  in
  TG.Product.Int_indexed.create_from_array fields, env

and join_function_type (env : Join_env.Binary.t)
    (func_type1 : TG.Function_type.t Or_unknown_or_bottom.t)
    (func_type2 : TG.Function_type.t Or_unknown_or_bottom.t) :
    TG.Function_type.t Or_unknown_or_bottom.t * _ =
  match func_type1, func_type2 with
  | Bottom, Bottom -> Bottom, env
  | Bottom, Unknown | Unknown, Bottom -> Unknown, env
  | Bottom, Ok func_type ->
    let env =
      import_names
        ~from_env:(Join_env.Binary.right_join_env env)
        env
        (TG.Function_type.free_names func_type)
    in
    Ok func_type, env
  | Ok func_type, Bottom ->
    let env =
      import_names
        ~from_env:(Join_env.Binary.left_join_env env)
        env
        (TG.Function_type.free_names func_type)
    in
    Ok func_type, env
  | Unknown, _ | _, Unknown -> Unknown, env
  | ( Ok { code_id = code_id1; rec_info = rec_info1 },
      Ok { code_id = code_id2; rec_info = rec_info2 } ) -> (
    let target_typing_env = Join_env.Binary.target_join_env env in
    (* As a note, sometimes it might be preferable not to do the code age
       relation join, and take the hit of an indirect call in exchange for
       calling specialised versions of the code. Maybe an annotation would be
       needed. Dolan thinks there isn't a single good answer here and we should
       maybe just not do the join. (The code age relation meet would remain
       though as it's useful elsewhere.) *)
    match
      Code_age_relation.join
        ~target_t:(TE.code_age_relation target_typing_env)
        ~resolver:(TE.code_age_relation_resolver target_typing_env)
        (TE.code_age_relation (Join_env.Binary.left_join_env env))
        (TE.code_age_relation (Join_env.Binary.right_join_env env))
        code_id1 code_id2
    with
    | Unknown -> Unknown, env
    | Known code_id -> (
      match mark_for_join env rec_info1 rec_info2 with
      | Known rec_info, env ->
        Ok (TG.Function_type.create code_id ~rec_info), env
      | Unknown, env -> Unknown, env))

and join_env_extension env (ext1 : TEE.t) (ext2 : TEE.t) :
    Join_env.Binary.t * TEE.t =
  Join_env.join_binary_env_extensions ~meet_type:(New meet_type)
    ~join_ty:(join ?bound_name:None) env ext1 ext2

(* Exposed to the outside world with Or_bottom type *)
let meet env ty1 ty2 : _ Or_bottom.t =
  if TE.is_bottom env
  then Bottom
  else
    let scope = TE.current_scope env in
    let scoped_env = TE.increment_scope env in
    match meet scoped_env ty1 ty2 with
    | Bottom _ -> Bottom
    | Ok (r, scoped_env) ->
      let res_ty = extract_value r ty1 ty2 in
      if TG.is_obviously_bottom res_ty
      then Bottom
      else
        let env_extension =
          TEL.as_extension (TE.cut scoped_env ~cut_after:scope)
        in
        Ok (res_ty, env_extension)

let meet_shape env t ~shape ~result_var ~result_kind : _ Or_bottom.t =
  if TE.is_bottom env
  then Bottom
  else
    let result = Bound_name.create_var result_var in
    let env = TE.add_definition env result result_kind in
    match meet env t shape with
    | Bottom -> Bottom
    | Ok (_, env_extension) -> Ok env_extension

let meet_env_extension env ext1 ext2 : _ Or_bottom.t =
  if TE.is_bottom env
  then Bottom
  else
    let scope = TE.current_scope env in
    let scoped_env = TE.increment_scope env in
    match
      TE.add_env_extension_strict scoped_env ext1 ~meet_type:(New meet_type)
    with
    | Bottom -> Bottom
    | Ok scoped_env -> (
      match
        TE.add_env_extension_strict scoped_env ext2 ~meet_type:(New meet_type)
      with
      | Bottom -> Bottom
      | Ok scoped_env ->
        let env_extension =
          TEL.as_extension_without_bindings (TE.cut scoped_env ~cut_after:scope)
        in
        Ok env_extension)
