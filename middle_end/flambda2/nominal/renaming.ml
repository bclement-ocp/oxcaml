(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Pierre Chambart and Guillaume Bury, OCamlPro                 *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018--2021 OCamlPro SAS                                    *)
(*   Copyright 2018--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module Continuations = Permutation.Make [@inlined hint] (Continuation)
module Variables = Permutation.Make [@inlined hint] (Variable)
module Code_ids = Permutation.Make [@inlined hint] (Code_id)
module Symbols = Permutation.Make [@inlined hint] (Symbol)
module Coercion = Int_ids.Coercion
module Const = Reg_width_const
module Simple = Int_ids.Simple

module Make_importer (N : sig
  include Container_types.S

  type exported

  val export : t -> exported

  val import : exported -> t

  val import_and_rename : exported -> t

  type serializable

  module Serializable : sig
    val find : serializable -> t -> exported

    val add : serializable -> exported -> t
  end
end) : sig
  type t

  val import : N.serializable -> t

  val apply : t -> N.t -> N.t

  val apply_backwards : t -> N.t -> N.t

  val import_and_bind : t -> N.t -> t * N.t
end = struct
  module In_original_compilation_unit : sig
    type t = private N.t

    val create : N.t -> t

    module Map : Container_types.Map with type key = t

    type serializable

    val import_table : N.serializable -> serializable

    module Serializable : sig
      val find : serializable -> t -> N.exported

      val add : serializable -> N.exported -> t
    end
  end = struct
    type t = N.t

    let create t = t

    module Map = N.Map

    type serializable = N.serializable

    let import_table import_data = import_data

    module Serializable = N.Serializable
  end

  module In_current_compilation_unit : sig
    type t = private N.t

    val create : N.t -> t

    val export : t -> N.exported

    val import : N.exported -> t

    val import_and_rename : N.exported -> t

    module Map : Container_types.Map with type key = t
  end = struct
    type t = N.t

    let create t = t

    let import = N.import

    let export = N.export

    let import_and_rename = N.import_and_rename

    module Map = N.Map
  end

  type t =
    { import_data : In_original_compilation_unit.serializable;
      original_to_current :
        In_current_compilation_unit.t In_original_compilation_unit.Map.t;
      current_to_original :
        In_original_compilation_unit.t In_current_compilation_unit.Map.t
    }

  let import import_data =
    { import_data = In_original_compilation_unit.import_table import_data;
      original_to_current = In_original_compilation_unit.Map.empty;
      current_to_original = In_current_compilation_unit.Map.empty
    }

  let find_data t n =
    try In_original_compilation_unit.Serializable.find t.import_data n
    with Not_found -> assert false

  let apply t n =
    match
      In_original_compilation_unit.Map.find_or_null n t.original_to_current
    with
    | This n -> n
    | Null -> In_current_compilation_unit.import (find_data t n)

  let apply_backwards t n =
    try In_current_compilation_unit.Map.find n t.current_to_original
    with Not_found ->
      In_original_compilation_unit.Serializable.add t.import_data
        (In_current_compilation_unit.export n)

  let import_and_bind t n1 =
    let n2 = In_current_compilation_unit.import_and_rename (find_data t n1) in
    let original_to_current, current_to_original =
      match
        In_original_compilation_unit.Map.find_or_null n1 t.original_to_current
      with
      | Null -> t.original_to_current, t.current_to_original
      | This n3 ->
        ( In_original_compilation_unit.Map.remove n1 t.original_to_current,
          In_current_compilation_unit.Map.remove n3 t.current_to_original )
    in
    let original_to_current =
      In_original_compilation_unit.Map.add n1 n2 original_to_current
    in
    let current_to_original =
      In_current_compilation_unit.Map.add n2 n1 current_to_original
    in
    { t with original_to_current; current_to_original }, n2

  let apply t n =
    let n = apply t (In_original_compilation_unit.create n) in
    (n : In_current_compilation_unit.t :> N.t)

  let apply_backwards t n =
    let n = apply_backwards t (In_current_compilation_unit.create n) in
    (n : In_original_compilation_unit.t :> N.t)

  let import_and_bind t n =
    let t, n = import_and_bind t (In_original_compilation_unit.create n) in
    t, (n : In_current_compilation_unit.t :> N.t)
end
[@@inline]

module Variable_importer = Make_importer (Variable)
module Continuation_importer = Make_importer (Continuation)

module Import_map : sig
  type t

  val create :
    symbols:Symbol.t Symbol.Map.t ->
    variables:Variable.serializable ->
    simples:Simple.t Simple.Map.t ->
    consts:Const.t Const.Map.t ->
    code_ids:Code_id.t Code_id.Map.t ->
    continuations:Continuation.serializable ->
    used_value_slots:Value_slot.Set.t ->
    original_compilation_unit:Compilation_unit.t ->
    t

  val const : t -> Const.t -> Const.t

  val variable : t -> Variable.t -> Variable.t

  val variable_backwards : t -> Variable.t -> Variable.t

  val freshen_variable : t -> Variable.t -> t * Variable.t [@@warning "-32"]

  val symbol : t -> Symbol.t -> Symbol.t

  val symbol_backwards : t -> Symbol.t -> Symbol.t

  val simple : t -> Simple.t -> Simple.t

  val code_id : t -> Code_id.t -> Code_id.t

  val continuation : t -> Continuation.t -> Continuation.t

  val value_slot_is_used : t -> Value_slot.t -> bool
end = struct
  type t =
    { symbols : Symbol.t Symbol.Map.t;
      inverse_symbols : Symbol.t Symbol.Map.t;
      variables : Variable_importer.t;
      simples : Simple.t Simple.Map.t;
      consts : Const.t Const.Map.t;
      code_ids : Code_id.t Code_id.Map.t;
      continuations : Continuation_importer.t;
      used_value_slots : Value_slot.Set.t;
      (* CR vlaviron: [used_value_slots] is here because we need to rewrite the
         types to remove occurrences of unused value slots, as otherwise the
         types can contain references to code that is neither exported nor
         present in the actual object file. But this means rewriting types, and
         the only place a rewriting traversal is done at the moment is during
         import. This solution is not ideal because the missing code IDs will
         still be present in the emitted cmx files, and during the traversal in
         [Flambda_cmx.compute_reachable_names_and_code] we have to assume that
         code IDs can be missing (and so we cannot detect code IDs that are
         really missing at this point). *)
      (* CR lmaurer: We should consider storing the _unused_ value slots rather
         than the used ones. This is the only place in this file where a bigger
         set means _fewer_ changes, and it means we can never know when an
         import map will have no effect (see PR #1398). *)
      original_compilation_unit : Compilation_unit.t
          (* This complements [used_value_slots]. Removal of value slots is only
             allowed for variables that are not used in the compilation unit
             they are defined in. *)
    }

  let create ~symbols ~variables ~simples ~consts ~code_ids ~continuations
      ~used_value_slots ~original_compilation_unit =
    { symbols;
      inverse_symbols =
        Symbol.Map.fold
          (fun old_symbol new_symbol inverse_symbols ->
            Symbol.Map.add new_symbol old_symbol inverse_symbols)
          symbols Symbol.Map.empty;
      variables = Variable_importer.import variables;
      simples;
      consts;
      code_ids;
      continuations = Continuation_importer.import continuations;
      used_value_slots;
      original_compilation_unit
    }

  let rename map orig ~find =
    match find orig map with a -> a | exception Not_found -> orig

  let symbol t orig = rename t.symbols orig ~find:Symbol.Map.find

  let symbol_backwards t renamed =
    rename t.inverse_symbols renamed ~find:Symbol.Map.find

  let variable t orig = Variable_importer.apply t.variables orig

  let variable_backwards t renamed =
    Variable_importer.apply_backwards t.variables renamed

  let freshen_variable t orig =
    let variables, renamed =
      Variable_importer.import_and_bind t.variables orig
    in
    { t with variables }, renamed

  let const t orig = rename t.consts orig ~find:Const.Map.find

  let code_id t orig = rename t.code_ids orig ~find:Code_id.Map.find

  let continuation t orig = Continuation_importer.apply t.continuations orig

  let simple t simple =
    (* [t.simples] only holds those [Simple]s with [Coercion] (analogously to
       the grand table of [Simple]s, see reg_width_things.ml). *)
    rename t.simples simple ~find:Simple.Map.find

  let value_slot_is_used t var =
    if Value_slot.in_compilation_unit var t.original_compilation_unit
    then Value_slot.Set.mem var t.used_value_slots
    else (* This value slot might be used in other units *)
      true
end

type t =
  { continuations : Continuations.t;
    variables : Variables.t;
    code_ids : Code_ids.t;
    symbols : Symbols.t;
    import_map : Import_map.t option
  }

let empty =
  { continuations = Continuations.empty;
    variables = Variables.empty;
    code_ids = Code_ids.empty;
    symbols = Symbols.empty;
    import_map = None
  }

let create_import_map ~symbols ~variables ~simples ~consts ~code_ids
    ~continuations ~used_value_slots ~original_compilation_unit =
  let import_map =
    Import_map.create ~symbols ~variables ~simples ~consts ~code_ids
      ~continuations ~used_value_slots ~original_compilation_unit
  in
  (* It's tempting to set [import_map] to [None] if everything is empty, but
     this is incorrect: an import map of [None] is equivalent to having _all_
     value slots used, not none (see [value_slot_is_used]). *)
  { empty with import_map = Some import_map }

let has_import_map t = Option.is_some t.import_map

let [@ocamlformat "disable"] print ppf
      { continuations; variables; code_ids; symbols; import_map = _; } =
  Format.fprintf ppf "@[<hov 1>(\
      @[<hov 1>(continuations@ %a)@]@ \
      @[<hov 1>(variables@ %a)@])@ \
      @[<hov 1>(code_ids@ %a)@])@ \
      @[<hov 1>(symbols@ %a)@])@ \
      @]"
    Continuations.print continuations
    Variables.print variables
    Code_ids.print code_ids
    Symbols.print symbols

let is_identity { continuations; variables; code_ids; symbols; import_map } =
  Continuations.is_empty continuations
  && Variables.is_empty variables
  && Code_ids.is_empty code_ids && Symbols.is_empty symbols
  &&
  match import_map with
  | None -> true
  | Some _ ->
    (* If there is any import map at all, then this renaming is not necessarily
       the identity: any value slots _not_ present in [used_value_slots] will be
       removed from closures. *)
    false

let compose0
    ~second:
      ({ continuations = continuations2;
         variables = variables2;
         code_ids = code_ids2;
         symbols = symbols2;
         import_map = import_map2
       } as second)
    ~first:
      ({ continuations = continuations1;
         variables = variables1;
         code_ids = code_ids1;
         symbols = symbols1;
         import_map = import_map1
       } as first) =
  { continuations =
      Continuations.compose ~second:continuations2 ~first:continuations1;
    variables = Variables.compose ~second:variables2 ~first:variables1;
    code_ids = Code_ids.compose ~second:code_ids2 ~first:code_ids1;
    symbols = Symbols.compose ~second:symbols2 ~first:symbols1;
    (* The process of simplification of terms together with the collection of
       [Ids_for_export] from types, prior to writing of .cmx files, should
       ensure that only [first] (and not [second]) has an import map. *)
    import_map =
      (match import_map1, import_map2 with
      | None, None -> None
      | Some _, None -> import_map1
      | (None | Some _), Some _ ->
        Misc.fatal_errorf
          "Cannot compose renamings; only the [first] renaming may have an \
           import map.  first:@ %a@ second:@ %a"
          print first print second)
  }

let compose ~second ~first =
  if is_identity second
  then first
  else if is_identity first
  then second
  else compose0 ~second ~first

let add_variable t var1 var2 =
  { t with variables = Variables.compose_one ~first:t.variables var1 var2 }

let add_fresh_variable t var1 ~guaranteed_fresh:var2 =
  { t with
    variables = Variables.compose_one_fresh t.variables var1 ~fresh:var2
  }

let apply_variable t var =
  let var =
    match t.import_map with
    | None -> var
    | Some import_map -> Import_map.variable import_map var
  in
  Variables.apply t.variables var

let bind_fresh_variable t var1 =
  match t.import_map with
  | None ->
    let var1 = apply_variable t var1 in
    let var2 = Variable.rename (apply_variable t var1) in
    let t = add_fresh_variable t var1 ~guaranteed_fresh:var2 in
    t, var2
  | Some import_map ->
    let import_map, var2 = Import_map.freshen_variable import_map var1 in
    { t with import_map = Some import_map }, var2

let apply_variable_backwards t var =
  let var = Variables.apply_backwards t.variables var in
  match t.import_map with
  | None -> var
  | Some import_map -> Import_map.variable_backwards import_map var

let apply_variable_set t vars =
  Variable.Set.fold
    (fun var result ->
      let var = apply_variable t var in
      Variable.Set.add var result)
    vars Variable.Set.empty

let add_symbol t symbol1 symbol2 =
  { t with symbols = Symbols.compose_one ~first:t.symbols symbol1 symbol2 }

let add_fresh_symbol t symbol1 ~guaranteed_fresh:symbol2 =
  { t with
    symbols = Symbols.compose_one_fresh t.symbols symbol1 ~fresh:symbol2
  }

let apply_symbol t symbol =
  let symbol =
    match t.import_map with
    | None -> symbol
    | Some import_map -> Import_map.symbol import_map symbol
  in
  Symbols.apply t.symbols symbol

let apply_symbol_backwards t symbol =
  let symbol = Symbols.apply_backwards t.symbols symbol in
  match t.import_map with
  | None -> symbol
  | Some import_map -> Import_map.symbol_backwards import_map symbol

let apply_symbol_set t symbols =
  Symbol.Set.fold
    (fun symbol result ->
      let symbol = apply_symbol t symbol in
      Symbol.Set.add symbol result)
    symbols Symbol.Set.empty

let apply_name t name =
  Name.pattern_match name
    ~var:(fun var -> Name.var (apply_variable t var))
    ~symbol:(fun symbol -> Name.symbol (apply_symbol t symbol))

let apply_name_backwards t name =
  Name.pattern_match name
    ~var:(fun var -> Name.var (apply_variable_backwards t var))
    ~symbol:(fun symbol -> Name.symbol (apply_symbol_backwards t symbol))

let add_continuation t k1 k2 =
  { t with
    continuations = Continuations.compose_one ~first:t.continuations k1 k2
  }

let add_fresh_continuation t k1 ~guaranteed_fresh:k2 =
  { t with
    continuations = Continuations.compose_one_fresh t.continuations k1 ~fresh:k2
  }

let apply_continuation t k =
  let k =
    match t.import_map with
    | None -> k
    | Some import_map -> Import_map.continuation import_map k
  in
  Continuations.apply t.continuations k

let bind_fresh_continuation t k1 =
  let k1 = apply_continuation t k1 in
  let k2 = Continuation.rename k1 in
  let t = add_fresh_continuation t k1 ~guaranteed_fresh:k2 in
  t, k2

let add_code_id t code_id1 code_id2 =
  { t with code_ids = Code_ids.compose_one ~first:t.code_ids code_id1 code_id2 }

let add_fresh_code_id t code_id1 ~guaranteed_fresh:code_id2 =
  { t with
    code_ids = Code_ids.compose_one_fresh t.code_ids code_id1 ~fresh:code_id2
  }

let apply_code_id t code_id =
  let code_id =
    match t.import_map with
    | None -> code_id
    | Some import_map -> Import_map.code_id import_map code_id
  in
  Code_ids.apply t.code_ids code_id

let apply_const t cst =
  match t.import_map with
  | None -> cst
  | Some import_map -> Import_map.const import_map cst

let apply_simple t simple =
  let simple =
    match t.import_map with
    | None -> simple
    | Some import_map -> Import_map.simple import_map simple
  in
  let[@inline always] name old_name ~coercion:old_coercion =
    let new_name = apply_name t old_name in
    let new_coercion =
      Coercion.map_depth_variables old_coercion ~f:(fun dv ->
          apply_variable t dv)
    in
    if old_name == new_name && old_coercion == new_coercion
    then simple
    else Simple.with_coercion (Simple.name new_name) new_coercion
  in
  (* Constants are never permuted, only freshened upon import. *)
  Simple.pattern_match simple ~name ~const:(fun cst ->
      assert (not (Simple.has_coercion simple));
      Simple.const (apply_const t cst))

let value_slot_is_used t value_slot =
  match t.import_map with
  | None -> true (* N.B. not false! *)
  | Some import_map -> Import_map.value_slot_is_used import_map value_slot
