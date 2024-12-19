(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Nathanaëlle Courant, Pierre Chambart, OCamlPro               *)
(*                                                                        *)
(*   Copyright 2024 OCamlPro SAS                                          *)
(*   Copyright 2024 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module Field = struct
  module M = struct
    type return_kind =
      | Normal of int
      | Exn

    type closure_entry_point =
      | Indirect_code_pointer
      | Direct_code_pointer

    type t =
      | Block of int
      | Value_slot of Value_slot.t
      | Function_slot of Function_slot.t
      | Code_of_closure
      | Is_int
      | Get_tag
      | Apply of closure_entry_point * return_kind

    let compare_return_kind r1 r2 =
      match r1, r2 with
      | Normal i, Normal j -> compare i j
      | Exn, Exn -> 0
      | Normal _, Exn -> 1
      | Exn, Normal _ -> -1

    let closure_entry_point_to_int = function
      | Indirect_code_pointer -> 0
      | Direct_code_pointer -> 1

    let compare t1 t2 =
      match t1, t2 with
      | Block n1, Block n2 -> Int.compare n1 n2
      | Value_slot v1, Value_slot v2 -> Value_slot.compare v1 v2
      | Function_slot f1, Function_slot f2 -> Function_slot.compare f1 f2
      | Code_of_closure, Code_of_closure -> 0
      | Is_int, Is_int -> 0
      | Get_tag, Get_tag -> 0
      | Apply (ep1, r1), Apply (ep2, r2) ->
        let c =
          Int.compare
            (closure_entry_point_to_int ep1)
            (closure_entry_point_to_int ep2)
        in
        if c <> 0 then c else compare_return_kind r1 r2
      | ( Block _,
          ( Value_slot _ | Function_slot _ | Code_of_closure | Is_int | Get_tag
          | Apply _ ) ) ->
        -1
      | ( ( Value_slot _ | Function_slot _ | Code_of_closure | Is_int | Get_tag
          | Apply _ ),
          Block _ ) ->
        1
      | ( Value_slot _,
          (Function_slot _ | Code_of_closure | Is_int | Get_tag | Apply _) ) ->
        -1
      | ( (Function_slot _ | Code_of_closure | Is_int | Get_tag | Apply _),
          Value_slot _ ) ->
        1
      | Function_slot _, (Code_of_closure | Is_int | Get_tag | Apply _) -> -1
      | (Code_of_closure | Is_int | Get_tag | Apply _), Function_slot _ -> 1
      | Code_of_closure, (Is_int | Get_tag | Apply _) -> -1
      | (Is_int | Get_tag | Apply _), Code_of_closure -> 1
      | Is_int, (Get_tag | Apply _) -> -1
      | (Get_tag | Apply _), Is_int -> 1
      | Get_tag, Apply _ -> -1
      | Apply _, Get_tag -> 1

    let equal a b = compare a b = 0

    let hash = Hashtbl.hash

    let closure_entry_point_to_string = function
      | Indirect_code_pointer -> "Indirect_code_pointer"
      | Direct_code_pointer -> "Direct_code_pointer"

    let print ppf = function
      | Block i -> Format.fprintf ppf "%i" i
      | Value_slot s -> Format.fprintf ppf "%a" Value_slot.print s
      | Function_slot f -> Format.fprintf ppf "%a" Function_slot.print f
      | Code_of_closure -> Format.fprintf ppf "Code"
      | Is_int -> Format.fprintf ppf "Is_int"
      | Get_tag -> Format.fprintf ppf "Get_tag"
      | Apply (ep, Normal i) ->
        Format.fprintf ppf "Apply (%s, Normal %i)"
          (closure_entry_point_to_string ep)
          i
      | Apply (ep, Exn) ->
        Format.fprintf ppf "Apply (%s, Exn)" (closure_entry_point_to_string ep)
  end

  include M
  module Container = Container_types.Make (M)
  module Map = Container.Map
end

module Dep = struct
  module M = struct
    type t =
      | Alias of { target : Name.t }
      | Use of { target : Code_id_or_name.t }
      | Accessor of
          { target : Name.t;
            relation : Field.t
          }
      | Constructor of
          { target : Code_id_or_name.t;
            relation : Field.t
          }
      | Alias_if_def of
          { target : Name.t;
            if_defined : Code_id.t
          }
      | Propagate of
          { target : Name.t;
            source : Name.t
          }

    let compare t1 t2 =
      let numbering = function
        | Alias _ -> 0
        | Use _ -> 1
        | Accessor _ -> 2
        | Constructor _ -> 3
        | Alias_if_def _ -> 4
        | Propagate _ -> 5
      in
      match t1, t2 with
      | Alias { target = target1 }, Alias { target = target2 } ->
        Name.compare target1 target2
      | Use { target = target1 }, Use { target = target2 } ->
        Code_id_or_name.compare target1 target2
      | ( Accessor { target = target1; relation = relation1 },
          Accessor { target = target2; relation = relation2 } ) ->
        let c = Name.compare target1 target2 in
        if c <> 0 then c else Field.compare relation1 relation2
      | ( Constructor { target = target1; relation = relation1 },
          Constructor { target = target2; relation = relation2 } ) ->
        let c = Code_id_or_name.compare target1 target2 in
        if c <> 0 then c else Field.compare relation1 relation2
      | ( Alias_if_def { target = target1; if_defined = if_defined1 },
          Alias_if_def { target = target2; if_defined = if_defined2 } ) ->
        let c = Name.compare target1 target2 in
        if c <> 0 then c else Code_id.compare if_defined1 if_defined2
      | ( Propagate { target = target1; source = source1 },
          Propagate { target = target2; source = source2 } ) ->
        let c = Name.compare target1 target2 in
        if c <> 0 then c else Name.compare source1 source2
      | ( ( Alias _ | Use _ | Accessor _ | Constructor _ | Alias_if_def _
          | Propagate _ ),
          _ ) ->
        Int.compare (numbering t1) (numbering t2)

    let equal x y = compare x y = 0

    let hash = Hashtbl.hash

    let print ppf = function
      | Alias { target } -> Format.fprintf ppf "Alias %a" Name.print target
      | Use { target } ->
        Format.fprintf ppf "Use %a" Code_id_or_name.print target
      | Accessor { target; relation } ->
        Format.fprintf ppf "Accessor %a %a" Field.print relation Name.print
          target
      | Constructor { target; relation } ->
        Format.fprintf ppf "Constructor %a %a" Field.print relation
          Code_id_or_name.print target
      | Alias_if_def { target; if_defined } ->
        Format.fprintf ppf "Alias_if_def %a %a" Name.print target Code_id.print
          if_defined
      | Propagate { target; source } ->
        Format.fprintf ppf "Propagate %a %a" Name.print target Name.print source
  end

  include M
  module Container = Container_types.Make (M)
  module Set = Container.Set
end

type graph =
  { name_to_dep : (Code_id_or_name.t, Dep.Set.t) Hashtbl.t;
    used : (Code_id_or_name.t, unit) Hashtbl.t;
    mutable datalog : Datalog.database;
    schedule : Datalog.Schedule.t;
    mutable field_map : int Field.Map.t * Field.t Numeric_types.Int.Map.t * int
  }

let pp_used_graph ppf (graph : graph) =
  let elts = List.of_seq @@ Hashtbl.to_seq graph.used in
  let pp ppf l =
    let pp_sep ppf () = Format.pp_print_string ppf "@, " in
    let pp ppf (name, ()) =
      Format.fprintf ppf "%a" Code_id_or_name.print name
    in
    Format.pp_print_list ~pp_sep pp ppf l
  in
  Format.fprintf ppf "{ %a }" pp elts

let rr = ref (Field.Map.empty, Numeric_types.Int.Map.empty, 0)

let field =
  Datalog.ColumnType.make "field" ~print:(fun ppf i ->
      let _, rev_map, _ = !rr in
      Field.print ppf (Numeric_types.Int.Map.find i rev_map))

let field_datalog_type = field

let alias_rel =
  Datalog.Relation.create ~name:"alias"
    [Code_id_or_name.datalog_column_type; Code_id_or_name.datalog_column_type]

let use_rel =
  Datalog.Relation.create ~name:"use"
    [Code_id_or_name.datalog_column_type; Code_id_or_name.datalog_column_type]

let accessor_rel =
  Datalog.Relation.create ~name:"accessor"
    [ Code_id_or_name.datalog_column_type;
      field;
      Code_id_or_name.datalog_column_type ]

let constructor_rel =
  Datalog.Relation.create ~name:"constructor"
    [ Code_id_or_name.datalog_column_type;
      field;
      Code_id_or_name.datalog_column_type ]

let propagate_rel =
  Datalog.Relation.create ~name:"propagate"
    [ Code_id_or_name.datalog_column_type;
      Code_id_or_name.datalog_column_type;
      Code_id_or_name.datalog_column_type ]

let used_pred =
  Datalog.Relation.create ~name:"used" [Code_id_or_name.datalog_column_type]

let used_fields_top_rel =
  Datalog.Relation.create ~name:"used_fields_top"
    [Code_id_or_name.datalog_column_type; field]

let used_fields_rel =
  Datalog.Relation.create ~name:"used_fields"
    [ Code_id_or_name.datalog_column_type;
      field;
      Code_id_or_name.datalog_column_type ]

let ( ~$ ) = Datalog.Term.variable

let ( @| ) = Datalog.Atom.create

let create () =
  (* propagate *)
  let alias_from_used_propagate =
    Datalog.Rule.create
      ~variables:["if_defined"; "source"; "target"]
      (alias_rel @| [~$"source"; ~$"target"])
      [ used_pred @| [~$"if_defined"];
        propagate_rel @| [~$"if_defined"; ~$"source"; ~$"target"] ]
  in
  (* alias *)
  let used_fields_from_used_fields_alias =
    Datalog.Rule.create
      ~variables:["source"; "target"; "field"; "v"]
      (used_fields_rel @| [~$"target"; ~$"field"; ~$"v"])
      ~negate:
        [ used_pred @| [~$"target"];
          used_pred @| [~$"source"];
          used_fields_top_rel @| [~$"target"; ~$"field"] ;
          used_fields_top_rel @| [~$"source"; ~$"field"] ;
          ]
      [ alias_rel @| [~$"source"; ~$"target"];
        used_fields_rel @| [~$"source"; ~$"field"; ~$"v"] ]
  in
  let used_fields_top_from_used_fields_alias_top =
    Datalog.Rule.create
      ~variables:["source"; "target"; "field"]
      (used_fields_top_rel @| [~$"target"; ~$"field"])
      ~negate:[used_pred @| [~$"target"]; used_pred @| [~$"source"]]
      [ alias_rel @| [~$"source"; ~$"target"];
        used_fields_top_rel @| [~$"source"; ~$"field"] ]
  in
  let used_from_alias_used =
    Datalog.Rule.create ~variables:["source"; "target"]
      (used_pred @| [~$"target"])
      [alias_rel @| [~$"source"; ~$"target"]; used_pred @| [~$"source"]]
  in
  (* accessor *)
  let used_fields_from_accessor_used =
    Datalog.Rule.create
      ~variables:["source"; "field"; "target"]
      (used_fields_top_rel @| [~$"target"; ~$"field"])
      ~negate:[used_pred @| [~$"target"]]
      [ accessor_rel @| [~$"source"; ~$"field"; ~$"target"];
        used_pred @| [~$"source"] ]
  in
  let used_fields_from_accessor_used_fields =
    Datalog.Rule.create
      ~variables:["source"; "field"; "target"]
      ~existentials:["anyf"; "anyx"]
      (used_fields_rel @| [~$"target"; ~$"field"; ~$"source"])
      ~negate:
        [ used_pred @| [~$"target"];
          used_pred @| [~$"source"];
          used_fields_top_rel @| [~$"target"; ~$"field"] ]
      [ accessor_rel @| [~$"source"; ~$"field"; ~$"target"];
        used_fields_rel @| [~$"source"; ~$"anyf"; ~$"anyx"] ]
  in
  let used_fields_from_accessor_used_fields_top =
    Datalog.Rule.create
      ~variables:["source"; "field"; "target"]
      ~existentials:["anyf"]
      (used_fields_rel @| [~$"target"; ~$"field"; ~$"source"])
      ~negate:
        [ used_pred @| [~$"target"];
          used_pred @| [~$"source"];
          used_fields_top_rel @| [~$"target"; ~$"field"] ]
      [ accessor_rel @| [~$"source"; ~$"field"; ~$"target"];
        used_fields_top_rel @| [~$"source"; ~$"anyf"] ]
  in
  (* constructor *)
  let alias_from_used_fields_constructor =
    Datalog.Rule.create
      ~variables:["source"; "field"; "target"; "v"]
      (alias_rel @| [~$"v"; ~$"target"])
      [ used_fields_rel @| [~$"source"; ~$"field"; ~$"v"];
        constructor_rel @| [~$"source"; ~$"field"; ~$"target"] ]
  in
  let used_from_constructor_field_used =
    Datalog.Rule.create
      ~variables:["source"; "field"; "target"]
      (used_pred @| [~$"target"])
      [ used_fields_top_rel @| [~$"source"; ~$"field"];
        constructor_rel @| [~$"source"; ~$"field"; ~$"target"] ]
  in
  let used_from_constructor_used =
    Datalog.Rule.create
      ~variables:["source"; "field"; "target"]
      (used_pred @| [~$"target"])
      [ used_pred @| [~$"source"];
        constructor_rel @| [~$"source"; ~$"field"; ~$"target"] ]
  in
  (* use *)
  let used_from_used_use =
    Datalog.Rule.create ~variables:["source"; "target"]
      (used_pred @| [~$"target"])
      [used_pred @| [~$"source"]; use_rel @| [~$"source"; ~$"target"]]
  in
  let used_from_used_fields_top_use =
    Datalog.Rule.create ~variables:["source"; "target"] ~existentials:["anyf"]
      (used_pred @| [~$"target"])
      [ used_fields_top_rel @| [~$"source"; ~$"anyf"];
        use_rel @| [~$"source"; ~$"target"] ]
  in
  let used_from_used_fields_use =
    Datalog.Rule.create ~variables:["source"; "target"]
      ~existentials:["anyf"; "anyx"]
      (used_pred @| [~$"target"])
      [ used_fields_rel @| [~$"source"; ~$"anyf"; ~$"anyx"];
        use_rel @| [~$"source"; ~$"target"] ]
  in
  let subsumption_rule_used_used_fields =
    Datalog.Rule.delete ~variables:["source"; "anyf"; "anyx"]
      (used_fields_rel @| [~$"source"; ~$"anyf"; ~$"anyx"])
      [ used_fields_rel @| [~$"source"; ~$"anyf"; ~$"anyx"];
        used_pred @| [~$"source"] ]
  in
  let subsumption_rule_used_used_fields_top =
    Datalog.Rule.delete ~variables:["source"; "anyf"]
      (used_fields_top_rel @| [~$"source"; ~$"anyf"])
      [used_fields_top_rel @| [~$"source"; ~$"anyf"]; used_pred @| [~$"source"]]
  in
  let subsumption_rule_used_fields_used_fields_top =
    Datalog.Rule.delete
      ~variables:["source"; "field"; "anyx"]
      (used_fields_rel @| [~$"source"; ~$"field"; ~$"anyx"])
      [ used_fields_rel @| [~$"source"; ~$"field"; ~$"anyx"];
        used_fields_top_rel @| [~$"source"; ~$"field"] ]
  in
  let schedule =
    Datalog.Schedule.(
      fixpoint
        (list
           [ saturate
               [ subsumption_rule_used_used_fields;
                 subsumption_rule_used_used_fields_top;
                 alias_from_used_propagate;
                 alias_from_used_fields_constructor;
                 used_from_used_fields_use;
                 used_from_used_fields_top_use;
                 used_from_alias_used;
                 used_from_constructor_used;
                 used_from_constructor_field_used;
                 used_from_used_use ];
             saturate [
                 subsumption_rule_used_fields_used_fields_top;
                 used_fields_top_from_used_fields_alias_top;
                 used_fields_from_accessor_used;
             ];
             saturate
               [ 
                 used_fields_from_used_fields_alias;
                 used_fields_from_accessor_used_fields_top;
                 used_fields_from_accessor_used_fields ] ]))
  in
  { name_to_dep = Hashtbl.create 100;
    used = Hashtbl.create 100;
    datalog = Datalog.empty;
    schedule;
    field_map = Field.Map.empty, Numeric_types.Int.Map.empty, 0
  }

let get_field t field =
  let map, rev_map, sz = t.field_map in
  match Field.Map.find_opt field map with
  | Some f -> f
  | None ->
    t.field_map
      <- ( Field.Map.add field sz map,
           Numeric_types.Int.Map.add sz field rev_map,
           sz + 1 );
    rr := t.field_map;
    sz

let add_fact t rel args = t.datalog <- Datalog.add_fact rel args t.datalog

let insert t (k : Code_id_or_name.t) v =
  let tbl = t.name_to_dep in
  (match Hashtbl.find_opt tbl k with
  | None -> Hashtbl.add tbl k (Dep.Set.singleton v)
  | Some s -> Hashtbl.replace tbl k (Dep.Set.add v s));
  match (v : Dep.t) with
  | Alias { target } -> add_fact t alias_rel [k; Code_id_or_name.name target]
  | Use { target } -> add_fact t use_rel [k; target]
  | Accessor { relation; target } ->
    let field = get_field t relation in
    add_fact t accessor_rel [k; field; Code_id_or_name.name target]
  | Constructor { relation; target } ->
    let field = get_field t relation in
    add_fact t constructor_rel [k; field; target]
  | Alias_if_def _ -> ()
  | Propagate { target; source } ->
    add_fact t propagate_rel
      [k; Code_id_or_name.name source; Code_id_or_name.name target]

let inserts t k v =
  (*let tbl = t.name_to_dep in match Hashtbl.find_opt tbl k with | None ->
    Hashtbl.add tbl k v | Some s -> Hashtbl.replace tbl k (Dep.Set.union v s) *)
  Dep.Set.iter (fun dep -> insert t k dep) v

let add_opaque_let_dependency t bp fv =
  let bound_to = Bound_pattern.free_names bp in
  let f () bound_to =
    Name_occurrences.fold_names fv
      ~f:(fun () dep ->
        insert t
          (Code_id_or_name.name bound_to)
          (Dep.Use { target = Code_id_or_name.name dep }))
      ~init:()
  in
  Name_occurrences.fold_names bound_to ~f ~init:()

let add_dep t bound_to dep = insert t bound_to dep

let add_deps t bound_to deps = inserts t bound_to deps

let add_use t (dep : Code_id_or_name.t) =
  Hashtbl.replace t.used dep ();
  add_fact t used_pred [dep]
