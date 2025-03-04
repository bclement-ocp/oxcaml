(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Basile Clément, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2024--2025 OCamlPro SAS                                    *)
(*   Copyright 2024--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type 'a incremental =
  { current : 'a;
    difference : 'a
  }

let incremental ~difference ~current = { current; difference }

let set_incremental f value t =
  incremental
    ~current:(f value.current t.current)
    ~difference:(f value.difference t.difference)

type binder =
  | Bind_table :
      { table_id : ('t, 'k, 'v) Table.Id.t;
        initial : 't incremental ref;
        current : 't incremental ref
      }
      -> binder

let print_binder ppf (binder : binder) =
  match binder with Bind_table { table_id; _ } -> Table.Id.print ppf table_id

type rule =
  | Recursive_rule :
      { rule_id : int;
        cursor : 'a Cursor.t;
        binders : binder list
      }
      -> rule
  | Materialization_rule :
      { rule_id : int;
        cursor : 'k Cursor.t;
        table_id : ('t, 'k, unit) Table.Id.t
      }
      -> rule

let print_rule ppf rule =
  match rule with
  | Recursive_rule { cursor; binders; _ } ->
    Format.fprintf ppf "@[%a@]@ :- %a"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
         print_binder)
      binders Cursor.print cursor
  | Materialization_rule { cursor; table_id; _ } ->
    Format.fprintf ppf "@[%a@]@ :- %a" Table.Id.print table_id Cursor.print
      cursor

let rule_id (rule : rule) =
  match rule with
  | Recursive_rule { rule_id; _ } -> rule_id
  | Materialization_rule { rule_id; _ } -> rule_id

(* Rule identifiers are only used for statistics collection at the moment. *)
let fresh_rule_id =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    !cnt

type stats = (int, rule * float) Hashtbl.t

let create_stats () = Hashtbl.create 17

let add_timing ~stats rule time =
  let rule_id = rule_id rule in
  Hashtbl.replace stats rule_id
    (rule, time +. try snd (Hashtbl.find stats rule_id) with Not_found -> -0.)

let print_stats ppf stats =
  Format.fprintf ppf "@[<v>";
  Hashtbl.iter
    (fun _ (rule, time) ->
      Format.fprintf ppf "@[@[%a@]@,: %f@]@ " print_rule rule time)
    stats;
  Format.fprintf ppf "@]"

type builder = { tables : (int, binder) Hashtbl.t }

let create_builder () = { tables = Hashtbl.create 17 }

type 'k rule_fn = 'k Heterogenous_list.Constant.hlist -> unit

let call_rule_fn f args = f args

let find_or_create_ref (type t k v) { tables } (table_id : (t, k, v) Table.Id.t)
    : t incremental ref =
  let uid = Table.Id.uid table_id in
  match Hashtbl.find_opt tables uid with
  | None ->
    let empty = Trie.empty (Table.Id.is_trie table_id) in
    let initial = ref (incremental ~difference:empty ~current:empty) in
    let current = ref !initial in
    Hashtbl.replace tables uid (Bind_table { table_id; initial; current });
    current
  | Some (Bind_table { table_id = other_table_id; initial = _; current }) ->
    let Equal = Table.Id.provably_equal_exn other_table_id table_id in
    current

let incremental_rule_fn is_trie table_ref : _ rule_fn =
 fun keys ->
  let incremental_table = !table_ref in
  match Trie.find_opt is_trie keys incremental_table.current with
  | Some _ -> ()
  | None ->
    table_ref
      := incremental
           ~current:
             (Trie.add_or_replace is_trie keys () incremental_table.current)
           ~difference:
             (Trie.add_or_replace is_trie keys () incremental_table.difference)

let add_rule builder tid : _ rule_fn =
  incremental_rule_fn (Table.Id.is_trie tid) (find_or_create_ref builder tid)

let build builder cursor =
  let binders =
    Hashtbl.fold (fun _ binder binders -> binder :: binders) builder.tables []
  in
  Recursive_rule { cursor; binders; rule_id = fresh_rule_id () }

let run_rule_incremental ?stats ~previous ~diff ~current incremental_db rule =
  match rule with
  | Materialization_rule { cursor; table_id; _ } ->
    let is_trie = Table.Id.is_trie table_id in
    let initial_table = Table.Map.get table_id incremental_db.current in
    let table_ref =
      ref
        (incremental ~current:initial_table
           ~difference:(Table.Map.get table_id incremental_db.difference))
    in
    let callback = incremental_rule_fn is_trie table_ref in
    let time0 = Sys.time () in
    Cursor.seminaive_iter cursor callback ~previous ~diff ~current;
    let time1 = Sys.time () in
    let seminaive_time = time1 -. time0 in
    Option.iter (fun stats -> add_timing ~stats rule seminaive_time) stats;
    let incremental_table = !table_ref in
    if initial_table == incremental_table.current
    then incremental_db
    else
      set_incremental (Table.Map.set table_id) incremental_table incremental_db
  | Recursive_rule { cursor; binders; _ } ->
    List.iter
      (fun (Bind_table { table_id; initial; current }) ->
        let table =
          incremental
            ~current:(Table.Map.get table_id incremental_db.current)
            ~difference:(Table.Map.get table_id incremental_db.difference)
        in
        initial := table;
        current := table)
      binders;
    let time0 = Sys.time () in
    Cursor.seminaive_run cursor ~previous ~diff ~current;
    let time1 = Sys.time () in
    let seminaive_time = time1 -. time0 in
    Option.iter (fun stats -> add_timing ~stats rule seminaive_time) stats;
    let set_if_changed db table_id ~before ~after =
      if after == before then db else Table.Map.set table_id after db
    in
    List.fold_left
      (fun incremental_db (Bind_table { table_id; initial; current }) ->
        let initial = !initial and current = !current in
        incremental
          ~current:
            (set_if_changed incremental_db.current table_id
               ~before:initial.current ~after:current.current)
          ~difference:
            (set_if_changed incremental_db.difference table_id
               ~before:initial.difference ~after:current.difference))
      incremental_db binders

type t =
  | Rule of rule
  (* NB: Only non-recursive rules are allowed within a [Rule]. *)
  | Sequence of t list
  (* NB: Schedules in a sequence must be ordered in topological order w.r.t
     their dependencies, i.e. a schedule that writes to table [t] must always be
     placed before all schedules that read from table [t]. *)
  | Saturate of rule list
  | Fixpoint of t list

let materialize ~name ~is_trie ~print_keys cursor =
  let rule_id = fresh_rule_id () in
  let table_id = Table.Id.create ~name ~is_trie ~print_keys ~default_value:() in
  table_id, Rule (Materialization_rule { table_id; cursor; rule_id })

let fixpoint schedule = Fixpoint schedule

let saturate rules = Saturate rules

let seq schedules = Sequence schedules

let run_rules_incremental ?stats rules ~previous ~diff ~current =
  List.fold_left
    (run_rule_incremental ?stats ~previous ~diff ~current)
    (incremental ~current ~difference:Table.Map.empty)
    rules

let rec saturate_rules_incremental ?stats ~previous ~diff ~current rules
    full_diff =
  let incremental_db =
    run_rules_incremental ?stats ~previous ~diff ~current rules
  in
  if Table.Map.is_empty incremental_db.difference
  then incremental ~current ~difference:full_diff
  else
    saturate_rules_incremental ?stats ~previous:current
      ~diff:incremental_db.difference ~current:incremental_db.current rules
      (Table.Map.concat ~earlier:full_diff ~later:incremental_db.difference)

let saturate_rules_incremental ?stats rules ~previous ~diff ~current =
  saturate_rules_incremental ?stats rules Table.Map.empty ~previous ~diff
    ~current

let run_list_incremental fns ~previous ~diff ~current =
  let rec cut ~cut_after result = function
    | [] -> result
    | (ts, diff) :: diffs ->
      if ts > cut_after
      then cut ~cut_after (Table.Map.concat ~earlier:diff ~later:result) diffs
      else result
  in
  let rec loop (current, diffs, ts, full_diff) fns =
    let (current, diffs, ts', full_diff), fns =
      List.fold_left_map
        (fun (db, diffs, ts, full_diff) (fn, previous, cut_after) ->
          let diff = cut ~cut_after Table.Map.empty diffs in
          let incremental_db = fn ~previous ~diff ~current:db in
          if Table.Map.is_empty incremental_db.difference
          then (db, diffs, ts, full_diff), (fn, db, ts)
          else
            let ts = ts + 1 in
            ( ( incremental_db.current,
                (ts, incremental_db.difference) :: diffs,
                ts,
                Table.Map.concat ~earlier:full_diff
                  ~later:incremental_db.difference ),
              (fn, incremental_db.current, ts) ))
        (current, diffs, ts, full_diff)
        fns
    in
    if ts' = ts
    then incremental ~current ~difference:full_diff
    else loop (current, diffs, ts', full_diff) fns
  in
  loop
    (current, [0, diff], 0, Table.Map.empty)
    (List.map (fun fn -> fn, previous, -1) fns)

let rec run_incremental ?stats schedule ~previous ~diff ~current =
  match schedule with
  | Rule rule ->
    run_rule_incremental ?stats ~previous ~diff ~current
      (incremental ~current ~difference:Table.Map.empty)
      rule
  | Saturate rules ->
    saturate_rules_incremental ?stats rules ~previous ~diff ~current
  | Fixpoint schedules ->
    run_list_incremental
      (List.map (run_incremental ?stats) schedules)
      ~previous ~diff ~current
  | Sequence schedules ->
    List.fold_left
      (fun db schedule ->
        let next_db =
          run_incremental ?stats schedule ~previous
            ~diff:(Table.Map.concat ~earlier:diff ~later:db.difference)
            ~current:db.current
        in
        let difference =
          Table.Map.concat ~earlier:db.difference ~later:next_db.difference
        in
        incremental ~current:next_db.current ~difference)
      (incremental ~current ~difference:Table.Map.empty)
      schedules

let run ?stats schedule db =
  (run_incremental ?stats schedule ~previous:Table.Map.empty ~diff:db
     ~current:db)
    .current
