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

type rule =
  | Rule :
      { cursor : 'k Cursor.t;
        table_id : ('t, 'k, unit) Table.Id.t
      }
      -> rule

type 'a incremental =
  { current : 'a;
    difference : 'a
  }

let incremental ~difference ~current = { current; difference }

let run_rule_incremental ~previous ~diff ~current incremental_db
    (Rule { table_id; cursor }) =
  let is_trie = Table.Id.is_trie table_id in
  let incremental_table =
    incremental
      ~current:(Table.Map.get table_id incremental_db.current)
      ~difference:(Table.Map.get table_id incremental_db.difference)
  in
  let incremental_table' =
    Cursor.seminaive_fold cursor ~previous ~diff ~current
      (fun keys incremental_table ->
        match Trie.find_opt is_trie keys incremental_table.current with
        | Some _ -> incremental_table
        | None ->
          incremental
            ~current:
              (Trie.add_or_replace is_trie keys () incremental_table.current)
            ~difference:
              (Trie.add_or_replace is_trie keys () incremental_table.difference))
      incremental_table
  in
  let set_if_changed db ~before ~after =
    if after == before then db else Table.Map.set table_id after db
  in
  incremental
    ~current:
      (set_if_changed incremental_db.current ~before:incremental_table.current
         ~after:incremental_table'.current)
    ~difference:
      (set_if_changed incremental_db.difference
         ~before:incremental_table.difference
         ~after:incremental_table'.difference)

type t =
  | Saturate of rule list
  | Fixpoint of t list

let fixpoint schedule = Fixpoint schedule

let saturate rules = Saturate rules

let run_rules_incremental rules ~previous ~diff ~current =
  List.fold_left
    (run_rule_incremental ~previous ~diff ~current)
    (incremental ~current ~difference:Table.Map.empty)
    rules

let rec saturate_rules_incremental ~previous ~diff ~current rules full_diff =
  let incremental_db = run_rules_incremental ~previous ~diff ~current rules in
  if Table.Map.is_empty incremental_db.difference
  then incremental ~current ~difference:full_diff
  else
    saturate_rules_incremental ~previous:current ~diff:incremental_db.difference
      ~current:incremental_db.current rules
      (Table.Map.concat ~earlier:full_diff ~later:incremental_db.difference)

let saturate_rules_incremental rules ~previous ~diff ~current =
  saturate_rules_incremental rules Table.Map.empty ~previous ~diff ~current

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

let rec run_incremental schedule ~previous ~diff ~current =
  match schedule with
  | Saturate rules -> saturate_rules_incremental rules ~previous ~diff ~current
  | Fixpoint schedules ->
    run_list_incremental
      (List.map run_incremental schedules)
      ~previous ~diff ~current

let run schedule db =
  (run_incremental schedule ~previous:Table.Map.empty ~diff:db ~current:db)
    .current

let create_rule tid cursor = Rule { table_id = tid; cursor }
