open Flambda2_datalog.Datalog

module Node : sig
  include Column.S

  val make : unit -> t
end = struct
  include Column.Make (struct
    let name = "node"

    let print ppf n = Format.fprintf ppf "node:%d" n
  end)

  let make =
    let cnt = ref 0 in
    fun () ->
      incr cnt;
      !cnt
end

type node = Node.t

let node : _ Column.t = (module Node)

let marked_pred : node rel1 = create_relation ~name:"marked" [node]

module Edge_rel =
  Table.Make
    (struct
      let name = "edge"
    end)
    (Schema.Relation2 (Node) (Node))

let n1 = Node.make ()

let n2 = Node.make ()

let n3 = Node.make ()

let n4 = Node.make ()

let n5 = Node.make ()

let add_edge n1 n2 edge_table = Edge_rel.add_or_replace [n1; n2] () edge_table

let create_edge_table edges =
  List.fold_left
    (fun edge_table (n1, n2) -> add_edge n1 n2 edge_table)
    Edge_rel.empty edges

let edge_table =
  create_edge_table [n1, n2; n3, n2; n2, n5; n5, n4; n4, n2; n4, n4]

let db = add_fact marked_pred [n1] @@ set_table Edge_rel.id edge_table @@ empty

let marked = atom marked_pred

let edge = atom (table_relation Edge_rel.id)

let () = Format.eprintf "@[<v 2>Database:@ @[<v>%a@]@]@.@." print db

let marked_cursor = Cursor.create ["X"] (fun [x] -> [marked [x]])

let edge_cursor = Cursor.create ["X"; "Y"] (fun [x; y] -> [edge [x; y]])

let _reverse_edges =
  Cursor.fold edge_cursor db ~init:[] ~f:(fun [src; dst] acc ->
      (dst, src) :: acc)

let () =
  Format.eprintf "@[<v 2>Marked nodes:@ ";
  Cursor.iter marked_cursor db ~f:(fun [n] ->
      Format.eprintf "- %a@ " Node.print n);
  Format.eprintf "@]@."

let successor_n1_cursor =
  Cursor.create ["X"] (fun [x] -> [edge [Term.constant n1; x]])

let () =
  let successors =
    Cursor.fold successor_n1_cursor db ~init:[] ~f:(fun [n] acc -> n :: acc)
  in
  Format.eprintf "@[<v 2>Successors of %a (with cursor):@ @[(%a)@]@]@.@."
    Node.print n1
    (Format.pp_print_list ~pp_sep:Format.pp_print_space Node.print)
    successors

let () =
  let successors_n1 = Node.Map.find n1 (get_table Edge_rel.id db) in
  let successors = Node.Map.fold (fun n () acc -> n :: acc) successors_n1 [] in
  Format.eprintf "@[<v 2>Successors of %a (direct access):@ @[(%a)@]@]@.@."
    Node.print n1
    (Format.pp_print_list ~pp_sep:Format.pp_print_space Node.print)
    successors

let successor_cursor =
  Cursor.create_with_parameters ~parameters:["P"] ["X"] (fun [p] [x] ->
      [edge [p; x]])

let () =
  let successors =
    Cursor.fold_with_parameters successor_cursor [n2] db ~init:[]
      ~f:(fun [n] acc -> n :: acc)
  in
  Format.eprintf "@[<v 2>Successors of %a (parameterized):@ @[(%a)@]@]@.@."
    Node.print n2
    (Format.pp_print_list ~pp_sep:Format.pp_print_space Node.print)
    successors

let predecessor_cursor =
  Cursor.create_with_parameters ~parameters:["P"] ["X"] (fun [p] [x] ->
      [edge [x; p]])

let () =
  Format.eprintf "@[<v 2>Predecessors of %a (parameterized):@ " Node.print n2;
  Cursor.iter_with_parameters predecessor_cursor [n2] db ~f:(fun [n] ->
      Format.eprintf "- %a@ " Node.print n);
  Format.eprintf "@]@."

let mark_successors_rule =
  compile ["X"; "Y"] (fun [x; y] ->
      where [edge [x; y]; marked [x]] (deduce (marked [y])))

let schedule = Schedule.saturate [mark_successors_rule]

let db = Schedule.run schedule db

let () =
  Format.eprintf "@[<v 2>Database after schedule:@ @[<v>%a@]@]@.@." print db
