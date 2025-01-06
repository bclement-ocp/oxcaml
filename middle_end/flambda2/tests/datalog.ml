module Test = struct
  module Node : sig
    type t (* = private int *)

    val print : Format.formatter -> t -> unit

    val column : t ColumnType.t

    val make : unit -> t
  end = struct
    type t = int

    let print ppf n = Format.fprintf ppf "node:%d" n

    let column = ColumnType.make "node" ~print

    let make =
      let cnt = ref 0 in
      fun () ->
        incr cnt;
        !cnt
  end

  type node = Node.t

  let node = Node.column

  let marked_pred : node rel1 = create_relation ~name:"marked" [node]

  let edge_rel : (node, node) rel2 = create_relation ~name:"edge" [node; node]

  let n1 = Node.make ()

  let n2 = Node.make ()

  let n3 = Node.make ()

  let n4 = Node.make ()

  let n5 = Node.make ()

  let db =
    add_fact marked_pred [n1]
    @@ add_fact edge_rel [n1; n2]
    @@ add_fact edge_rel [n3; n2]
    @@ add_fact edge_rel [n2; n5]
    @@ add_fact edge_rel [n5; n4]
    @@ add_fact edge_rel [n4; n2]
    @@ add_fact edge_rel [n4; n4]
    @@ empty

  let marked = atom marked_pred

  let edge = atom edge_rel

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

  let successor_n1_cursor = Cursor.create ["X"] (fun [x] -> [edge [x; x]])

  let () =
    let successors =
      Cursor.fold successor_n1_cursor db ~init:[] ~f:(fun [n] acc -> n :: acc)
    in
    Format.eprintf "@[<v 2>Successors of %a:@ @[(%a)@]@]@.@." Node.print n1
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
    compile_rule ["X"; "Y"] (fun [x; y] ->
        rule [edge [x; y]; marked [x]] (marked [y]))

  let schedule = Schedule.saturate [mark_successors_rule]

  let () =
    Format.eprintf "@[<v 2>Executing schedule:@ @[<v>%a@]@]@.@." Schedule.print
      schedule

  let db = Schedule.run schedule db

  let () =
    Format.eprintf "@[<v 2>Database after schedule:@ @[<v>%a@]@]@.@." print db
end
