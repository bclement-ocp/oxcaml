[@@@warning "-32-37-34-60"]

module Id = struct
  module T = struct
    include Int

    let print = Numbers.Int.print
  end

  include T
  module Tree = Patricia_tree.Make (T)
  module Set = Tree.Set
  module Map = Tree.Map
end

module Trie = struct
  type 'a t =
    | Absent
    | Present of 'a
    | Map of 'a t Id.Map.t

  type 'a iterator =
    | Top_level of 'a t
    | At_value of 'a * 'a iterator
    | In_level of 'a t Id.Map.iterator * 'a iterator

  let iterator trie = Top_level trie

  module Iterator = struct
    type 'a t = 'a iterator

    let current it =
      match it with
      | Top_level _ -> invalid_arg "current"
      | At_value (_, _) -> invalid_arg "current"
      | In_level (level_iterator, _) -> (
        match Id.Map.current level_iterator with
        | Some (key, _) -> Leapfrog.Key key
        | None -> Leapfrog.At_end)

    let advance it =
      match it with
      | Top_level _ -> invalid_arg "advance"
      | At_value (_, _) -> invalid_arg "current"
      | In_level (level_iterator, rest) ->
        let level_iterator = Id.Map.advance level_iterator in
        In_level (level_iterator, rest)

    let seek it key =
      match it with
      | Top_level _ -> invalid_arg "seek"
      | At_value (_, _) -> invalid_arg "seek"
      | In_level (level_it, rest) ->
        let level_it = Id.Map.seek level_it key in
        In_level (level_it, rest)

    let down it =
      match it with
      | Top_level trie -> (
        match trie with
        | Absent | Present _ -> invalid_arg "down"
        | Map m -> In_level (Id.Map.iterator m, it))
      | At_value (_, _) -> invalid_arg "down"
      | In_level (level_it, _) -> (
        match Id.Map.current level_it with
        | None -> In_level (Id.Map.iterator Id.Map.empty, it)
        | Some (_, next_level) -> (
          match next_level with
          | Absent -> In_level (Id.Map.iterator Id.Map.empty, it)
          | Present v -> At_value (v, it)
          | Map m -> In_level (Id.Map.iterator m, it)))

    let up it =
      match it with
      | Top_level _ -> invalid_arg "up"
      | At_value (_, parent) | In_level (_, parent) -> parent

    module I = struct
      type 'a t = 'a iterator ref

      let create () = ref (Top_level Absent)

      let current it = current !it

      let advance it = it := advance !it

      let seek it key = it := seek !it key

      let down it = it := down !it

      let up it = it := up !it
    end
  end

  let create ~arity =
    assert (arity >= 0);
    if arity = 0 then Absent else Map Id.Map.empty

  let is_empty t =
    match t with
    | Absent -> true
    | Present _ -> false
    | Map m -> Id.Map.is_empty m

  let rec singleton inputs output =
    match inputs with
    | [] -> Present output
    | first_input :: other_inputs ->
      Map (Id.Map.singleton first_input (singleton other_inputs output))

  let rec add_or_replace inputs output t =
    match inputs, t with
    | [], (Absent | Present _) -> Present output
    | [], Map _ | _ :: _, Present _ -> invalid_arg "Trie.add"
    | _ :: _, Absent -> singleton inputs output
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> Map (Id.Map.add first_input (singleton other_inputs output) m)
      | Some subtrie ->
        let subtrie' = add_or_replace other_inputs output subtrie in
        Map (Id.Map.add first_input subtrie' m))

  let rec remove t inputs =
    match inputs, t with
    | _, Absent | [], Present _ -> Absent
    | [], Map _ | _ :: _, Present _ -> invalid_arg "Trie.remove"
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> t
      | Some subtrie ->
        let subtrie' = remove subtrie other_inputs in
        if is_empty subtrie'
        then
          let m = Id.Map.remove first_input m in
          if Id.Map.is_empty m then Absent else Map m
        else Map (Id.Map.add first_input subtrie' m))

  let rec find_opt t inputs =
    match inputs, t with
    | _, Absent -> None
    | [], Present output -> Some output
    | [], Map _ | _ :: _, Present _ -> invalid_arg "Trie.find_opt"
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> None
      | Some subtrie -> find_opt subtrie other_inputs)

  let mem t inputs = Option.is_some (find_opt t inputs)
end

type 'a trie =
  | Value of 'a
  | Map of 'a

type table_id =
  | Table_id of
      { id : int;
        arity : int
      }

let create_table_id =
  let cnt = ref 0 in
  fun ~arity ->
    incr cnt;
    Table_id { id = !cnt; arity }

let pp_table_id ppf (Table_id tid) = Format.fprintf ppf "T%d" tid.id

type variable = int

type symbol = int

type term =
  | Variable of variable
  | Symbol of symbol

let variable v = Variable v

let symbol s = Symbol s

type atom = Atom of table_id * term array

let create_atom a b = Atom (a, b)

type fact = Fact of table_id * symbol array
(* Arguments must be symbols. *)

let print_fact ppf (tid, args) =
  Format.fprintf ppf "@[<hov>T%d(@[<hov>%a@]).@]" tid
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
       Format.pp_print_int)
    (Array.to_list args)

let create_fact a b = Fact (a, b)

type fact_id = int

type index = fact_id Trie.t

type permutation =
  | Identity
  | Permutation of int array

module Permutation = struct
  type t = permutation =
    | Identity
    | Permutation of int array

  let print ppf p =
    match p with
    | Identity -> Format.fprintf ppf "id"
    | Permutation sigma ->
      Format.fprintf ppf "(@[<hov>%a)@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_int)
        (Array.to_list sigma)

  let create sigma =
    try
      Array.iteri (fun i j -> if i <> j then raise Not_found) sigma;
      Identity
    with Not_found -> Permutation sigma

  let apply p a =
    match p with
    | Identity -> a
    | Permutation sigma -> Array.init (Array.length a) (fun i -> a.(sigma.(i)))
end

type expr =
  | Evar of int
  | Esym of symbol

module Projection = struct
  let apply sigma a =
    Array.map (fun s -> match s with Evar n -> a.(n) | Esym s -> s) sigma
end

exception Found of int

let compare_permutation p1 p2 =
  match p1, p2 with
  | Identity, Identity -> 0
  | Identity, Permutation _ -> -1
  | Permutation _, Identity -> 1
  | Permutation p1, Permutation p2 -> (
    let c = Int.compare (Array.length p1) (Array.length p2) in
    if c <> 0
    then c
    else
      try
        for i = 0 to Array.length p1 - 1 do
          let c = Int.compare p1.(i) p2.(i) in
          if c <> 0 then raise (Found c)
        done;
        0
      with Found c -> c)

module Permap = Map.Make (struct
  type t = permutation

  let compare = compare_permutation
end)

type table =
  { facts : symbol array Id.Map.t;
        (** Map from fact identifiers to corresponding facts. *)
    last_fact_id : int;  (** Identifier of the last recorded fact. *)
    primary : index;
    arity : int;
    indices : index Permap.t
  }

let print_table ppf (tid, table) =
  Id.Map.iter
    (fun _ syms -> Format.fprintf ppf "@[<hov>%a@]@ " print_fact (tid, syms))
    table.facts

let create_table ~arity =
  { facts = Id.Map.empty;
    last_fact_id = 0;
    primary = Trie.create ~arity;
    arity;
    indices = Permap.empty
  }

let build_index ~arity facts permutation =
  Id.Map.fold
    (fun fid args index ->
      let args' = Permutation.apply permutation args in
      Trie.add_or_replace (Array.to_list args') fid index)
    facts (Trie.create ~arity)

module Joined_iterator = Leapfrog.Iterator_operations (struct
  type key = int

  let compare_key = Int.compare

  let equal_key = Int.equal

  let print_key = Format.pp_print_int

  include Trie.Iterator.I
end)

let add_fact table args =
  let args_list = Array.to_list args in
  match Trie.find_opt table.primary args_list with
  | Some _ -> table
  | None ->
    let fact_id = table.last_fact_id + 1 in
    let last_fact_id = fact_id in
    (* XXX: do not add to indices immediately? *)
    let primary = Trie.add_or_replace args_list fact_id table.primary in
    let facts = Id.Map.add fact_id args table.facts in
    let indices =
      Permap.mapi
        (fun perm index ->
          Trie.add_or_replace
            (Array.to_list @@ Permutation.apply perm args)
            fact_id index)
        table.indices
    in
    { arity = table.arity; facts; last_fact_id; primary; indices }

let cut_table table ~cut_after =
  let _, _, delta_facts = Id.Map.split cut_after table.facts in
  let arity = table.arity in
  { facts = delta_facts;
    last_fact_id = table.last_fact_id;
    arity = table.arity;
    primary = build_index ~arity delta_facts Permutation.Identity;
    indices =
      Permap.mapi
        (fun perm _ -> build_index ~arity delta_facts perm)
        table.indices
  }

type query =
  | Query :
      { indices : (table_id * permutation * int Trie.iterator ref) array;
        iterator : 'a Joined_iterator.triejoin;
        mutable depth : int;
        output : int array;
        max_depth : int
      }
      -> query

type instruction =
  | Add of table_id * expr array
  | Sequence of instruction list

type rule = Rule of query * instruction

type database =
  { tables : table Id.Map.t;
    levels : int Id.Map.t list;
    current_level : int;
    last_propagation : int Id.Map.t;
    rules : rule list
  }

let print_database ppf db =
  Id.Map.iter
    (fun tid table ->
      Format.fprintf ppf "@[<v>T%d@ @[<v>%a@]@]@ " tid print_table (tid, table))
    db.tables

let current_scope db = db.current_level

let current_level db = Id.Map.map (fun table -> table.last_fact_id) db.tables

let push_scope db =
  let prev_level = current_level db in
  { db with
    levels = prev_level :: db.levels;
    current_level = db.current_level + 1
  }

let pop_scope db =
  match db.levels with
  | [] -> invalid_arg "pop_scope"
  | _ :: levels -> { db with levels; current_level = db.current_level - 1 }

let cut_level db level =
  let tables =
    Id.Map.mapi
      (fun tid table ->
        match Id.Map.find_opt tid level with
        | Some cut_after -> cut_table table ~cut_after
        | None -> table)
      db.tables
  in
  { tables;
    levels = [];
    current_level = 0;
    rules = [];
    last_propagation = Id.Map.empty
  }

let cut_db db ~cut_after =
  match List.nth_opt db.levels (db.current_level - cut_after - 1) with
  | None -> db
  | Some level -> cut_level db level

let empty_db =
  { tables = Id.Map.empty;
    levels = [];
    current_level = 0;
    rules = [];
    last_propagation = Id.Map.empty
  }

let get_table db (Table_id tid) =
  match Id.Map.find_opt tid.id db.tables with
  | None -> create_table ~arity:tid.arity
  | Some table -> table

let set_table db (Table_id tid) table =
  { db with tables = Id.Map.add tid.id table db.tables }

let add_fact db (Fact (tid, args)) =
  let table = get_table db tid in
  let table' = add_fact table args in
  if table' == table then db else set_table db tid table'

let find_index permutation table =
  match permutation with
  | Identity -> Some table.primary
  | Permutation _ -> Permap.find_opt permutation table.indices

let build_index table perm = build_index ~arity:table.arity table.facts perm

let bind_index_iterator ((Table_id tid as table_id), permutation, iter) db =
  let table = get_table db table_id in
  match find_index permutation table with
  | None ->
    if true
    then (
      Format.eprintf "Could not find index on table: %d for: %a@." tid.id
        Permutation.print permutation;
      assert false)
    else
      let index = build_index table permutation in
      iter := Trie.iterator index
  | Some index -> iter := Trie.iterator index

let register_index table permutation =
  match permutation with
  | Identity -> table
  | Permutation _ -> (
    match Permap.find_opt permutation table.indices with
    | None ->
      let index = build_index table permutation in
      { table with indices = Permap.add permutation index table.indices }
    | Some _ -> table)

let register_index db tid permutation =
  let table = get_table db tid in
  let table = register_index table permutation in
  set_table db tid table

let rec loop ~max_depth levels depth tuple =
  match Joined_iterator.current levels with
  | Leapfrog.At_start -> assert false
  | Leapfrog.Key current_key ->
    if depth < Array.length tuple then tuple.(depth) <- current_key;
    if depth = max_depth
    then
      let rec moveup depth =
        if depth = Array.length tuple - 1
        then depth
        else (
          Joined_iterator.up levels;
          moveup (depth - 1))
      in
      moveup depth
    else (
      Joined_iterator.down levels;
      loop ~max_depth levels (depth + 1) tuple)
  | Leapfrog.At_end ->
    Joined_iterator.up levels;
    if depth <= 0
    then -1
    else (
      Joined_iterator.advance levels;
      loop ~max_depth levels (depth - 1) tuple)

let build_projection varmap args =
  Array.map
    (fun term ->
      match term with
      | Variable var -> (
        match Hashtbl.find_opt varmap var with
        | Some index -> Evar index
        | None -> invalid_arg "unbound var")
      | Symbol s -> Esym s)
    args

let build_permutation ?(inverse = false) ~scratch varmap args =
  Array.fill scratch 0 (Array.length scratch) (-1);
  Array.iteri
    (fun pos term ->
      match term with
      | Variable var -> (
        match Hashtbl.find_opt varmap var with
        | Some index ->
          if scratch.(index) <> -1 then invalid_arg "duplicate var in rel";
          scratch.(index) <- pos
        | None -> invalid_arg "unbound var")
      | Symbol _ -> invalid_arg "symbols not supported in queries yet")
    args;
  let permutation = Array.make (Array.length args) (-1) in
  let index = ref 0 in
  for i = 0 to Array.length scratch - 1 do
    if scratch.(i) <> -1
    then (
      if inverse
      then permutation.(scratch.(i)) <- !index
      else permutation.(!index) <- scratch.(i);
      incr index)
  done;
  Permutation.create permutation

let create_varmap ?(existentials = [||]) variables =
  let varmap = Hashtbl.create 17 in
  Array.iteri
    (fun index var ->
      if Hashtbl.mem varmap var then invalid_arg "create_varmap";
      Hashtbl.replace varmap var index)
    variables;
  let nvars = Array.length variables in
  Array.iteri
    (fun index var ->
      if Hashtbl.mem varmap var then invalid_arg "create_varmap";
      Hashtbl.replace varmap var (nvars + index))
    existentials;
  varmap, nvars + Array.length existentials

let create_query ~variables ?existentials hyps : query =
  let varmap, nvars = create_varmap ?existentials variables in
  let scratch = Array.make nvars (-1) in
  let levels = Array.make nvars [] in
  let all_iterators =
    Array.map
      (fun (Atom (tid, args)) ->
        let permutation = build_permutation ~scratch varmap args in
        let iter = Trie.Iterator.I.create () in
        let iterator = tid, permutation, iter in
        Array.iteri
          (fun i v -> if v <> -1 then levels.(i) <- iter :: levels.(i))
          scratch;
        iterator)
      hyps
  in
  let tuple = Array.make (Array.length variables) 0 in
  let levels =
    Joined_iterator.triejoin
    @@ Array.map
         (fun l ->
           match l with
           | [] -> invalid_arg "create_query"
           | _ -> Joined_iterator.join_array (Array.of_list l))
         levels
  in
  Query
    { indices = all_iterators;
      iterator = levels;
      depth = -1;
      output = tuple;
      max_depth = nvars - 1
    }

let bind_query db
    (Query ({ indices; iterator; depth = _; max_depth; output } as q)) =
  (* tuple has size nvars *)
  Array.iter (fun iterator -> bind_index_iterator iterator db) indices;
  Joined_iterator.reset iterator;
  Joined_iterator.down iterator;
  q.depth <- loop ~max_depth iterator 0 output

let query_current (Query { depth; output; _ }) =
  if depth < 0 then None else Some output

let query_advance (Query ({ iterator; depth; output; max_depth; _ } as q)) =
  if depth >= 0
  then (
    Joined_iterator.advance iterator;
    q.depth <- loop ~max_depth iterator depth output)

type relation = table_id

let create_relation = create_table_id

let create_symbol n = n

let create_variable =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    !cnt

type tuple = int array

let tuple_arity = Array.length

let tuple_get = Array.get

type action =
  | Add_atom of table_id * term array
  | Many of action list

let add_atom (Atom (r, args)) = Add_atom (r, args)

let action_sequence actions = Many actions

let rec compile_action varmap action =
  match action with
  | Add_atom (tid, args) -> Add (tid, build_projection varmap args)
  | Many actions -> Sequence (List.map (compile_action varmap) actions)

let create_rule ~variables action ?existentials hyps : rule =
  let query = create_query ~variables ?existentials hyps in
  (* Existential variables cannot be used in actions. *)
  let varmap, _ = create_varmap variables in
  Rule (query, compile_action varmap action)

let create () = empty_db

let rec apply_action db action tuple =
  match action with
  | Add (tid, projection) ->
    let args = Projection.apply projection tuple in
    let fact = Fact (tid, args) in
    add_fact db fact
  | Sequence instructions ->
    List.fold_left
      (fun db instruction -> apply_action db instruction tuple)
      db instructions

let rec saturate_naive db0 =
  let did_change = ref false in
  let db =
    List.fold_left
      (fun db (Rule (query, action)) ->
        bind_query db0 query;
        let rec loop db =
          match query_current query with
          | None -> db
          | Some tuple ->
            let db' = apply_action db action tuple in
            if db' != db then did_change := true;
            query_advance query;
            loop db'
        in
        loop db)
      db0 db0.rules
  in
  if !did_change then saturate_naive db else db

let rec saturate_seminaive db0 db1 =
  let did_change = ref false in
  let current_scope = current_level db0 in
  let db =
    List.fold_left
      (fun db (Rule (query, action)) ->
        let (Query ({ indices; iterator; depth = _; max_depth; output } as q)) =
          query
        in
        let rec loop0 db delta_index =
          if delta_index < 0
          then db
          else (
            Array.iteri
              (fun index iterator ->
                if index = delta_index
                then bind_index_iterator iterator db1
                else bind_index_iterator iterator db0)
              indices;
            Joined_iterator.reset iterator;
            Joined_iterator.down iterator;
            q.depth <- loop ~max_depth iterator 0 output;
            let rec loop1 db =
              match query_current query with
              | None -> db
              | Some tuple ->
                let db' = apply_action db action tuple in
                if db' != db then did_change := true;
                query_advance query;
                loop1 db'
            in
            loop0 (loop1 db) (delta_index - 1))
        in
        loop0 db (Array.length indices - 1))
      db0 db0.rules
  in
  if !did_change
  then saturate_seminaive db (cut_level db current_scope)
  else
    let db' = cut_level db current_scope in
    assert (
      Id.Map.for_all (fun _ table -> Id.Map.is_empty table.facts) db'.tables);
    db

let saturate db =
  let db1 = cut_level db db.last_propagation in
  let db' = saturate_seminaive db db1 in
  assert (db'.current_level = db.current_level);
  { db' with last_propagation = current_level db' }

let add_rule db rule = { db with rules = rule :: db.rules }

let () =
  if false
  then (
    let db = empty_db in
    let p = create_table_id ~arity:2 in
    let q = create_table_id ~arity:2 in
    let r = create_table_id ~arity:3 in
    let s = create_table_id ~arity:2 in
    (* Register indices *)
    let db = register_index db p (Permutation.create [| 1; 0 |]) in
    let db = register_index db q (Permutation.create [| 1; 0 |]) in
    let db = register_index db r (Permutation.create [| 2; 1; 0 |]) in
    let db = register_index db r (Permutation.create [| 0; 2; 1 |]) in
    (* p *)
    let db = add_fact db (Fact (p, [| 0; 1 |])) in
    let db = add_fact db (Fact (p, [| 1; 0 |])) in
    let db = add_fact db (Fact (p, [| 2; 1 |])) in
    let db = add_fact db (Fact (p, [| 7; 3 |])) in
    let db = add_fact db (Fact (p, [| 1; 7 |])) in
    (* q *)
    let db = add_fact db (Fact (q, [| 1; 2 |])) in
    let db = add_fact db (Fact (q, [| 3; 1 |])) in
    (* r *)
    let db = add_fact db (Fact (r, [| 1; 3; 0 |])) in
    let db = add_fact db (Fact (r, [| 7; 12; 1 |])) in
    let x = create_variable () in
    let y = create_variable () in
    let z = create_variable () in
    let rule =
      create_rule ~variables:[| z; y; x |]
        (add_atom (create_atom r [| Variable x; Symbol 42; Variable z |]))
        [| Atom (p, [| Variable x; Variable y |]);
           Atom (q, [| Variable y; Variable z |])
        |]
    in
    let db = add_rule db rule in
    let rule =
      create_rule ~variables:[| x; y |] ~existentials:[| z |]
        (add_atom (create_atom p [| Variable x; Variable y |]))
        [| Atom (r, [| Variable x; Variable z; Variable y |]) |]
    in
    let db = add_rule db rule in
    let rule =
      create_rule ~variables:[| x; y |]
        (add_atom (create_atom s [| Variable x; Variable y |]))
        [| create_atom p [| Variable x; Variable y |];
           create_atom p [| Variable y; Variable x |]
        |]
    in
    let db = add_rule db rule in
    Format.eprintf "@[<v>Before:@ %a@]@." print_database db;
    let db = saturate_naive db in
    let db = add_fact db (Fact (p, [| 57; 57 |])) in
    Format.eprintf "doit again@.";
    let db = saturate_naive db in
    Format.eprintf "@[<v>After:@ %a@]@." print_database db)

let create_rule ~variables atom ?existentials hyps =
  create_rule ~variables (add_atom atom) ?existentials hyps
