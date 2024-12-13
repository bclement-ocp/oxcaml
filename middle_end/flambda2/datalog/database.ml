[@@@warning "-32-37-34-60"]

module Id = struct
  module T = struct
    include Table_by_int_id.Id

    let print = Numbers.Int.print
  end

  include T
  module Tree = Patricia_tree.Make (T)
  module Set = Tree.Set
  module Map = Tree.Map
end

module Trie = struct
  type 'a t =
    | Empty
    | Value of 'a
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
        | Empty -> In_level (Id.Map.iterator Id.Map.empty, it)
        | Value _ -> invalid_arg "down"
        | Map m -> In_level (Id.Map.iterator m, it))
      | At_value (_, _) -> invalid_arg "down"
      | In_level (level_it, _) -> (
        match Id.Map.current level_it with
        | None -> In_level (Id.Map.iterator Id.Map.empty, it)
        | Some (_, next_level) -> (
          match next_level with
          | Empty -> In_level (Id.Map.iterator Id.Map.empty, it)
          | Value v -> At_value (v, it)
          | Map m -> In_level (Id.Map.iterator m, it)))

    let up it =
      match it with
      | Top_level _ -> invalid_arg "up"
      | At_value (_, parent) | In_level (_, parent) -> parent

    module I = struct
      type 'a t = 'a iterator ref

      let create () = ref (Top_level Empty)

      let current it = current !it

      let advance it = it := advance !it

      let seek it key = it := seek !it key

      let down it = it := down !it

      let up it = it := up !it
    end
  end

  let empty = Empty

  let is_empty t = match t with Empty -> true | Value _ | Map _ -> false

  let rec singleton inputs output =
    match inputs with
    | [] -> Value output
    | first_input :: other_inputs ->
      Map (Id.Map.singleton first_input (singleton other_inputs output))

  let rec add_or_replace inputs output t =
    match inputs, t with
    | [], (Empty | Value _) -> Value output
    | [], Map _ | _ :: _, Value _ -> invalid_arg "Trie.add"
    | _ :: _, Empty -> singleton inputs output
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> Map (Id.Map.add first_input (singleton other_inputs output) m)
      | Some subtrie ->
        let subtrie' = add_or_replace other_inputs output subtrie in
        Map (Id.Map.add first_input subtrie' m))

  let rec remove t inputs =
    match inputs, t with
    | _, Empty | [], Value _ -> Empty
    | [], Map _ | _ :: _, Value _ -> invalid_arg "Trie.remove"
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> t
      | Some subtrie ->
        let subtrie' = remove subtrie other_inputs in
        if is_empty subtrie'
        then
          let m = Id.Map.remove first_input m in
          if Id.Map.is_empty m then Empty else Map m
        else Map (Id.Map.add first_input subtrie' m))

  let rec find_opt t inputs =
    match inputs, t with
    | _, Empty -> None
    | [], Value output -> Some output
    | [], Map _ | _ :: _, Value _ -> invalid_arg "Trie.find_opt"
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> None
      | Some subtrie -> find_opt subtrie other_inputs)

  let mem t inputs = Option.is_some (find_opt t inputs)
end

type 'a trie =
  | Value of 'a
  | Map of 'a

type table_id = Table_id of int [@@unboxed]

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
    indices : index Permap.t
  }

let empty_table =
  { facts = Id.Map.empty;
    last_fact_id = 0;
    primary = Trie.empty;
    indices = Permap.empty
  }

let build_index facts permutation =
  Id.Map.fold
    (fun fid args index ->
      let args' = Permutation.apply permutation args in
      Trie.add_or_replace (Array.to_list args') fid index)
    facts Trie.empty

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
    { facts; last_fact_id; primary; indices }

let cut_table table ~cut_after =
  let _, _, delta_facts = Id.Map.split cut_after table.facts in
  { facts = delta_facts;
    last_fact_id = table.last_fact_id;
    primary = build_index delta_facts Permutation.Identity;
    indices =
      Permap.mapi (fun perm _ -> build_index delta_facts perm) table.indices
  }

let build_index table perm = build_index table.facts perm

type database =
  { tables : table Id.Map.t;
    levels : int Id.Map.t list;
    current_level : int
  }

let db_increment_level db =
  let prev_level = Id.Map.map (fun table -> table.last_fact_id) db.tables in
  { db with
    levels = prev_level :: db.levels;
    current_level = db.current_level + 1
  }

let cut_db db ~cut_after =
  match List.nth_opt db.levels (db.current_level - cut_after) with
  | None -> db
  | Some level ->
    let tables =
      Id.Map.mapi
        (fun tid table ->
          match Id.Map.find_opt tid level with
          | Some cut_after -> cut_table table ~cut_after
          | None -> table)
        db.tables
    in
    { tables; levels = []; current_level = 0 }

let empty_db = { tables = Id.Map.empty; levels = []; current_level = 0 }

let get_table db (Table_id tid) =
  match Id.Map.find_opt tid db.tables with
  | None -> empty_table
  | Some table -> table

let set_table db (Table_id tid) table =
  { db with tables = Id.Map.add tid table db.tables }

let add_fact db (Fact (tid, args)) =
  let table = get_table db tid in
  set_table db tid (add_fact table args)

let find_index permutation table =
  match permutation with
  | Identity -> Some table.primary
  | Permutation _ -> Permap.find_opt permutation table.indices

let bind_index_iterator (Table_id tid, permutation, iter) db =
  let table = Id.Map.find tid db.tables in
  match find_index permutation table with
  | None ->
    if true
    then (
      Format.eprintf "Could not find index on table: %d for: %a@." tid
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

let rec loop levels depth tuple =
  match Joined_iterator.current levels with
  | Leapfrog.At_start -> assert false
  | Leapfrog.Key current_key ->
    tuple.(depth) <- current_key;
    if depth = Array.length tuple - 1
    then depth
    else (
      Joined_iterator.down levels;
      loop levels (depth + 1) tuple)
  | Leapfrog.At_end ->
    Joined_iterator.up levels;
    if depth <= 0
    then -1
    else (
      Joined_iterator.advance levels;
      loop levels (depth - 1) tuple)

type query =
  (table_id * permutation * int Trie.iterator ref) array
  * int Joined_iterator.triejoin
  * int ref
  * int array

let create_query ~variables ?(existentials = [||]) hyps : query =
  ignore existentials;
  let varmap = Hashtbl.create 17 in
  Array.iteri (fun index var -> Hashtbl.replace varmap var index) variables;
  let scratch = Array.make (Array.length variables) (-1) in
  let levels = Array.make (Array.length variables) [] in
  let all_iterators =
    Array.map
      (fun (Atom (tid, args)) ->
        for i = 0 to Array.length scratch - 1 do
          scratch.(i) <- -1
        done;
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
            permutation.(!index) <- scratch.(i);
            incr index)
        done;
        let iter = Trie.Iterator.I.create () in
        let iterator = tid, Permutation.create permutation, iter in
        Array.iteri
          (fun i v -> if v <> -1 then levels.(i) <- iter :: levels.(i))
          scratch;
        iterator)
      hyps
  in
  let tuple = Array.make (Array.length levels) 0 in
  let levels =
    Joined_iterator.triejoin
    @@ Array.map (fun l -> Joined_iterator.join_array (Array.of_list l)) levels
  in
  all_iterators, levels, ref 0, tuple

let bind_query db (all_iterators, levels, depth, tuple) =
  (* tuple has size nvars *)
  Array.iter (fun iterator -> bind_index_iterator iterator db) all_iterators;
  Joined_iterator.reset levels;
  Joined_iterator.down levels;
  depth := loop levels 0 tuple

let query_current (_, _levels, depth, tuple) =
  if !depth < 0 then None else Some tuple

let query_advance (_, levels, depth, tuple) =
  if !depth >= 0
  then (
    Joined_iterator.advance levels;
    depth := loop levels !depth tuple)

let query_next q =
  match query_current q with
  | Some tuple ->
    query_advance q;
    Some tuple
  | None -> None

let create_table_id =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    !cnt

let () =
  if false
  then (
    let db = empty_db in
    let p = Table_id 0 in
    let q = Table_id 1 in
    let r = Table_id 2 in
    (* Register indices *)
    let db = register_index db p (Permutation.create [| 1; 0 |]) in
    let db = register_index db q (Permutation.create [| 1; 0 |]) in
    let db = register_index db r (Permutation.create [| 2; 1; 0 |]) in
    (* p *)
    let db = add_fact db (Fact (p, [| 0; 1 |])) in
    let db = add_fact db (Fact (p, [| 1; 0 |])) in
    let db = add_fact db (Fact (p, [| 2; 1 |])) in
    let db = add_fact db (Fact (p, [| 1; 3 |])) in
    (* q *)
    let db = add_fact db (Fact (q, [| 1; 0 |])) in
    let db = add_fact db (Fact (q, [| 1; 2 |])) in
    let db = add_fact db (Fact (q, [| 3; 1 |])) in
    (* r *)
    let db = add_fact db (Fact (r, [| 1; 3; 0 |])) in
    let query =
      create_query ~variables:[| -3; -2; -1 |]
        [| Atom (p, [| Variable (-1); Variable (-2) |]);
           Atom (q, [| Variable (-1); Variable (-3) |]);
           Atom (r, [| Variable (-1); Variable (-2); Variable (-3) |])
        |]
    in
    bind_query db query;
    let rec loop () =
      match query_current query with
      | None -> ()
      | Some tuple ->
        Format.eprintf "@[(%a)@]@."
          (Format.pp_print_list ~pp_sep:Format.pp_print_space
             Format.pp_print_int)
          (Array.to_list tuple);
        query_advance query;
        loop ()
    in
    loop ())

type relation = table_id

let create_relation ~arity:_ = Table_id (create_table_id ())

let create_symbol n = n

let create_variable =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    !cnt

type tuple = int array

let tuple_arity = Array.length

let tuple_get = Array.get

type rule = unit

let create_rule ~variables:_ ?existentials:_ _head _hyps : rule = ()

let create () = empty_db

let saturate db = db

let add_rule db () = db
