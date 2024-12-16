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

  let rec remove inputs t =
    match inputs, t with
    | _, Absent | [], Present _ -> Absent
    | [], Map _ | _ :: _, Present _ -> invalid_arg "Trie.remove"
    | first_input :: other_inputs, Map m -> (
      match Id.Map.find_opt first_input m with
      | None -> t
      | Some subtrie ->
        let subtrie' = remove other_inputs subtrie in
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

type table_id =
  | Table_id of
      { id : int;
        arity : int;
        name : string;
        print : Format.formatter -> int array -> unit
      }

let default_print_tuple ppf arr =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
    Format.pp_print_int ppf (Array.to_list arr)

let create_table_id =
  let cnt = ref 0 in
  fun ~arity ?(print = default_print_tuple) name ->
    incr cnt;
    Table_id { id = !cnt; arity; print; name }

let print_table_id ppf (Table_id tid) = Format.fprintf ppf "%s" tid.name

let print_relation pp_arg ppf (Table_id tid, args) =
  Format.fprintf ppf "@[<hov>(%s@ %a)@]" tid.name
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
       (fun ppf arg -> Format.fprintf ppf "@[%a@]" pp_arg arg))
    args

type variable = string

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

let print_fact ppf (table_id, args) =
  let (Table_id { print; _ }) = table_id in
  Format.fprintf ppf "@[<hov>%a(@[<hov>%a@]).@]" print_table_id table_id print
    args

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

  let inverse p =
    match p with
    | Identity -> Identity
    | Permutation sigma ->
      let inv = Array.make (Array.length sigma) (-1) in
      Array.iteri (fun i j -> inv.(j) <- i) sigma;
      Permutation inv

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

  let get p i = match p with Identity -> i | Permutation sigma -> sigma.(i)
end

type expr =
  | Evar of int
  | Esym of symbol

let print_expr print_var ppf e =
  match e with Evar i -> print_var ppf i | Esym _ -> assert false

type projection = expr array

module Projection = struct
  let apply sigma a =
    Array.map (fun s -> match s with Evar n -> a.(n) | Esym s -> s) sigma

  let get sigma i = sigma.(i)
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
    indices : index Permap.t;
    table_id : table_id
  }

let print_table ppf table =
  Id.Map.iter
    (fun _ syms ->
      Format.fprintf ppf "@[<hov>%a@]@ " print_fact (table.table_id, syms))
    table.facts

let create_table ~arity table_id =
  { facts = Id.Map.empty;
    last_fact_id = 0;
    primary = Trie.create ~arity;
    arity;
    indices = Permap.empty;
    table_id
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

let find_fact table args =
  let args_list = Array.to_list args in
  Trie.find_opt table.primary args_list

let remove_fact table args =
  let args_list = Array.to_list args in
  match Trie.find_opt table.primary args_list with
  | None -> table
  | Some fact_id ->
    let primary = Trie.remove args_list table.primary in
    let facts = Id.Map.remove fact_id table.facts in
    let indices =
      Permap.mapi
        (fun perm index ->
          Trie.remove (Array.to_list @@ Permutation.apply perm args) index)
        table.indices
    in
    { arity = table.arity;
      facts;
      last_fact_id = table.last_fact_id;
      primary;
      indices;
      table_id = table.table_id
    }

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
    { arity = table.arity;
      facts;
      last_fact_id;
      primary;
      indices;
      table_id = table.table_id
    }

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
        table.indices;
    table_id = table.table_id
  }

type 'a state =
  { levels : 'a Joined_iterator.triejoin;
    mutable depth : int
  }

type outcome =
  | Accept  (** Accept and output the current tuple. *)
  | Down
      (** Accept the current prefix, look for the a binding at the next level. *)
  | Skip  (** Skip the current prefix. *)

type _ action =
  | Const : 'a -> 'a action  (** Return the provided value. *)
  | Set_field : int array * int -> unit action
      (** [Set_field out i] sets the field [out.(i)] to the current key. *)
  | Moveto : int -> unit action
      (** [Moveto depth] moves up to depth [depth]. *)
  | Then : unit action * 'a action -> 'a action
  | And : outcome action * outcome action -> outcome action
      (** [Then] performs actions in sequence. *)
  | Mem_fact : table_id * expr array * int array -> bool action
  | Ite : bool action * 'a action * 'a action -> 'a action

(* ite (test tbl proj tup) advance accept *)

type query =
  | Query :
      { indices :
          (table_id * permutation * projection * int Trie.iterator ref) array;
        state : 'a state;
        output : int array;
        variables : variable array;
        existentials : variable array;
        actions : outcome action array;
        hyps : atom array
      }
      -> query

let table_arity (Table_id tid) = tid.arity

let print_query_var (Query { variables; existentials; _ }) ppf i =
  if i < Array.length variables
  then Format.pp_print_string ppf variables.(i)
  else Format.pp_print_string ppf existentials.(i - Array.length variables)

let print_query pp_var ppf
    (Query
      { indices;
        state = _;
        output = _;
        variables = _;
        existentials = _;
        actions = _;
        hyps = _
      }) =
  let first = ref true in
  Format.fprintf ppf "@[(";
  Array.iter
    (fun (table_id, _, proj, _) ->
      if !first then first := false else Format.fprintf ppf "@ ";
      print_relation pp_var ppf
        ( table_id,
          List.init (table_arity table_id) (fun i -> Projection.get proj i) ))
    indices;
  Format.fprintf ppf ")@]"

type instruction =
  | Add of table_id * expr array
  | Remove of table_id * expr array
  | Sequence of instruction list

let rec print_instruction print_var ppf instruction =
  match instruction with
  | Add (tid, args) ->
    Format.fprintf ppf "@[<hov 0>(add@ ";
    print_relation
      (fun ppf expr ->
        match expr with
        | Evar v -> print_var ppf v
        | Esym s -> Format.pp_print_int ppf s)
      ppf
      (tid, Array.to_list args);
    Format.fprintf ppf ")@]"
  | Remove (tid, args) ->
    Format.fprintf ppf "@[<hov 0>(remove@ ";
    print_relation
      (fun ppf expr ->
        match expr with
        | Evar v -> print_var ppf v
        | Esym s -> Format.pp_print_int ppf s)
      ppf
      (tid, Array.to_list args);
    Format.fprintf ppf ")@]"
  | Sequence instructions ->
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
      (print_instruction print_var)
      ppf instructions

type topaction =
  | Add_atom of table_id * term array
  | Remove_atom of table_id * term array
  | Many of topaction list

type rule = Rule of query * instruction

type ruleset = Ruleset of rule list

let print_ruleset ppf (Ruleset rules) =
  Format.pp_print_list ~pp_sep:Format.pp_print_space
    (fun ppf (Rule (query, instruction)) ->
      let print_var = print_query_var query in
      Format.fprintf ppf "@[<2>(rule @[<hv>";
      print_query (print_expr print_var) ppf query;
      Format.fprintf ppf "@]@ @[%a@])@]"
        (print_instruction print_var)
        instruction)
    ppf rules

type schedule =
  | Saturate of ruleset * int Id.Map.t
  | Sequence of schedule list
  | Fixpoint of schedule

module Schedule = struct
  type t = schedule

  let saturate rules = Saturate (Ruleset rules, Id.Map.empty)

  let list schedule = Sequence schedule

  let fixpoint schedule = Fixpoint schedule
end

let rec print_schedule ppf schedule =
  match schedule with
  | Saturate (ruleset, _) ->
    Format.fprintf ppf "@[<hv 2>(saturate@ %a)@]" print_ruleset ruleset
  | Sequence schedules ->
    Format.fprintf ppf "@[<hv 2>(sequence@ %a)@]"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space print_schedule)
      schedules
  | Fixpoint schedule ->
    Format.fprintf ppf "@[<hv 2>(fixpoint@ %a)@]" print_schedule schedule

type database =
  { tables : table Id.Map.t;
    last_propagation : int Id.Map.t;
    schedule : schedule
  }

let print_database ppf db =
  Format.fprintf ppf "@[<v>";
  Id.Map.iter
    (fun _ table ->
      Format.fprintf ppf "@[<v>%a (%d)@ ==========@ @[<v>%a@]@]@ "
        print_table_id table.table_id
        (Id.Map.cardinal table.facts)
        print_table table)
    db.tables;
  Format.fprintf ppf "@ Rules@ =====@ ";
  print_schedule ppf db.schedule;
  Format.fprintf ppf "@]"

let filter_database f db =
  { tables = Id.Map.filter (fun _ table -> f table.table_id) db.tables;
    last_propagation = Id.Map.empty;
    schedule = db.schedule
  }

let current_level db = Id.Map.map (fun table -> table.last_fact_id) db.tables

let cut_level db level =
  let tables =
    Id.Map.mapi
      (fun tid table ->
        match Id.Map.find_opt tid level with
        | Some cut_after -> cut_table table ~cut_after
        | None -> table)
      db.tables
  in
  { tables; schedule = db.schedule; last_propagation = Id.Map.empty }

let empty_db =
  { tables = Id.Map.empty;
    schedule = Sequence [];
    last_propagation = Id.Map.empty
  }

let get_table db (Table_id tid as ttid) =
  match Id.Map.find_opt tid.id db.tables with
  | None -> create_table ~arity:tid.arity ttid
  | Some table -> table

let set_table db (Table_id tid) table =
  { db with tables = Id.Map.add tid.id table db.tables }

let find_fact db (Fact (tid, args)) = find_fact (get_table db tid) args

let add_fact db (Fact (tid, args)) =
  let table = get_table db tid in
  let table' = add_fact table args in
  if table' == table then db else set_table db tid table'

let remove_fact db (Fact (tid, args)) =
  let table = get_table db tid in
  let table' = remove_fact table args in
  if table' == table then db else set_table db tid table'

let find_index permutation table =
  match permutation with
  | Identity -> Some table.primary
  | Permutation _ -> Permap.find_opt permutation table.indices

let build_index table perm = build_index ~arity:table.arity table.facts perm

let bind_index_iterator (table_id, permutation, _, iter) db =
  let table = get_table db table_id in
  match find_index permutation table with
  | None ->
    if true
    then (
      Format.eprintf "Could not find index on table: %a for: %a@."
        print_table_id table_id Permutation.print permutation;
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

let movedown (st : _ state) =
  Joined_iterator.down st.levels;
  st.depth <- st.depth + 1

let moveup (st : _ state) =
  Joined_iterator.up st.levels;
  st.depth <- st.depth - 1

let rec run_action : type a. _ -> _ -> _ -> a action -> a =
 fun db st key action ->
  match action with
  | Const c -> c
  | Set_field (tuple, field) -> tuple.(field) <- key
  | Mem_fact (tid, projection, tuple) ->
    let args = Projection.apply projection tuple in
    Option.is_some (find_fact db (Fact (tid, args)))
  | Moveto depth ->
    while st.depth > depth do
      moveup st
    done
  | Then (lhs, rhs) ->
    run_action db st key lhs;
    run_action db st key rhs
  | Ite (c, t, e) ->
    if run_action db st key c
    then run_action db st key t
    else run_action db st key e
  | And (a1, a2) -> (
    match run_action db st key a1 with
    | Skip -> Skip
    | (Accept | Down) as out -> (
      match run_action db st key a2 with
      | Skip -> Skip
      | Accept -> out
      | Down -> assert false))

let rec loop db (st : _ state) actions =
  match Joined_iterator.current st.levels with
  | Leapfrog.At_start -> assert false
  | Leapfrog.Key current_key -> (
    match run_action db st current_key actions.(st.depth) with
    | Accept -> ()
    | Down ->
      movedown st;
      loop db st actions
    | Skip ->
      Joined_iterator.advance st.levels;
      loop db st actions)
  | Leapfrog.At_end ->
    moveup st;
    if st.depth >= 0
    then (
      Joined_iterator.advance st.levels;
      loop db st actions)

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

let create_query ~variables ?(existentials = [||]) ?(negate = [||]) hyps : query
    =
  let varmap, nvars = create_varmap ~existentials variables in
  let scratch = Array.make nvars (-1) in
  let levels = Array.make nvars [] in
  let all_iterators =
    Array.map
      (fun (Atom (tid, args)) ->
        let permutation = build_permutation ~scratch varmap args in
        let projection = build_projection varmap args in
        let iter = Trie.Iterator.I.create () in
        let iterator = tid, permutation, projection, iter in
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
  let output_size = Array.length tuple in
  let actions =
    Array.init nvars (fun i ->
        let action =
          if i = nvars - 1
          then Then (Moveto (output_size - 1), Const Accept)
          else Const Down
        in
        if i < output_size then Then (Set_field (tuple, i), action) else action)
  in
  (* Add negation checks *)
  Array.iter
    (fun (Atom (tid, args)) ->
      (* XXX: this could use existential variables, which are not actually
         available in the tuple. *)
      let projection = build_projection varmap args in
      let max_var =
        Array.fold_left
          (fun max_var expr ->
            match expr with
            | Esym _ -> max_var
            | Evar n -> (
              assert (n <= Array.length variables);
              match max_var with None -> Some n | Some m -> Some (max n m)))
          None projection
      in
      match max_var with
      | None -> invalid_arg "negation with no variables"
      | Some max_var ->
        actions.(max_var)
          <- And
               ( actions.(max_var),
                 Ite
                   (Mem_fact (tid, projection, tuple), Const Skip, Const Accept)
               ))
    negate;
  let state = { levels; depth = -1 } in
  Query
    { indices = all_iterators;
      state;
      output = tuple;
      variables;
      existentials;
      actions;
      hyps
    }

let bind_query db (Query { indices; state; actions; _ }) =
  Array.iter (fun iterator -> bind_index_iterator iterator db) indices;
  Joined_iterator.reset state.levels;
  Joined_iterator.down state.levels;
  state.depth <- 0;
  loop db state actions

let query_current (Query { state; output; _ }) =
  if state.depth < 0 then None else Some output

let query_advance db (Query { state; actions; _ }) =
  if state.depth >= 0
  then (
    Joined_iterator.advance state.levels;
    loop db state actions)

type relation = table_id

let create_relation = create_table_id

let create_symbol n = n

type tuple = int array

let tuple_arity = Array.length

let tuple_get = Array.get

let add_atom (Atom (r, args)) = Add_atom (r, args)

let remove_atom (Atom (r, args)) = Remove_atom (r, args)

let action_sequence actions = Many actions

let rec compile_action varmap action : instruction =
  match action with
  | Add_atom (tid, args) -> Add (tid, build_projection varmap args)
  | Remove_atom (tid, args) -> Remove (tid, build_projection varmap args)
  | Many actions -> Sequence (List.map (compile_action varmap) actions)

let create_rule ~variables action ?existentials ?negate hyps : rule =
  let query = create_query ~variables ?existentials ?negate hyps in
  (* Existential variables cannot be used in actions. *)
  let varmap, _ = create_varmap variables in
  Rule (query, compile_action varmap action)

let create () = empty_db

let rec apply_action db (action : instruction) tuple =
  match action with
  | Add (tid, projection) ->
    let args = Projection.apply projection tuple in
    let fact = Fact (tid, args) in
    add_fact db fact
  | Remove (tid, projection) ->
    let args = Projection.apply projection tuple in
    let fact = Fact (tid, args) in
    remove_fact db fact
  | Sequence instructions ->
    List.fold_left
      (fun db instruction -> apply_action db instruction tuple)
      db instructions

let run_ruleset (Ruleset rules) db0 =
  List.fold_left
    (fun db (Rule (query, action)) ->
      bind_query db0 query;
      let rec loop db =
        match query_current query with
        | None -> db
        | Some tuple ->
          let db' = apply_action db action tuple in
          query_advance db0 query;
          loop db'
      in
      loop db)
    db0 rules

let rec saturate_naive_ruleset (Ruleset rules) db0 =
  let db' = run_ruleset (Ruleset rules) db0 in
  let did_change = db' != db0 in
  if did_change then saturate_naive_ruleset (Ruleset rules) db' else db'

let rec saturate_seminaive_ruleset ruleset db0 db1 =
  let (Ruleset rules) = ruleset in
  let current_scope = current_level db0 in
  let db =
    List.fold_left
      (fun db (Rule (query, action)) ->
        let (Query { indices; state; actions; _ }) = query in
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
            Joined_iterator.reset state.levels;
            Joined_iterator.down state.levels;
            state.depth <- 0;
            loop db0 state actions;
            let rec loop1 db =
              match query_current query with
              | None -> db
              | Some tuple ->
                let db' = apply_action db action tuple in
                query_advance db0 query;
                loop1 db'
            in
            loop0 (loop1 db) (delta_index - 1))
        in
        loop0 db (Array.length indices - 1))
      db0 rules
  in
  let did_change = db != db0 in
  if did_change
  then saturate_seminaive_ruleset ruleset db (cut_level db current_scope)
  else db

let rec run_schedule db schedule =
  match schedule with
  | Saturate (ruleset, last_propagation) ->
    let db, last_propagation =
      if Id.Map.is_empty last_propagation
      then run_ruleset ruleset db, current_level db
      else db, last_propagation
    in
    let db1 = cut_level db last_propagation in
    let db' = saturate_seminaive_ruleset ruleset db db1 in
    db', Saturate (ruleset, current_level db')
  | Sequence schedules ->
    let db, schedules = List.fold_left_map run_schedule db schedules in
    db, Sequence schedules
  | Fixpoint schedule ->
    let db', schedule' = run_schedule db schedule in
    if db == db'
    then db', Fixpoint schedule'
    else run_schedule db' (Fixpoint schedule')

let saturate db =
  let db', schedule' = run_schedule db db.schedule in
  { db' with schedule = schedule' }

let add_rule db rule =
  let schedule =
    match db.schedule with
    | Sequence [] -> Saturate (Ruleset [rule], Id.Map.empty)
    | Sequence _ -> assert false
    | Fixpoint _ -> assert false
    | Saturate (Ruleset ruleset, last) ->
      Saturate (Ruleset (rule :: ruleset), last)
  in
  { db with schedule }

let () =
  if false
  then (
    let db = empty_db in
    let p = create_table_id "p" ~arity:2 in
    let q = create_table_id "q" ~arity:2 in
    let r = create_table_id "r" ~arity:3 in
    let s = create_table_id "s" ~arity:2 in
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
    let x = "x" in
    let y = "y" in
    let z = "z" in
    let rule1 =
      create_rule ~variables:[| z; y; x |]
        (add_atom (create_atom r [| Variable x; Symbol 42; Variable z |]))
        [| Atom (p, [| Variable x; Variable y |]);
           Atom (q, [| Variable y; Variable z |])
        |]
    in
    let rule2 =
      create_rule ~variables:[| x; y |] ~existentials:[| z |]
        (add_atom (create_atom p [| Variable x; Variable y |]))
        [| Atom (r, [| Variable x; Variable z; Variable y |]) |]
    in
    let _rule3 =
      create_rule ~variables:[| x; y |]
        (add_atom (create_atom s [| Variable x; Variable y |]))
        [| create_atom p [| Variable x; Variable y |];
           create_atom p [| Variable y; Variable x |]
        |]
    in
    let _rule4 =
      create_rule ~variables:[| x; y |]
        (remove_atom (create_atom p [| Variable x; Variable y |]))
        [| create_atom s [| Variable x; Variable y |] |]
    in
    let _rule5 =
      create_rule ~variables:[| x; y |]
        (add_atom (create_atom s [| Variable x; Variable y |]))
        ~negate:[| create_atom q [| Variable y; Variable x |] |]
        [| create_atom p [| Variable x; Variable y |] |]
    in
    let schedule =
      let open! Schedule in
      list
        [ fixpoint (list [saturate [rule1; rule2] (* ; saturate ([rule3]) *)]);
          saturate [_rule5] ]
    in
    Format.eprintf "@[<v>Before:@ %a@]@." print_database db;
    let db = { db with schedule } in
    let db, _schedule = run_schedule db schedule in
    (* let db = add_fact db (Fact (p, [| 57; 57 |])) in *)
    Format.eprintf "doit again@.";
    (* let db, _schedule = run_schedule db schedule in *)
    Format.eprintf "@[<v>After:@ %a@]@." print_database db)

let create_deletion_rule ~variables atom ?existentials ?negate hyps =
  create_rule ~variables (remove_atom atom) ?existentials ?negate hyps

let create_rule ~variables atom ?existentials ?negate hyps =
  create_rule ~variables (add_atom atom) ?existentials ?negate hyps

let relation_name (Table_id { name; _ }) = name

let register_index db p perm = register_index db p (Permutation.create perm)

let set_schedule db schedule = { db with schedule }

let mem_fact db fact = Option.is_some (find_fact db fact)

let print_fact ppf (Fact (tid, args)) = print_fact ppf (tid, args)

let table_size db tid = Id.Map.cardinal (get_table db tid).facts
