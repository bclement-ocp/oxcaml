module Timestamp = struct
  (** Timestamps represent instants. *)

  module T = struct
    include Int

    let print = Numeric_types.Int.print

    let hash = Hashtbl.hash
  end

  include T

  type timestamp = t

  module Tree = Patricia_tree.Make (T)
  module Set = Tree.Set
  module Map = Tree.Map
end

module Inputs_map = struct
  type 'a t =
    | Value of 'a
    | Map of 'a t Simple.Map.t

  type 'a apply_result =
    | Abstraction of 'a t Simple.Map.t
    | Application of 'a * Simple.t list

  let rec singleton inputs output =
    match inputs with
    | [] -> Value output
    | first_input :: other_inputs ->
      Map (Simple.Map.singleton first_input (singleton other_inputs output))

  let rec remove t inputs =
    match inputs with
    | [] -> t
    | first_input :: other_inputs -> (
      match t with
      | Value _ -> assert false
      | Map m -> (
        match Simple.Map.find first_input m with
        | exception Not_found -> t
        | next_level ->
          let next_level' = remove next_level other_inputs in
          if next_level' == next_level
          then t
          else Map (Simple.Map.add first_input next_level' m)))

  let rec add' t inputs output =
    match inputs with
    | [] -> (
      match t with
      | Value value -> Value output, Some value
      | Map _ -> assert false)
    | first_input :: other_inputs -> (
      match t with
      | Value _ -> assert false
      | Map m -> (
        match Simple.Map.find first_input m with
        | exception Not_found ->
          ( Map (Simple.Map.add first_input (singleton other_inputs output) m),
            None )
        | next_level ->
          let next_level', eqn = add' next_level other_inputs output in
          if next_level' == next_level
          then t, eqn
          else Map (Simple.Map.add first_input next_level' m), eqn))

  (* Returns a pair [value, remaining_inputs] for under- and
     over-applications. *)
  let rec apply t inputs =
    match inputs with
    | [] -> (
      match t with
      | Value value -> Application (value, [])
      | Map m -> Abstraction m)
    | first_input :: other_inputs -> (
      match t with
      | Value value -> Application (value, inputs)
      | Map map -> apply (Simple.Map.find first_input map) other_inputs)

  let find t inputs =
    match apply t inputs with
    | Application (value, []) -> Some value
    | Application (_, _ :: _) -> Misc.fatal_error "too many arguments provided"
    | Abstraction _ -> Misc.fatal_error "not enough arguments provided"
    | exception Not_found -> None
end

module Tuple = struct
  type 'a t =
    { inputs : Simple.t list;
      output : 'a
    }

  module Id = struct
    module T = struct
      include Int

      let print = Numeric_types.Int.print

      let hash = Hashtbl.hash
    end

    include T

    type id = t

    module Tree = Patricia_tree.Make (T)
    module Set = Tree.Set
    module Map = Tree.Map
  end
end

type 'a meet_return_value =
  | Left_input
  | Right_input
  | Both_inputs
  | New_result of 'a

type uf

type 'a meet_result =
  | Bottom of unit meet_return_value
  | Ok of 'a meet_return_value * uf

module Schema = struct
  type 'a t

  type 'a canonical =
    | Is_canonical
    | Alias_of_canonical of 'a

  let canonicalize_inputs : 'a t -> Simple.t list -> Simple.t list canonical =
    assert false

  let canonicalize_output : 'a t -> 'a -> 'a canonical = assert false

  let meet : 'a t -> 'a -> 'a -> 'a meet_result = assert false
end

module Tabule = struct
  type 'a t =
    { tuples : 'a Tuple.t Tuple.Id.Map.t;
      primary : Tuple.Id.t Inputs_map.t;
      schema : 'a Schema.t;
      stale : Tuple.Id.Set.t;
      last_tuple_id : Tuple.Id.t
    }

  (* XXX: removing a tuple means removing it from the indices also? Or are we
     fine keeping stale tuples around for a bit?

     I think we are ok with keeping stale tuples in the index.

     XXX: Can we delay removing stale tuples? We'd want [filter_fold] to avoid
     rebuilding the maps...

     Also, there is something to be said about reusing tuple IDs. We need to do
     more work for timestamps (to remember which tuples were updated), but less
     work for indices. Actually I think that is good? Maybe? *)

  let rebuild_tuple t uf tid =
    match Tuple.Id.Map.find tid t.tuples with
    | exception Not_found -> (* Tuple is stale *) t, uf
    | tuple -> (
      match Schema.canonicalize_inputs t.schema tuple.Tuple.inputs with
      | Is_canonical -> (
        match Schema.canonicalize_output t.schema tuple.Tuple.output with
        | Is_canonical -> (* Tuple is already canonical *) t, uf
        | Alias_of_canonical canonical_output ->
          (* Record new output *)
          let stale = Tuple.Id.Set.add tid t.stale in
          let last_tuple_id = t.last_tuple_id + 1 in
          let primary, _ =
            Inputs_map.add' t.primary tuple.Tuple.inputs last_tuple_id
          in
          let tuples =
            Tuple.Id.Map.add last_tuple_id
              { tuple with Tuple.output = canonical_output }
              (Tuple.Id.Map.remove tid t.tuples)
          in
          { tuples; primary; schema = t.schema; stale; last_tuple_id }, uf)
      | Alias_of_canonical canonical_inputs -> (
        (* Inputs were canonicalized; remove the old tuple. *)
        let primary = Inputs_map.remove t.primary tuple.Tuple.inputs in
        let tuples = Tuple.Id.Map.remove tid t.tuples in
        let canonical_output =
          match Schema.canonicalize_output t.schema tuple.Tuple.output with
          | Is_canonical -> tuple.Tuple.output
          | Alias_of_canonical canonical_output -> canonical_output
        in
        match Inputs_map.find primary canonical_inputs with
        | exception Not_found ->
          let last_tuple_id = t.last_tuple_id + 1 in
          let primary, _ =
            Inputs_map.add' primary canonical_inputs last_tuple_id
          in
          let tuples =
            Tuple.Id.Map.add last_tuple_id
              { Tuple.inputs = canonical_inputs;
                Tuple.output = canonical_output
              }
              tuples
          in
          ( { primary;
              tuples;
              last_tuple_id;
              schema = t.schema;
              stale = t.stale
            },
            uf )
        | existing_tid -> (
          let existing_tuple =
            try Tuple.Id.Map.find tid t.tuples
            with Not_found -> Misc.fatal_error "canonical tid cannot be stale"
          in
          match Schema.canonicalize_output t.schema existing_tuple.output with
          | Is_canonical -> (
            match
              Schema.meet t.schema existing_tuple.output canonical_output
            with
            | Bottom _ ->
              (* Environment is inconsistent: raise Bottom_result *)
              assert false
            | Ok ((Left_input | Both_inputs), uf) ->
              ( { primary;
                  tuples;
                  last_tuple_id = t.last_tuple_id;
                  schema = t.schema;
                  stale = t.stale
                },
                uf )
            | Ok (((Right_input | New_result _) as nr), uf) ->
              let output =
                match nr with
                | Right_input -> canonical_output
                | New_result output -> output
                | Left_input | Both_inputs -> assert false
              in
              (* Remove existing; replace with output *)
              assert false)
          | Alias_of_canonical existing_canonical_output ->
            (* Need to update *)
            assert false)))
end

module Value = struct
  module T = struct
    include Int

    let print = Numeric_types.Int.print

    let hash = Hashtbl.hash
  end

  include T

  type value = t

  (* XXX: meet, join *)

  module Set = Set.Make (T)
  module Map = Map.Make (T)
end

module Input = struct
  module T = struct
    type t = Value.t list

    let compare = List.compare Value.compare
  end

  include T
  module Set = Set.Make (T)
  module Map = Map.Make (T)
end

module Output = struct
  type t =
    { value : Value.t;
      timestamp : Timestamp.t
    }
end

type fragment = Output.t Input.Map.t

type iterator =
  { key : unit -> (Input.t * Output.t) option;
    advance : unit -> unit;
    seek : Input.t -> unit
  }

let fragment_iterator fragment =
  let entry = ref None in
  let fragment = ref fragment in
  let advance () =
    let current_fragment = !fragment in
    match Input.Map.min_binding_opt current_fragment with
    | None -> entry := None
    | Some (min_input, _) as next_entry ->
      entry := next_entry;
      fragment := Input.Map.remove min_input current_fragment
  in
  let seek inputs =
    let _, output_opt, rest = Input.Map.split inputs !fragment in
    fragment := rest;
    match output_opt with
    | Some output -> entry := Some (inputs, output)
    | None -> advance ()
  in
  advance ();
  let key () = !entry in
  { key; advance; seek }

type table =
  { timestamps : fragment Timestamp.Map.t;
    cache : fragment;
    max_time : Timestamp.t
  }

let add_or_merge ~time t inputs merge =
  assert (time >= t.max_time);
  match Input.Map.find inputs t.cache with
  | { value; timestamp = _ } ->
    let new_value = merge (Some value) in
    if Value.equal new_value value
    then t
    else
      let fragment =
        try Timestamp.Map.find time t.timestamps
        with Not_found -> Input.Map.empty
      in
      let output = { Output.value = new_value; timestamp = time } in
      let fragment = Input.Map.add inputs output fragment in
      let timestamps = Timestamp.Map.add time fragment t.timestamps in
      let cache = Input.Map.add inputs output t.cache in
      { cache; timestamps; max_time = time }
  | exception Not_found ->
    let output = { Output.value = merge None; timestamp = time } in
    let fragment =
      try Timestamp.Map.find time t.timestamps
      with Not_found -> Input.Map.empty
    in
    let fragment = Input.Map.add inputs output fragment in
    { cache = Input.Map.add inputs output t.cache;
      timestamps = Timestamp.Map.add time fragment t.timestamps;
      max_time = time
    }

module type Uf = sig
  type t
end

let remove table inputs =
  match Input.Map.find inputs table.cache with
  | exception Not_found -> table
  | output ->
    let cache = Input.Map.remove inputs table.cache in
    let timestamps =
      Timestamp.Map.update output.timestamp
        (function
          | None -> Misc.fatal_error "error"
          | Some level -> Some (Input.Map.remove inputs level))
        table.timestamps
    in
    { table with cache; timestamps }

type t = { table : table }

let rebuild_one ~time ~deferred t uf inputs output =
  (* XXX: Check for stale!. *)
  let output_changed, value = canonicalize uf output.Output.value in
  let inputs_changed, canon_inputs =
    List.fold_left_map
      (fun modified value ->
        let modified', value = canonicalize uf value in
        modified || modified', value)
      false inputs
  in
  if not (inputs_changed || output_changed)
  then t
  else
    let table = if inputs_changed then remove t.table inputs else t.table in
    let table =
      add_or_merge ~time table canon_inputs (function
        | None -> value
        | Some old_value ->
          let _, old_value = canonicalize uf old_value in
          (* TODO: merge immediately? if so, record it *)
          if not (Value.equal value old_value)
          then deferred := (canon_inputs, old_value, value) :: !deferred;
          old_value)
    in
    { table }

let rebuild_all ~time t uf =
  let cache = t.table.cache in
  let deferred = ref [] in
  let t =
    Input.Map.fold
      (fun inputs output t -> rebuild_one ~time ~deferred t uf inputs output)
      cache t
  in
  t, !deferred
