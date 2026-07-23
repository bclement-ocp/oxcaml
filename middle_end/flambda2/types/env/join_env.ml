(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Basile Clément, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2013--2025 OCamlPro SAS                                    *)
(*   Copyright 2014--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Implement the join of typing envs, or more precisely of typing env levels.

   Most of the code here is actually concerned with the join of *aliases*
   specifically (keeping track of how names change between the different
   environments), and delegates the actual join of types to the
   [Meet_and_n_way_join] module.

   The join involves multiple environments that are known under different names.
   Within this file, we standardise on the following names:

   - The {b source environment} is the initial value (before the join) of the
   environment that we will extend. This is also called the "definition typing
   env" in join_levels.ml; in the context of [Simplify], this is the environment
   we would use to simplify the handler when not doing a join. This is different
   from the "env at fork" in that the source environment is expected to already
   have definitions for the params (and extra params) of the current handler.

   - The {b target environment} is the final value (after the join) of the
   source environment. This is also called the "handler env" in [Simplify]. This
   environment does not exist until the join is completed, but it is still
   helpful to refer to things that will exist there (those either also exist in
   the source environment, or are existential variables added during the join).

   - The {b joined environments} are each of the individual environments that we
   are joining. In the context of [Simplify], these are the environments at each
   use. The joined environments are uniquely identified (within the current
   join) by an {!Index.t}.

   {1:assumptions Assumptions}

   We make the following assumptions on the input environments.

   {2:scope_of_names Scope of variables and symbols}

   We assume that any name (variable or symbol) defined in the source
   environment is also be defined in all the joined environments.

   Any name defined in the source environment is also necessarily defined in the
   target environment by definition.

   {2:lifted_constants Lifted constants}

   We further assume that any symbol defined in one of the joined environments
   is also defined in the source environment (and hence the target environment).
   In the context of [Simplify], this means that we expect lifted constants from
   the joined environments to have already been inserted into the source
   environment with a suitable type.

   In practice, this means that any of the symbols we manipulate can be assumed
   to exist in both the source environment and in the target environemnt (but
   not in the joined environments, as they could be lifted constants from
   another branch).

   {2:coherent_binding_times Coherent binding times}

   We assume that {b the relative order of variables defined in the source
   environment is preserved across all the joined environments}.

   More precisely, if [a] is defined before (resp. strictly before) [b] in the
   source environment, then [a] is also defined before (resp. strictly before)
   [b] in all of the joined environments. In the context of [Simplify], this
   means that the continuation parameters must be added in the same order in the
   handler and at all uses.

   Note that this assumption does not impose any restriction on the relative
   binding times of variables that don't exist in the source environment, even
   if they exist in all the joined environments.

   This assumption is used in [get_possible_canonical_in_source_env] and allows
   an efficient (linear) implementation of this function. *)

module K = Flambda_kind
module TG = Type_grammar
module MTC = More_type_creators
module TE = Typing_env
module ME = Meet_env
module TEE = Typing_env_extension
module TEL = Typing_env_level

module Symbol_projection = struct
  include Symbol_projection
  include Container_types.Make (Symbol_projection)
end

(* {1 Prelude: iterators} *)

(* We start off with some utilities for using leapfrog iterators that will be
   useful to compute intersections below.

   We use a local module to encapsulate the use of imperative iterators. *)

(* CR bclement: These should be in [Flambda_algorithms]. *)

module Iterator_utils : sig
  type ('a, 'b) incremental_join_entry

  val fold_incremental_join_entry :
    f:('a -> 'b -> 'c -> 'c) -> init:'c -> ('a, 'b) incremental_join_entry -> 'c

  type 'a incremental =
    { previous : 'a;
      diff : 'a;
      current : 'a
    }

  type ('a, 'b) folder = { fold : 'c. ('a -> 'b -> 'c -> 'c) -> 'c -> 'c }

  (* Compute an incremental join using the semi-naive algorithm from Datalog.

     Given a set of incremental inputs [Ci = Pi + Δi] (where [Pi], [Δi] and [Ci]
     are the [previous], [diff], and [current] fields of the {!incremental} type
     above, and [+] is [Name.Map.union (fun _ _ v -> Some v)]), fold over the
     entries in [join(C1, ..., Cn)] {b except for those that are also in
     [join(P1, ..., Pn)]}.

     {b Note}: The equality [Ci = Pi + Δi] must be ensured by the caller. *)
  val fold_incremental_join :
    f:(Name.t -> ('a, 'b) incremental_join_entry -> 'c -> 'c) ->
    init:'c ->
    ('a, 'b Name.Map.t incremental) folder ->
    'c
end = struct
  module Name_map_iterator = Leapfrog.Map (Name)
  module Name_map_join_iterator = Leapfrog.Join (Name_map_iterator)

  let create_iterator ~init ~dummy =
    let send_map, recv_map = Channel.create init in
    let send_val, recv_val = Channel.create dummy in
    let iterator = Name_map_iterator.create recv_map send_val in
    send_map, iterator, recv_val

  let naive_iterator ~init ~dummy =
    let _send, iterator, recv = create_iterator ~init ~dummy in
    iterator, recv

  let join_iterators = Name_map_join_iterator.create

  let[@inline] fold_iterator ~f ~init iterator =
    let rec loop iterator acc =
      match Name_map_join_iterator.current iterator with
      | None -> acc
      | Some name ->
        Name_map_join_iterator.accept iterator;
        let acc = (f [@inlined hint]) name acc in
        Name_map_join_iterator.advance iterator;
        loop iterator acc
    in
    Name_map_join_iterator.init iterator;
    loop iterator init

  type ('a, 'b) incremental_join_entry = ('a * 'b Channel.receiver) list

  let fold_incremental_join_entry ~f ~init incremental_join_entry =
    List.fold_left
      (fun acc (index, receiver) -> f index (Channel.recv receiver) acc)
      init incremental_join_entry

  type 'a incremental =
    { previous : 'a;
      diff : 'a;
      current : 'a
    }

  type ('a, 'b) folder = { fold : 'c. ('a -> 'b -> 'c -> 'c) -> 'c -> 'c }

  exception Join_is_empty

  let fold_incremental_join ~f ~init { fold } =
    (* If $Ci = Pi + Δi$ (where $Ci$, $Pi$ and $Δi$ are the [current],
       [previous], and [diff] fields, respectively), then we have:

       $$join(C1, ..., Cn) = join(P1 + Δ1, ..., Pn + Δn)$$

       By multilinearity: *)
    (*
     * join(C1, ..., Cn) =
     *   join(P1, ..., Pn) +
     *   join(Δ1, P2, ..., Pn) +       \
     *   join(C1, Δ2, P3, ..., Pn) +    | n incremental joins
     *   ... +                          |
     *   join(C1, ..., C{n-1}, Δn)     /
     *)
    (* We are interested in computing the join {b incrementally}, so we want to
       ignore the $join(P0, ..., Pn)$ part and only compute the new joined
       equations that involve at least one of the $Δi$.

       This can be done by initializing all join inputs to their previous ($Pi$)
       value, then for each input $i$:

       - Perform a join with $Δi$;

       - Set the input to $Ci$ for the following joins.

       In total, there are $n + 1$ joins, including the join of the previous
       values that we don't want to compute and $n$ incremental joins involving
       one of the $Δi$.

       We can simplify the joins by noticing the following:

       - We can remove any join where $Δi$ is empty

       - Suppose that the first $p$ inputs have an empty $Pi$ (we can always
       sort these first). Then the result of the first $p$ joins is necessarily
       empty, since it involves an empty $Pi$. Note that these are the first $p$
       join {b including the previous join}, so only the first $p - 1$
       incremental joins.

       This means that for any $i$ such that {b either} $Δi$ or $Pi$ is empty,
       the $i$-th input to the [join] is invariant and always equal to $Ci$ (if
       $Pi$ is empty, then all the non-empty joins use either $Ci$ or $Δi$; if
       $Δi$ is empty, then all the non-empty joins use either $Ci$ or $Pi$). For
       these inputs, we can simply initialize the input to $Ci$.

       There is one caveat: usually we are skipping the first join since all
       inputs are equal to their $Pi$ values. But if there is at least one of
       the inputs that has an empty $Pi$ and a non-empty $Δi$, we have already
       skipped this join by initializing that input to $Ci = Δi$ instead, and so
       we must perform join with the initial inputs. *)
    try
      let senders, iterators, receivers, perform_initial_join =
        fold
          (fun index { previous; diff; current }
               (senders, iterators, receivers, perform_initial_join) ->
            let perform_initial_join =
              perform_initial_join
              || (Name.Map.is_empty previous && not (Name.Map.is_empty diff))
            in
            (* CR bclement: we should be able to initialise the iterator with
               this value (see [fold_binary_join]). *)
            match Name.Map.choose_opt current with
            | None -> raise Join_is_empty
            | Some (_, dummy) ->
              if Name.Map.is_empty diff || Name.Map.is_empty previous
              then
                let iterator, receiver = naive_iterator ~init:current ~dummy in
                ( senders,
                  iterator :: iterators,
                  (index, receiver) :: receivers,
                  perform_initial_join )
              else
                let sender, iterator, receiver =
                  create_iterator ~init:previous ~dummy
                in
                ( (sender, diff, current) :: senders,
                  iterator :: iterators,
                  (index, receiver) :: receivers,
                  perform_initial_join ))
          ([], [], [], false)
      in
      let iterator = join_iterators iterators in
      let[@inline] f name acc = f name receivers acc in
      let acc =
        (* If any of the inputs has an empty $Pi$ and a non-empty $Δi$, then the
           initial join is not $join(P1, ..., Pn)$ but a join involving this
           $Δi$ and it must not be skipped. *)
        if perform_initial_join then fold_iterator ~f ~init iterator else init
      in
      List.fold_left
        (fun acc (sender, diff, current) ->
          Channel.send sender diff;
          let acc = fold_iterator ~f ~init:acc iterator in
          Channel.send sender current;
          acc)
        acc senders
    with Join_is_empty -> init
end

open Iterator_utils

(* {1:type_safe_wrappers Type-safe wrappers}

   Since we are dealing with many environments with distinct set of bound names,
   we introduce small wrappers around the [Variable], [Name], [Simple] and
   [Type_grammar] modules depending on the environment they live in. *)

module Index : sig
  include Container_types.S

  (* Fold over the list with a distinct index for each element.

     This is the only way to create [Index.t] values and is called when starting
     a new join. *)
  val fold_list : (t -> 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b
end = struct
  include Numeric_types.Int

  let fold_list f xs init =
    let _, acc =
      List.fold_left
        (fun (index, acc) x -> index + 1, f index x acc)
        (0, init) xs
    in
    acc
end

module Id_in_env (Id : Container_types.S) () : sig
  include
    Container_types.S
      with type t = private Id.t
       and type Set.t = private Id.Set.t
       and type +!'a Map.t = private 'a Id.Map.t

  val create : Id.t -> t

  val create_set : Id.Set.t -> Set.t

  val create_map : 'a Id.Map.t -> 'a Map.t
end = struct
  include Id

  let create thing = thing

  let create_set s = s

  let create_map m = m
end

module Int_ids_in_env () = struct
  module Variable = Id_in_env (Variable) ()
  module Symbol = Id_in_env (Symbol) ()

  module Name : sig
    include module type of Id_in_env (Name) ()

    val var : Variable.t -> t

    val symbol : Symbol.t -> t

    val var_map : 'a Variable.Map.t -> 'a Map.t
  end = struct
    include Id_in_env (Name) ()

    let var (var : Variable.t) : t =
      create (Name.var (var :> Int_ids.Variable.t))

    let symbol (symbol : Symbol.t) =
      create (Name.symbol (symbol :> Int_ids.Symbol.t))

    let var_map (type a) (m : a Variable.Map.t) =
      create_map (Name.var_map (m :> a Int_ids.Variable.Map.t))
  end

  (* CR bclement: In practice, we consider that these must be canonicals in the
     corresponding environment, so this could be renamed to [Canonical] (and
     [Canonical_in_target_env] etc. below) for clarity. *)
  module Simple : sig
    include module type of Id_in_env (Simple) ()

    val const : Reg_width_const.t -> t

    val name : ?coercion:Coercion.t -> Name.t -> t [@@warning "-32"]

    val symbol : ?coercion:Coercion.t -> Symbol.t -> t

    val var : ?coercion:Coercion.t -> Variable.t -> t

    val pattern_match :
      t ->
      name:(Name.t -> coercion:Coercion.t -> 'a) ->
      const:(Reg_width_const.t -> 'a) ->
      'a

    val pattern_match' :
      t ->
      var:(Variable.t -> coercion:Coercion.t -> 'a) ->
      symbol:(Symbol.t -> coercion:Coercion.t -> 'a) ->
      const:(Reg_width_const.t -> 'a) ->
      'a
  end = struct
    include Id_in_env (Simple) ()

    let const const = create (Simple.const const)

    let name ?(coercion = Coercion.id) (name : Name.t) =
      let simple_without_coercion = Simple.name (name :> Int_ids.Name.t) in
      let simple = Simple.with_coercion simple_without_coercion coercion in
      create simple

    let symbol ?coercion symbol = name ?coercion (Name.symbol symbol)

    let var ?coercion var = name ?coercion (Name.var var)

    let[@inline always] pattern_match (t : t) ~name:when_name ~const =
      Simple.pattern_match
        (t :> Simple.t)
        ~name:(fun name ~coercion ->
          (when_name [@inlined hint]) (Name.create name) ~coercion)
        ~const

    let[@inline always] pattern_match' (t : t) ~var:when_var ~symbol:when_symbol
        ~const =
      Simple.pattern_match'
        (t :> Simple.t)
        ~var:(fun var ~coercion ->
          (when_var [@inlined hint]) (Variable.create var) ~coercion)
        ~symbol:(fun symbol ~coercion ->
          (when_symbol [@inlined hint]) (Symbol.create symbol) ~coercion)
        ~const
  end
end

module Int_ids_in_source_env = Int_ids_in_env ()
module Variable_in_source_env = Int_ids_in_source_env.Variable
module Symbol_in_source_env = Int_ids_in_source_env.Symbol
module Simple_in_source_env = Int_ids_in_source_env.Simple

module Int_ids_from_source_env () = struct
  module Int_ids_in_env = Int_ids_in_env ()

  module Variable = struct
    include Int_ids_in_env.Variable

    (* See {!section-scope_of_names} *)
    let from_source_env (var : Variable_in_source_env.t) =
      create (var :> Variable.t)
  end

  module Symbol = Int_ids_in_env.Symbol
  module Name = Int_ids_in_env.Name

  module Simple = struct
    include Int_ids_in_env.Simple

    (* See {!section-scope_of_names} *)
    let from_source_env (simple : Simple_in_source_env.t) =
      create (simple :> Simple.t)
  end
end

module Int_ids_in_target_env = Int_ids_from_source_env ()
module Variable_in_target_env = Int_ids_in_target_env.Variable
module Name_in_target_env = Int_ids_in_target_env.Name
module Simple_in_target_env = Int_ids_in_target_env.Simple
module Int_ids_in_one_joined_env = Int_ids_from_source_env ()
module Variable_in_one_joined_env = Int_ids_in_one_joined_env.Variable

module Symbol_in_one_joined_env = struct
  include Int_ids_in_one_joined_env.Symbol

  (* See {!section-lifted_constants} *)
  let in_source_env symbol =
    Symbol_in_source_env.create (symbol : t :> Symbol.t)
end

module Simple_in_one_joined_env = Int_ids_in_one_joined_env.Simple

(* {1:environments Environments} *)

module Simples_in_joined_envs : sig
  include Container_types.S with type t = Simple_in_one_joined_env.t Index.Map.t

  val choose_a_suitable_name : t -> string
end = struct
  module T0 = struct
    type t = Simple_in_one_joined_env.t Index.Map.t

    let print = Index.Map.print Simple_in_one_joined_env.print

    let hash map =
      Index.Map.fold
        (fun index simple hash ->
          Hashtbl.hash
            (hash, Index.hash index, Simple_in_one_joined_env.hash simple))
        map (Hashtbl.hash 0)

    let equal = Index.Map.equal Simple_in_one_joined_env.equal

    let compare = Index.Map.compare Simple_in_one_joined_env.compare
  end

  include T0
  include Container_types.Make (T0)

  let choose_a_suitable_name t =
    if not (Index.Map.cardinal t > 1)
    then (
      Format.eprintf "choose a suitable name for: %a@." print t;
      assert false);
    let shared_name =
      try
        Index.Map.fold
          (fun _ simple raw_name ->
            Simple.pattern_match' simple
              ~const:(fun _ -> raw_name)
              ~symbol:(fun _ ~coercion:_ -> raw_name)
              ~var:(fun var ~coercion:_ ->
                let var_name = Variable.raw_name var in
                match raw_name with
                | None -> Some var_name
                | Some raw_name when String.equal raw_name var_name ->
                  Some raw_name
                | Some _ -> raise Not_found))
          (t : t :> Simple.t Index.Map.t)
          None
      with Not_found -> None
    in
    match shared_name with
    | Some raw_name -> "j" ^ raw_name
    | None -> "join_var"
end

module Source_env : sig
  type t

  val create : TE.t -> t

  val machine_width : t -> Target_system.Machine_width.t

  val exists_in_source_env : t -> Variable.t -> Variable_in_source_env.t option

  val exists_at_name_mode :
    min_name_mode:Name_mode.t ->
    t ->
    Variable.t ->
    Variable_in_source_env.t option

  type candidate_canonical_in_source_env =
    | No_simples_in_joined_envs  (** The provided set of simples was empty. *)
    | No_canonical_in_source_env
        (** There is no [simple] in the source environment that is equal to this
            specific set of simples in each joined environment. *)
    | Canonical_in_all_joined_envs of Simple_in_one_joined_env.t
        (** This [simple] is canonical in all the joined environments.

            It may or may not be defined in the source environment. *)
    | Latest_bound_source_var of Variable_in_source_env.t * Coercion.t
        (** This variable is the one with the latest binding time amongst the
            variables in joined environments that exist in the source
            environment.

            If there is any simple in the source environment that is equal to
            the provided set of simples in each joined environments, it can only
            be this variable because of our assumption on binding times being
            coherent (see {!section-coherent_binding_times}). *)

  val candidate_canonical_in_source_env :
    t -> Simples_in_joined_envs.t -> candidate_canonical_in_source_env
end = struct
  type t = { source_env : TE.t } [@@unboxed]

  let create source_env = { source_env }

  let machine_width { source_env; _ } = TE.machine_width source_env

  let exists_in_source_env { source_env } var =
    if TE.mem source_env (Name.var var)
    then Some (Variable_in_source_env.create var)
    else None

  let exists_at_name_mode ~min_name_mode { source_env } var =
    if TE.mem ~min_name_mode source_env (Name.var var)
    then Some (Variable_in_source_env.create var)
    else None

  let total_compare_binding_times { source_env } var1 var2 =
    TE.stable_compare_simples source_env
      (Simple.var (var1 : Variable_in_source_env.t :> Variable.t))
      (Simple.var (var2 : Variable_in_source_env.t :> Variable.t))

  type candidate_canonical_in_source_env =
    | No_simples_in_joined_envs
    | No_canonical_in_source_env
    | Canonical_in_all_joined_envs of Simple_in_one_joined_env.t
    | Latest_bound_source_var of Variable_in_source_env.t * Coercion.t

  let candidate_canonical_in_source_env t canonicals_in_joined_envs =
    Index.Map.fold
      (fun _index canonical possible_canonical_in_source_env ->
        let[@inline] pattern_match_local_simple simple ~local_simple ~source_var
            =
          Simple_in_one_joined_env.pattern_match' simple
            ~const:(fun _ -> local_simple simple)
            ~symbol:(fun _ ~coercion:_ -> local_simple simple)
            ~var:(fun var ~coercion ->
              match
                exists_in_source_env t
                  (var : Variable_in_one_joined_env.t :> Variable.t)
              with
              | None -> local_simple simple
              | Some var -> (source_var [@inlined hint]) var ~coercion)
        in
        let maybe_this_source_var () =
          pattern_match_local_simple canonical
            ~local_simple:(fun _ -> No_canonical_in_source_env)
            ~source_var:(fun var ~coercion ->
              Latest_bound_source_var (var, coercion))
        in
        let latest_source_var_with var ~coercion =
          pattern_match_local_simple canonical
            ~local_simple:(fun _ -> Latest_bound_source_var (var, coercion))
            ~source_var:(fun var0 ~coercion:coercion0 ->
              let c = total_compare_binding_times t var var0 in
              if c < 0
              then Latest_bound_source_var (var0, coercion0)
              else (
                if not (c > 0 || Variable_in_source_env.equal var0 var)
                then
                  Misc.fatal_errorf "Non-total extension of binding times order";
                Latest_bound_source_var (var, coercion)))
        in
        match possible_canonical_in_source_env with
        | No_simples_in_joined_envs -> Canonical_in_all_joined_envs canonical
        | No_canonical_in_source_env -> maybe_this_source_var ()
        | Latest_bound_source_var (var, coercion) ->
          latest_source_var_with var ~coercion
        | Canonical_in_all_joined_envs shared_simple ->
          if Simple_in_one_joined_env.equal canonical shared_simple
          then possible_canonical_in_source_env
          else
            pattern_match_local_simple shared_simple
              ~local_simple:(fun _ -> maybe_this_source_var ())
              ~source_var:(fun var ~coercion ->
                latest_source_var_with var ~coercion))
      canonicals_in_joined_envs No_simples_in_joined_envs
end

module Bindings_in_target_env : sig
  (* This module is only concerned with providing a consistent name to represent
     a set of simples in the joined environments.

     Names in the target environment are either names that exist in the source
     environment, or local variables that are created in the target environment
     but do not exist in the source environment.

     We currently maintain two types of relations between names in the joined
     environment and names in the target environment:

     - Imported variables represent a specific variable in all the joined
     environments where it exists.

     - Existentials represent a specific set of simples in the joined
     environments.

     {b Warning}: Each local variable is defined either as an imported variable
     or as an existential, but imported variables and existentials are not
     necessarily represented by local variables in the target environment: there
     might already be a suitable name in the source environment to represent
     this imported variable or existential.

     For instance, consider that we are doing the join of [x: (= a)] in env 0
     and [x: (= b)] in env 1, where [x] exists in the source environment but not
     [a] and [b]. Then we can use [x] to represent [((0 a) (1 b))], we do not
     have to create a local variable. Note that in the case of imported
     variables, this effectively mean that we can rename variables as we import
     them. *)

  type t

  val from_source_env : Source_env.t -> t

  val source_env : t -> Source_env.t

  (* Return the (unique across the whole join) name to be used to represent this
     set of simples in joined environments.

     This is either a name that has been recorded with
     [add_existential_for_these_simples], or an existential local variable
     created to represent it. *)
  val existential_for_these_simples :
    ?existing_var_in_target_env:Variable_in_target_env.t ->
    t ->
    Simples_in_joined_envs.t ->
    K.t ->
    Variable_in_target_env.t * t

  val import_var : t -> Variable_in_one_joined_env.t -> t

  val fold_imported_variables :
    (Variable_in_one_joined_env.t -> K.t -> 'a -> 'a) -> t -> 'a -> 'a

  val fold_created_variables :
    (Variable_in_target_env.t -> K.t -> 'a -> 'a) -> t -> 'a -> 'a
end = struct
  type t =
    { source_env : Source_env.t;
      imported_variables : Variable_in_one_joined_env.Set.t;
      (* Set of variables that have been imported from at least one of the
         joined environments into the target environment. *)
      existential_for_these_simples :
        Variable_in_target_env.t Simples_in_joined_envs.Map.t;
      (* Maps a set of [simples] in joined environments to the (unique across
         the whole join) name used to represent this exact set of simples in the
         target environment. *)
      created_variables : K.t Variable_in_target_env.Map.t
          (* This contains all the existential variables, created during the
             join, that exist in the target environment but not in the source
             environment or in any of the joined environments. *)
    }

  let from_source_env source_env =
    { source_env;
      imported_variables = Variable_in_one_joined_env.Set.empty;
      existential_for_these_simples = Simples_in_joined_envs.Map.empty;
      created_variables = Variable_in_target_env.Map.empty
    }

  let source_env { source_env; _ } = source_env

  let has_existential_for_these_simples t simples =
    Simples_in_joined_envs.Map.find_opt simples t.existential_for_these_simples

  let existential_for_these_simples ?existing_var_in_target_env t simples kind =
    match has_existential_for_these_simples t simples with
    | Some existing_canonical -> existing_canonical, t
    | None ->
      let var, t =
        match existing_var_in_target_env with
        | None ->
          let var =
            let name = Simples_in_joined_envs.choose_a_suitable_name simples in
            Variable_in_target_env.create (Variable.create name kind)
          in
          let created_variables =
            Variable_in_target_env.Map.add var kind t.created_variables
          in
          var, { t with created_variables }
        | Some var -> var, t
      in
      let existential_for_these_simples =
        Simples_in_joined_envs.Map.add simples var
          t.existential_for_these_simples
      in
      var, { t with existential_for_these_simples }

  let import_var t (var : Variable_in_one_joined_env.t) =
    if Variable_in_one_joined_env.Set.mem var t.imported_variables
    then t
    else
      let imported_variables =
        Variable_in_one_joined_env.Set.add var t.imported_variables
      in
      { t with imported_variables }

  let fold_imported_variables f t acc =
    (* CR bclement: iterate in order consistent with the recorded binding
       times. *)
    Variable_in_one_joined_env.Set.fold
      (fun var acc ->
        let kind = Variable.kind (var :> Variable.t) in
        f var kind acc)
      t.imported_variables acc

  let fold_created_variables f t acc =
    (* CR bclement: iterate in order consistent with the recorded binding
       times. *)
    Variable_in_target_env.Map.fold f t.created_variables acc
end

module Joined_envs : sig
  type t

  (* We use an [incremental] type for equations because the join of env
     extensions needs to know about the equations that exist outside of the join
     extension.

     The [previous] field correspond to the equations added at higher scopes
     (one layer of env extensions removed), and is empty for a top-level
     join. *)
  val create : (TE.t * TG.t Name.Map.t incremental) Index.Map.t -> t

  val get_nth_joined_env : t -> Index.t -> TE.t

  val keys : t -> Index.Set.t

  val exists_in_all_joined_envs : t -> _ Index.Map.t -> bool

  val types_for_imported_var :
    t -> Variable_in_one_joined_env.t -> TG.t Index.Map.t

  val types_for_canonicals :
    t -> K.t -> Simples_in_joined_envs.t -> TG.t Index.Map.t

  val equal_in_all_joined_envs :
    t -> Simple_in_one_joined_env.t -> Simples_in_joined_envs.t -> bool

  val get_canonical_simples_ignoring_name_mode :
    t -> (Index.t * Simple.t) list -> Simples_in_joined_envs.t
end = struct
  type t =
    { envs_and_equations : (TE.t * TG.t Name.Map.t incremental) Index.Map.t }
  [@@unboxed]

  let create envs_and_equations = { envs_and_equations }

  let envs_and_equations = function
    | { envs_and_equations } -> envs_and_equations

  let get_nth_joined_env t index =
    match Index.Map.find_opt index (envs_and_equations t) with
    | Some (one_joined_env, _) -> one_joined_env
    | None ->
      Misc.fatal_errorf "Join does not include environment %a" Index.print index

  let keys t = Index.Map.keys (envs_and_equations t)

  let exists_in_all_joined_envs t m =
    Index.Map.subset_domain (envs_and_equations t) m

  let get_canonical_simple_ignoring_name_mode typing_env simple =
    Simple_in_one_joined_env.create
      (TE.get_canonical_simple_ignoring_name_mode typing_env
         (simple : Simple_in_one_joined_env.t :> Simple.t))

  let equal_in_all_joined_envs t simple simples_in_joined_envs =
    Index.Map.for_all
      (fun index canonical ->
        (* Avoid env lookup when not necessary *)
        Simple_in_one_joined_env.equal canonical simple
        || Simple_in_one_joined_env.equal canonical
             (get_canonical_simple_ignoring_name_mode
                (get_nth_joined_env t index)
                simple))
      simples_in_joined_envs

  let types_for_imported_var t var =
    if Flambda_features.check_light_invariants ()
    then
      if
        not
          (Current_unit.is_current
             (Variable.compilation_unit
                (var : Variable_in_one_joined_env.t :> Variable.t)))
      then
        Misc.fatal_errorf
          "Cannot re-define variable %a defined in another compilation unit \
           into the target environment of join"
          Variable.print
          (var : Variable_in_one_joined_env.t :> Variable.t);
    Index.Map.filter_map
      (fun _index (env, _) ->
        let name =
          Name.var (var : Variable_in_one_joined_env.t :> Variable.t)
        in
        if TE.mem env name then Some (TE.find env name None) else None)
      (envs_and_equations t)

  let types_for_canonicals t kind canonicals =
    Index.Map.mapi
      (fun index canonical ->
        Simple_in_one_joined_env.pattern_match canonical
          ~const:(fun const ->
            Expand_head.Expanded_type.(create_const const |> to_type))
          ~name:(fun name ~coercion ->
            let env = get_nth_joined_env t index in
            let ty = TE.find env (name :> Name.t) (Some kind) in
            match TG.get_alias_opt ty with
            | Some _ ->
              Misc.fatal_errorf
                "Canonical name in joined env %a should never have [Equals] \
                 type %a:@\n\n\
                 %a"
                Simple_in_one_joined_env.print canonical TG.print ty TE.print
                env
            | None -> TG.apply_coercion ty coercion))
      canonicals

  let get_canonical_simples_ignoring_name_mode t simples =
    List.fold_left
      (fun acc (index, simple) ->
        let env = get_nth_joined_env t index in
        let canonical =
          Simple_in_one_joined_env.create
            (TE.get_canonical_simple_ignoring_name_mode env simple)
        in
        Index.Map.add index canonical acc)
      Index.Map.empty simples
end

module Aliases_in_target_env = struct
  type t =
    { aliases_of_variables :
        Variable_in_target_env.Set.t Variable_in_target_env.Map.t
    }

  let empty = { aliases_of_variables = Variable_in_target_env.Map.empty }

  let aliases_of_existential_var t var =
    try Variable_in_target_env.Map.find var t.aliases_of_variables
    with Not_found -> Variable_in_target_env.Set.empty

  let add t ~(demoted_variable : Variable_in_target_env.t)
      ~(canonical_element : Variable_in_target_env.t) =
    let aliases_of_canonical_element =
      aliases_of_existential_var t canonical_element
    in
    let aliases_of_existential_var =
      Variable_in_target_env.Set.add demoted_variable
        aliases_of_canonical_element
    in
    let aliases_of_variables =
      Variable_in_target_env.Map.add canonical_element
        aliases_of_existential_var t.aliases_of_variables
    in
    { aliases_of_variables }
end

(** {1 Public interface} *)

type env_id = Index.t

type 'a join_arg = env_id * 'a

type t =
  { joined_envs : Joined_envs.t;
    types_in_target_env : TG.t Name_in_target_env.Map.t;
    types_in_joined_envs : TG.t Index.Map.t Name_in_target_env.Map.t;
    aliases_in_target_env : Aliases_in_target_env.t;
    imported_vars : Variable.Set.t;
    definitions_in_joined_envs :
      (Simples_in_joined_envs.t * K.t) Variable_in_target_env.Map.t;
    bindings : Bindings_in_target_env.t
  }

let new_bindings_for_existentials t ~since =
  Variable_in_target_env.Map.diff_shared
    (fun _ new_defn _old_defn -> Some new_defn)
    t.definitions_in_joined_envs since.definitions_in_joined_envs

let create ~joined_envs ~bindings =
  { joined_envs;
    types_in_target_env = Name_in_target_env.Map.empty;
    types_in_joined_envs = Name_in_target_env.Map.empty;
    aliases_in_target_env = Aliases_in_target_env.empty;
    imported_vars = Variable.Set.empty;
    definitions_in_joined_envs = Variable_in_target_env.Map.empty;
    bindings
  }

type n_way_join_type = t -> TG.t join_arg list -> TG.t Or_unknown.t * t

type canonical_in_target_env =
  | Canonical_in_source_env of Simple_in_source_env.t
  | Import_from_all_joined_envs of Simple_in_one_joined_env.t
  | Existential_for_these_simples of Variable_in_target_env.t * t

let get_canonical_in_target_env env canonicals_in_joined_envs kind =
  let[@local] existential_for_these_simples () =
    let var, bindings =
      Bindings_in_target_env.existential_for_these_simples env.bindings
        canonicals_in_joined_envs kind
    in
    let definitions_in_joined_envs =
      if Variable_in_target_env.Map.mem var env.definitions_in_joined_envs
      then env.definitions_in_joined_envs
      else
        Variable_in_target_env.Map.add var
          (canonicals_in_joined_envs, kind)
          env.definitions_in_joined_envs
    in
    Existential_for_these_simples
      (var, { env with bindings; definitions_in_joined_envs })
  in
  let source_env = Bindings_in_target_env.source_env env.bindings in
  match
    Source_env.candidate_canonical_in_source_env source_env
      canonicals_in_joined_envs
  with
  | No_simples_in_joined_envs | No_canonical_in_source_env ->
    existential_for_these_simples ()
  | Canonical_in_all_joined_envs simple ->
    Simple_in_one_joined_env.pattern_match' simple
      ~const:(fun const ->
        Canonical_in_source_env (Simple_in_source_env.const const))
      ~symbol:(fun symbol ~coercion ->
        Canonical_in_source_env
          (Simple_in_source_env.symbol ~coercion
             (Symbol_in_one_joined_env.in_source_env symbol)))
      ~var:(fun var ~coercion ->
        match
          Source_env.exists_in_source_env source_env
            (var : Variable_in_one_joined_env.t :> Variable.t)
        with
        | Some var ->
          Canonical_in_source_env (Simple_in_source_env.var ~coercion var)
        | None ->
          Import_from_all_joined_envs
            (Simple_in_one_joined_env.var ~coercion var))
  | Latest_bound_source_var (var, coercion) ->
    let latest_simple = Simple_in_source_env.var var ~coercion in
    if
      Joined_envs.equal_in_all_joined_envs env.joined_envs
        (Simple_in_one_joined_env.from_source_env latest_simple)
        canonicals_in_joined_envs
    then Canonical_in_source_env latest_simple
    else existential_for_these_simples ()

let fold_incremental_join ~f ~init equations_to_join =
  fold_incremental_join ~f ~init
    { fold =
        (fun[@inline] f init ->
          Index.Map.fold
            (fun index (env, maps) -> f (index, env) maps)
            equations_to_join init)
    }

(* Wrapper around [fold_incremental_join] so that we only fold over equations
   for names that exist in the source env. *)
let fold_incremental_join_in_source_env equations_to_join ~exists_in_source_env
    ~init ~f =
  fold_incremental_join equations_to_join ~init ~f:(fun name join_entry acc ->
      Name.pattern_match name
        ~var:(fun var ->
          match exists_in_source_env var with
          | None -> acc
          | Some var_in_target_env -> f var_in_target_env join_entry acc)
        ~symbol:(fun _symbol ->
          (* If [name] is that of a lifted constant symbol generated during one
             of the levels, then ignore it. [Simplify_expr] will already have
             made its type suitable for the [source_env] and inserted it into
             that environment.

             This should not be necessary, but if we don't ignore the join of
             types for lifted constants, and one of them happen to be a
             moderately large mutually recursive set of closures, we end up
             computing a potentially very expensive but useless meet of closure
             types (between the type from [make_suitable_for_environment] and
             the one we are computing during the join).

             It's quite brittle to depend on the set of known lifted constants,
             however, so we just never propagate types on symbols for now. This
             is fine, because if [name] is a symbol that is not a lifted
             constant, it was defined before the fork and already has an
             equation in the [source_env]. While it is possible that its type
             could be refined by all of the branches, it is unlikely, so we are
             fine with dropping the equation.

             CR bclement and vlaviron: This is OK (and is already what we were
             doing with the previous join implementation); however, the n-way
             join actually computes the same type as the one from
             [make_suitable_for_environment] -- it would be better to simply
             compute the type of symbols here and drop the call to
             [make_suitable_for_environment] in [lifted_constant_state],
             resolving at the same time the two CRs there. *)
          acc))

let delay_n_way_join_type env name types =
  let types_in_joined_envs =
    Name_in_target_env.Map.add name types env.types_in_joined_envs
  in
  { env with types_in_joined_envs }

let new_delayed_types env ~since =
  Name_in_target_env.Map.diff_shared
    (fun _ new_type _old_type -> Some new_type)
    env.types_in_joined_envs since.types_in_joined_envs

let add_concrete_equation env name ty =
  assert (not (Name_in_target_env.Map.mem name env.types_in_target_env));
  assert (Option.is_none (TG.get_alias_opt ty));
  let types_in_target_env =
    Name_in_target_env.Map.add name ty env.types_in_target_env
  in
  { env with types_in_target_env }

let add_equation env var ty =
  let name = Name_in_target_env.var var in
  assert (not (Name_in_target_env.Map.mem name env.types_in_target_env));
  let types_in_target_env =
    Name_in_target_env.Map.add name ty env.types_in_target_env
  in
  { env with types_in_target_env }

exception No_alias_in_one_joined_env

let rec import_simple_transitive env simple =
  Simple.pattern_match simple
    ~const:(fun _ -> env)
    ~name:(fun name ~coercion:_ -> import_name_transitive env name)

and import_name_transitive env name =
  Name.pattern_match name
    ~symbol:(fun _ -> env)
    ~var:(fun var -> import_var_transitive env var)

and import_var_transitive env var =
  match
    Source_env.exists_in_source_env
      (Bindings_in_target_env.source_env env.bindings)
      var
  with
  | Some _ -> env
  | None ->
    if Variable.Set.mem var env.imported_vars
    then env
    else
      let imported_vars = Variable.Set.add var env.imported_vars in
      let bindings =
        Bindings_in_target_env.import_var env.bindings
          (Variable_in_one_joined_env.create var)
      in
      let env = { env with bindings; imported_vars } in
      let types =
        Joined_envs.types_for_imported_var env.joined_envs
          (Variable_in_one_joined_env.create var)
      in
      import_or_delay_n_way_join_type env
        (Variable_in_target_env.create var)
        types

and import_type_transitive env ty =
  Name_occurrences.fold_variables (TG.free_names ty) ~init:env
    ~f:(fun env var -> import_var_transitive env var)

and add_equals_in_joined_envs env kind var simples =
  match simples with
  | [] -> Misc.fatal_errorf "N-way join of zero simples"
  | (_, simple) :: simples
    when List.for_all (fun (_, simple') -> Simple.equal simple simple') simples
    ->
    let env = add_equation env var (TG.alias_type_of kind simple) in
    import_simple_transitive env simple
  | _ -> (
    let canonicals =
      Joined_envs.get_canonical_simples_ignoring_name_mode env.joined_envs
        simples
    in
    match get_canonical_in_target_env env canonicals kind with
    | Canonical_in_source_env canonical ->
      add_equation env var (TG.alias_type_of kind (canonical :> Simple.t))
    | Import_from_all_joined_envs canonical ->
      let env =
        add_equation env var (TG.alias_type_of kind (canonical :> Simple.t))
      in
      import_simple_transitive env (canonical :> Simple.t)
    | Existential_for_these_simples (existential_var, env) ->
      let aliases_in_target_env =
        Aliases_in_target_env.add env.aliases_in_target_env
          ~demoted_variable:var ~canonical_element:existential_var
      in
      { env with aliases_in_target_env })

and import_or_delay_n_way_join_type env var types =
  match
    Index.Map.fold
      (fun index ty (kind, simples) ->
        match TG.get_alias_opt ty with
        | None -> raise_notrace No_alias_in_one_joined_env
        | Some simple ->
          let kind =
            match kind with
            | None -> TG.kind ty
            | Some kind ->
              if not (K.equal kind (TG.kind ty))
              then
                Misc.fatal_errorf "Incompatible kinds for variable during join";
              kind
          in
          Some kind, (index, simple) :: simples)
      types (None, [])
  with
  | None, _ -> Misc.fatal_error "Unexpected bottom during join"
  | Some kind, simples -> add_equals_in_joined_envs env kind var simples
  | exception No_alias_in_one_joined_env -> (
    match Index.Map.choose types with
    | exception Not_found -> assert false
    | _, ty ->
      if Index.Map.for_all (fun _ ty' -> ty == ty') types
      then
        let env = add_concrete_equation env (Name_in_target_env.var var) ty in
        import_type_transitive env ty
      else delay_n_way_join_type env (Name_in_target_env.var var) types)

(* This function is responsible for splitting the [equations_to_join] between
   those that are demotions in all joined environments, that are replayed in the
   target environment by adding to the bindings, and the rest, that are expanded
   to equations on concrete types that will be joined later.

   Note that we only care about names that have new types in all of the joined
   environments, otherwise the join can never be more precise than what we had
   initially. We also only care about names that exist in the target
   environments; other names will be imported automatically during the join of
   types and only if they are reachable.

   {b Note}: This function is only used during a top-level join. For nested
   joins, it would be incorrect to record aliases into the bindings (since they
   are only valid during the env extension, and the bindings must be valid for
   the whole join); [join_aliases_in_env_extension] is used instead. *)
let join_aliases_into_bindings env equations_to_join =
  fold_incremental_join_in_source_env equations_to_join
    ~exists_in_source_env:
      (Source_env.exists_in_source_env
         (Bindings_in_target_env.source_env env.bindings))
    ~init:env
    ~f:(fun var join_entry env ->
      let types =
        fold_incremental_join_entry join_entry ~init:Index.Map.empty
          ~f:(fun (index, _) ty types -> Index.Map.add index ty types)
      in
      import_or_delay_n_way_join_type env
        (Variable_in_target_env.from_source_env var)
        types)

let rec add_inverse_relation_to_env_extension ?(seen = Name.Set.empty)
    env_extension name relation ~scrutinee =
  let empty_descr : TG.Head_of_kind_naked_immediate.descr =
    { naked_immediates = Unknown; inverse_relations = TG.Relation.Map.empty }
  in
  let[@inline] updated_type_from_descr
      (descr : TG.Head_of_kind_naked_immediate.descr) =
    let inverse_relations =
      TG.Relation.Map.update relation
        (function
          | None -> Some (Name.Set.singleton scrutinee)
          | Some existing_args -> Some (Name.Set.add scrutinee existing_args))
        descr.inverse_relations
    in
    TG.create_from_head_naked_immediate
      (TG.Head_of_kind_naked_immediate.from_descr_non_empty
         { descr with inverse_relations })
  in
  match Name.Map.find_opt name (TEE.to_map env_extension) with
  | None ->
    TEE.add_or_replace_equation env_extension name
      (updated_type_from_descr empty_descr)
  | Some existing_ty -> (
    match TG.descr existing_ty with
    | Naked_immediate Bottom ->
      (* If we already know that we are bottom, we don't need to store anything
         more precise. *)
      env_extension
    | Naked_immediate Unknown ->
      (* This should not happen, as we would usually only only store non-obvious
         types in extensions -- but it's also harmless. *)
      TEE.add_or_replace_equation env_extension name
        (updated_type_from_descr empty_descr)
    | Naked_immediate (Ok (No_alias head)) ->
      (* There is a concrete type for this name in the extension; augment it
         with the reverse relation. *)
      let descr = TG.Head_of_kind_naked_immediate.descr head in
      TEE.add_or_replace_equation env_extension name
        (updated_type_from_descr descr)
    | Naked_immediate (Ok (Equals simple)) ->
      (* Usually we expect that the name we are adding an alias for would be
         canonical in the env extension, but it could (rarely) happen that it is
         not the case. We simply follow the aliases until we either find one
         that has a concrete type in the extension, or until we detect a
         loop. *)
      Simple.pattern_match simple
        ~name:(fun name' ~coercion:_ ->
          if Name.Set.mem name' seen
          then
            (* There is an alias loop in the env extension -- it is fine to
               break the loop to store the non-alias type anywhere, so we might
               as well do it when we detect the loop. *)
            TEE.add_or_replace_equation env_extension name
              (updated_type_from_descr empty_descr)
          else
            add_inverse_relation_to_env_extension ~seen:(Name.Set.add name seen)
              env_extension name' relation ~scrutinee)
        ~const:(fun _ ->
          (* We do not store reverse relations on constants as that would be
             both expensive and of dubious use. *)
          env_extension)
    | Value _ | Naked_float32 _ | Naked_float _ | Naked_int8 _ | Naked_int16 _
    | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _ | Naked_vec128 _
    | Naked_vec256 _ | Naked_vec512 _ | Rec_info _ | Region _ ->
      Misc.fatal_error "Kind mismatch for output of relation: expected %a")

let add_to_inverse_relations inverse_relations name relation ~scrutinee =
  Name.Map.union_total_shared
    (fun _ inv_rels1 inv_rels2 ->
      TG.Relation.Map.union_total_shared
        (fun _ names1 names2 -> Name.Set.union names1 names2)
        inv_rels1 inv_rels2)
    inverse_relations
    (Name.Map.singleton name
       (TG.Relation.Map.singleton relation (Name.Set.singleton scrutinee)))

let recover_inverse_relations ~exists_in_all_joined_envs inverse_relations name
    ty =
  (* We can only recover inverse relations if the type we are recovering from is
     valid in all the joined environments.

     If we have a type [x : Variant (is_int = y)] for [x], but [x] only exists
     in a subset of the joined environments, then the equation [y = %is_int x]
     is only valid in those environments -- in particular, if [y] exists in more
     environments than [x], it is unsound to include that equation in the target
     environment.

     We avoid this situation by only recovering relations if the type we are
     recovering from exists in all the joined environments -- this ensures that
     the variables mentioned in the type cannot exist in more environments than
     the type itself.

     CR-someday bclement: We could be more precise here by recovering relations
     if they are valid in all the environments where the involved variables are
     defined, but it is not clear if that would actually be useful. *)
  assert exists_in_all_joined_envs;
  match TG.descr ty with
  | Value (Ok (No_alias { is_null = Not_null; non_null = Ok head })) -> (
    match head with
    | Variant { immediates = Known imm_ty; get_tag = Some get_tag_var; _ }
      when TG.is_obviously_bottom imm_ty ->
      (* If we have no immediates, we can add the inverse relation on [get_tag]
         at the toplevel. *)
      let inverse_relations =
        add_to_inverse_relations inverse_relations (Name.var get_tag_var)
          TG.Relation.get_tag ~scrutinee:name
      in
      ty, inverse_relations
    | Variant
        { is_int;
          get_tag;
          immediates = (Known _ | Unknown) as immediates;
          blocks;
          extensions;
          is_unique
        } ->
      (* In the general case, we must store the [Get_tag] equation inside the
         "block" env extension. This is because storing a [Get_tag] reverse
         relation on a naked immediate allows us to perform a reduction to learn
         that the target of the relation is a block, which is not valid if it
         could be an immediate. *)
      let inverse_relations =
        match is_int with
        | None -> inverse_relations
        | Some is_int_var ->
          add_to_inverse_relations inverse_relations (Name.var is_int_var)
            TG.Relation.is_int ~scrutinee:name
      in
      let ty =
        match get_tag with
        | None -> ty
        | Some get_tag_var ->
          let when_immediate, when_block =
            match extensions with
            | No_extensions -> TEE.empty, TEE.empty
            | Ext { when_immediate; when_block } -> when_immediate, when_block
          in
          let when_block =
            add_inverse_relation_to_env_extension when_block
              (Name.var get_tag_var) TG.Relation.get_tag ~scrutinee:name
          in
          let head' =
            TG.Head_of_kind_value_non_null.create_variant ~is_unique ~blocks
              ~immediates
              ~extensions:(Ext { when_immediate; when_block })
              ~is_int ~get_tag
          in
          TG.create_from_head_value { is_null = Not_null; non_null = Ok head' }
      in
      ty, inverse_relations
    | Mutable_block _
    | Boxed_float32 (_, _)
    | Boxed_float (_, _)
    | Boxed_int32 (_, _)
    | Boxed_int64 (_, _)
    | Boxed_nativeint (_, _)
    | Boxed_vec128 (_, _)
    | Boxed_vec256 (_, _)
    | Boxed_vec512 (_, _)
    | Closures _ | String _ | Array _ ->
      ty, inverse_relations)
  | Value (Ok (No_alias { is_null = Maybe_null { is_null }; non_null = _ })) ->
    (* CR bclement: if we are possibly null, we can't recover inverse relations
       from the non-null case because we don't have an appropriate env extension
       to place them in.

       We can't store them directly in the env for the same reason we can't do
       it for [Get_tag], see the comment for the [Variant] case. *)
    let inverse_relations =
      match is_null with
      | None -> inverse_relations
      | Some is_null_var ->
        add_to_inverse_relations inverse_relations (Name.var is_null_var)
          TG.Relation.is_null ~scrutinee:name
    in
    ty, inverse_relations
  | Value
      ( Ok
          ( Equals _
          | No_alias { is_null = Not_null; non_null = Unknown | Bottom } )
      | Unknown | Bottom )
  | Naked_immediate _ | Naked_float32 _ | Naked_float _ | Naked_int8 _
  | Naked_int16 _ | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _
  | Naked_vec128 _ | Naked_vec256 _ | Naked_vec512 _ | Rec_info _ | Region _ ->
    ty, inverse_relations

let n_way_join_round ~(n_way_join_type : n_way_join_type) t equations_to_join
    inverse_relations =
  Name_in_target_env.Map.fold
    (fun name types (inverse_relations, t) ->
      if
        Flambda_features.check_light_invariants ()
        && Name_in_target_env.Map.mem name t.types_in_target_env
      then
        Misc.fatal_errorf
          "Processing join of %a but we already have a type for it."
          Name_in_target_env.print name;
      let heads = Index.Map.bindings types in
      match n_way_join_type t heads with
      | Unknown, t -> inverse_relations, t
      | Known ty, t ->
        let exists_in_all_joined_envs =
          Joined_envs.exists_in_all_joined_envs t.joined_envs types
        in
        if Option.is_some (TG.get_alias_opt ty)
        then
          Misc.fatal_errorf
            "Alias before inverse relations: %a@.From join of types:@ %a@."
            TG.print ty (Index.Map.print TG.print) types;
        let ty, inverse_relations =
          if exists_in_all_joined_envs
          then
            recover_inverse_relations ~exists_in_all_joined_envs
              inverse_relations
              (name :> Name.t)
              ty
          else ty, inverse_relations
        in
        if Option.is_some (TG.get_alias_opt ty)
        then
          Misc.fatal_errorf
            "Alias AFTER inverse relations: %a@.From join of types:@ %a@."
            TG.print ty (Index.Map.print TG.print) types;
        let t = add_concrete_equation t name ty in
        inverse_relations, t)
    equations_to_join (inverse_relations, t)

(** {2:n-way-join Cut and n-way join} *)

let n_way_join_symbol_projections t symbol_projections_to_join =
  (* Recall that being a symbol projection is a property of the *variable*
     itself, not of the canonicals -- so we can only propagate a symbol
     projection when the same symbol projection is associated with the same
     variable in all joined environments. *)
  let joined_projections =
    Index.Map.fold
      (fun index symbol_projections acc ->
        Variable_in_one_joined_env.Map.fold
          (fun var symbol_projection symbol_projections_to_join ->
            match
              Source_env.exists_at_name_mode ~min_name_mode:Name_mode.normal
                (Bindings_in_target_env.source_env t.bindings)
                (var :> Variable.t)
            with
            | None -> symbol_projections_to_join
            | Some var ->
              Variable_in_source_env.Map.update var
                (fun joined_projections ->
                  let joined_projections =
                    Option.value joined_projections ~default:Index.Map.empty
                  in
                  Some
                    (Index.Map.add index symbol_projection joined_projections))
                symbol_projections_to_join)
          symbol_projections acc)
      symbol_projections_to_join Variable_in_source_env.Map.empty
  in
  let all_indices = Joined_envs.keys t.joined_envs in
  Variable_in_source_env.Map.fold
    (fun var joined_projections symbol_projections ->
      if not (Index.Set.subset all_indices (Index.Map.keys joined_projections))
      then symbol_projections
      else
        match Index.Map.choose joined_projections with
        | _, unique_projection
          when Index.Map.for_all
                 (fun _ projection ->
                   Symbol_projection.equal projection unique_projection)
                 joined_projections ->
          Variable_in_target_env.Map.add
            (Variable_in_target_env.from_source_env var)
            unique_projection symbol_projections
        | _ | (exception Not_found) ->
          (* This can only happen if:

             - The same variable is bound to different symbol projections in
             different input environments; or

             - We are joining zero environments

             We don't expect either of these to happen, but still return
             [symbol_projections] in this case as it is harmless. *)
          symbol_projections)
    joined_projections Variable_in_target_env.Map.empty

let cut_for_join typing_env ~cut_after =
  let level = TE.cut typing_env ~cut_after in
  let equations = TEL.equations level in
  let incremental_equations =
    { previous = Name.Map.empty; diff = equations; current = equations }
  in
  let symbol_projections =
    Variable_in_one_joined_env.create_map (TEL.symbol_projections level)
  in
  incremental_equations, symbol_projections

let move_equation ~from ~to_ equations =
  assert (not (Name.Map.mem to_ equations));
  match Name.Map.find from equations with
  | exception Not_found -> equations
  | ty ->
    let equations = Name.Map.remove from equations in
    Name.Map.add to_ ty equations

let move_definition ~from ~to_ definitions =
  match Variable_in_target_env.Map.find from definitions with
  | exception Not_found -> definitions
  | defn ->
    let definitions = Variable_in_target_env.Map.remove from definitions in
    Variable_in_target_env.Map.add to_ defn definitions

let alias_equations_for_existential kind ~canonical_element ~demoted_aliases
    equations =
  let ty = TG.alias_type_of kind canonical_element in
  let equations =
    Variable_in_target_env.Set.fold
      (fun alias equations ->
        Name.Map.add (Name.var (alias :> Variable.t)) ty equations)
      demoted_aliases equations
  in
  ty, equations

let define_or_eliminate_variables env source_env inverse_relations
    ~meet_expanded_head =
  let names_in_inverse_relations =
    Name.Map.fold
      (fun name relations names_in_inverse_relations ->
        TG.Relation.Map.fold
          (fun _ names names_in_inverse_relations ->
            Name.Set.union names names_in_inverse_relations)
          relations
          (Name.Set.add name names_in_inverse_relations))
      inverse_relations Name.Set.empty
  in
  let equations = (env.types_in_target_env :> TG.t Name.Map.t) in
  let free_vars_in_equations =
    Name.Map.fold
      (fun _ ty free_names_in_equations ->
        Name_occurrences.with_only_variables (TG.free_names ty)
        |> Name_occurrences.union free_names_in_equations)
      equations Name_occurrences.empty
  in
  let unique_occurence_is_in_equations var =
    (not (Name.Set.mem (Name.var var) names_in_inverse_relations))
    &&
    match Name_occurrences.count_variable free_vars_in_equations var with
    | Zero | One -> true
    | More_than_one -> false
  in
  let target_env =
    Bindings_in_target_env.fold_imported_variables
      (fun var kind target_env ->
        ME.add_variable_definition target_env
          (var :> Variable.t)
          kind Name_mode.in_types)
      env.bindings source_env
  in
  let target_env, to_expand, equations, inverse_relations, definitions =
    Bindings_in_target_env.fold_created_variables
      (fun var kind
           (target_env, to_expand, equations, inverse_relations, definitions) ->
        let aliases_of_var =
          Aliases_in_target_env.aliases_of_existential_var
            env.aliases_in_target_env var
        in
        let erased_var = (var :> Variable.t) in
        match Variable_in_target_env.Set.choose_opt aliases_of_var with
        | None ->
          if unique_occurence_is_in_equations erased_var
          then
            let ty, equations =
              match Name.Map.find (Name.var erased_var) equations with
              | exception Not_found -> MTC.unknown kind, equations
              | ty -> ty, Name.Map.remove (Name.var erased_var) equations
            in
            ( target_env,
              Variable.Map.add erased_var ty to_expand,
              equations,
              inverse_relations,
              Variable_in_target_env.Map.remove var definitions )
          else
            ( ME.add_variable_definition target_env erased_var kind
                Name_mode.in_types,
              to_expand,
              equations,
              inverse_relations,
              definitions )
        | Some alias ->
          let definitions = move_definition definitions ~from:var ~to_:alias in
          let equations =
            move_equation equations ~from:(Name.var erased_var)
              ~to_:(Name.var (alias :> Variable.t))
          in
          let move_inverse_relation ~from ~to_ inverse_relations =
            match Name.Map.find_or_null from inverse_relations with
            | Null -> inverse_relations
            | This relations ->
              let inverse_relations = Name.Map.remove from inverse_relations in
              Name.Map.add to_ relations inverse_relations
          in
          let inverse_relations =
            move_inverse_relation ~from:(Name.var erased_var)
              ~to_:(Name.var (alias :> Variable.t))
              inverse_relations
          in
          let ty, equations =
            alias_equations_for_existential kind equations
              ~canonical_element:(Simple_in_target_env.var alias :> Simple.t)
              ~demoted_aliases:
                (Variable_in_target_env.Set.remove alias aliases_of_var)
          in
          ( target_env,
            Variable.Map.add erased_var ty to_expand,
            equations,
            inverse_relations,
            definitions ))
      env.bindings
      ( target_env,
        Variable.Map.empty,
        equations,
        inverse_relations,
        env.definitions_in_joined_envs )
  in
  let to_project = Variable.Map.keys to_expand in
  let rec expand var =
    match Variable.Map.find var to_expand with
    | exception Not_found -> assert false
    | ty -> (
      match TG.get_alias_opt ty with
      | None -> TG.project_variables_out ~to_project ~expand ty
      | Some simple ->
        Simple.pattern_match' simple
          ~const:(fun _ -> ty)
          ~symbol:(fun _ ~coercion:_ -> ty)
          ~var:(fun var ~coercion ->
            if Variable.Set.mem var to_project
            then TG.apply_coercion (expand var) coercion
            else ty))
  in
  let equations =
    Name.Map.map (TG.project_variables_out ~to_project ~expand) equations
  in
  let equations_for_inverse_relations =
    Name.Map.map
      (fun inverse_relations ->
        TG.Head_of_kind_naked_immediate.create_inverse_relations
          inverse_relations
        |> TG.create_from_head_naked_immediate
        |> TG.project_variables_out ~to_project ~expand)
      inverse_relations
  in
  let target_env =
    ME.add_env_extension ~meet_expanded_head target_env (TEE.from_map equations)
  in
  let target_env =
    ME.add_env_extension ~meet_expanded_head target_env
      (TEE.from_map equations_for_inverse_relations)
  in
  target_env, definitions

let cut_and_n_way_join0 ~n_way_join_type ~meet_expanded_head ~cut_after
    source_env joined_envs equations_to_join symbol_projections_to_join =
  try
    let empty_bindings =
      Bindings_in_target_env.from_source_env
        (Source_env.create (ME.typing_env source_env))
    in
    let joined_envs = Joined_envs.create equations_to_join in
    let empty_env = create ~joined_envs ~bindings:empty_bindings in
    let env = join_aliases_into_bindings empty_env equations_to_join in
    let rec n_way_join_delayed_equations env_this_round inverse_relations
        equations_to_join =
      if Name_in_target_env.Map.is_empty equations_to_join
      then inverse_relations, env_this_round
      else
        let inverse_relations, env_next_round =
          n_way_join_round ~n_way_join_type env_this_round equations_to_join
            inverse_relations
        in
        n_way_join_delayed_equations env_next_round inverse_relations
          (new_delayed_types env_next_round ~since:env_this_round)
    in
    let rec n_way_join_loop ~depth env_this_round inverse_relations
        new_existentials =
      if
        Variable_in_target_env.Map.is_empty new_existentials
        || depth >= Flambda_features.join_depth ()
      then inverse_relations, env_this_round
      else
        let equations_to_join =
          Variable_in_target_env.Map.map
            (fun (simples, kind) ->
              Joined_envs.types_for_canonicals env_this_round.joined_envs kind
                simples)
            new_existentials
        in
        let inverse_relations, env_next_round =
          n_way_join_delayed_equations env_this_round inverse_relations
            (Name_in_target_env.var_map equations_to_join)
        in
        n_way_join_loop ~depth:(depth + 1) env_next_round inverse_relations
          (new_bindings_for_existentials env_next_round ~since:env_this_round)
    in
    (* First, process the equations for names in the source environment and any
       variables reachable from there; then process the existential variables
       created during that process. *)
    let inverse_relations, env =
      n_way_join_delayed_equations env Name.Map.empty
        (new_delayed_types env ~since:empty_env)
    in
    let inverse_relations, env =
      n_way_join_loop ~depth:0 env inverse_relations
        (new_bindings_for_existentials env ~since:empty_env)
    in
    let target_env, definitions =
      define_or_eliminate_variables env source_env inverse_relations
        ~meet_expanded_head
    in
    let target_env =
      Variable_in_target_env.Map.fold
        (fun var symbol_projection target_env ->
          ME.add_symbol_projection target_env
            (var :> Variable.t)
            symbol_projection)
        (n_way_join_symbol_projections env symbol_projections_to_join)
        target_env
    in
    target_env, definitions
  with Misc.Fatal_error ->
    let bt = Printexc.get_raw_backtrace () in
    Format.eprintf "\n@[<v 2>%tContext is:%t cut and join of levels:@ %a@]\n"
      Flambda_colours.error Flambda_colours.pop
      (Index.Map.print (fun ppf env -> TEL.print ppf (TE.cut ~cut_after env)))
      joined_envs;
    Printexc.raise_with_backtrace Misc.Fatal_error bt

(** {2:simplify Interface for simplify} *)

module Analysis = struct
  type 'a t =
    { definitions_in_joined_envs :
        (Simples_in_joined_envs.t * K.t) Variable_in_target_env.Map.t;
      canonical_definitions_at_normal_mode :
        (Simple_in_one_joined_env.t Index.Map.t * K.t)
        Variable_in_target_env.Map.t;
      external_ids : 'a Index.Map.t
    }

  let print ppf { definitions_in_joined_envs; _ } =
    Variable_in_target_env.Map.print
      (fun ppf (simples, _) ->
        Index.Map.print Simple_in_one_joined_env.print ppf simples)
      ppf definitions_in_joined_envs

  let create ~external_ids ~joined_envs definitions_in_joined_envs =
    let canonical_definitions_at_normal_mode =
      Variable_in_target_env.Map.filter_map
        (fun _name ((simples : Simples_in_joined_envs.t), kind) ->
          let exists_at_normal_name_mode_in_all_envs_it_is_defined_in =
            Index.Map.for_all
              (fun env_id simple ->
                let typing_env =
                  match Index.Map.find_opt env_id joined_envs with
                  | Some typing_env -> typing_env
                  | None ->
                    Misc.fatal_errorf "Join does not include environment %a"
                      Index.print env_id
                in
                TE.mem_simple ~min_name_mode:Name_mode.normal typing_env simple)
              (simples :> Simple.t Index.Map.t)
          in
          if exists_at_normal_name_mode_in_all_envs_it_is_defined_in
          then Some (simples, kind)
          else None)
        definitions_in_joined_envs
    in
    { definitions_in_joined_envs;
      canonical_definitions_at_normal_mode;
      external_ids
    }

  module Variable_refined_at_join = struct
    type 'a t =
      { canonicals_in_joined_envs : Simple_in_one_joined_env.t Index.Map.t;
        kind : K.t;
        external_ids : 'a Index.Map.t
      }

    let fold_values_at_uses f t init =
      Index.Map.fold
        (fun index simple acc ->
          match Index.Map.find_opt index t.external_ids with
          | None -> Misc.fatal_error "Missing environment for use"
          | Some external_id ->
            Simple_in_one_joined_env.pattern_match simple
              ~const:(fun const -> f external_id (Or_unknown.Known const) acc)
              ~name:(fun _ ~coercion:_ -> f external_id Or_unknown.Unknown acc))
        t.canonicals_in_joined_envs init
  end

  type 'a simple_refined_at_join =
    | Not_refined_at_join
    | Invariant_in_all_uses of Simple.t
    | Variable_refined_at_these_uses of 'a Variable_refined_at_join.t

  let simple_refined_at_join t env simple =
    let simple = TE.get_canonical_simple_ignoring_name_mode env simple in
    Simple.pattern_match' simple
      ~const:(fun _ -> Invariant_in_all_uses simple)
      ~symbol:(fun _ ~coercion:_ -> Invariant_in_all_uses simple)
      ~var:(fun var ~coercion:_ ->
        match
          Variable_in_target_env.Map.find_opt
            (Variable_in_target_env.create var)
            t.definitions_in_joined_envs
        with
        | None ->
          (* CR bclement: This is not entirely true -- variables in the source
             env could have been refined at some (but not all!) of the uses, in
             which case we won't have a [definition_in_join_env].

             This could be fixed by storing a [definition_in_join_env] in the
             [Latest_bound_source_var] / [Canonical_in_source_env] case in
             [join_aliases_into_bindings]. *)
          Not_refined_at_join
        | Some (canonicals_in_joined_envs, kind) ->
          Variable_refined_at_these_uses
            { Variable_refined_at_join.canonicals_in_joined_envs;
              kind;
              external_ids = t.external_ids
            })

  module Simples_at_join = struct
    type 'a t =
      { canonicals_in_joined_envs : Simple_in_one_joined_env.t Index.Map.t;
        external_ids : 'a Index.Map.t
      }

    type definition_at_use = At_normal_mode of Simple.t [@@unboxed]

    let fold_definitions_at_uses f t init =
      Index.Map.fold
        (fun index simple acc ->
          match Index.Map.find_opt index t.external_ids with
          | None -> Misc.fatal_error "Missing environment for use"
          | Some external_id ->
            f external_id
              (At_normal_mode (simple : Simple_in_one_joined_env.t :> Simple.t))
              acc)
        t.canonicals_in_joined_envs init
  end

  let fold_variables_created_at_join ~f t ~init =
    Variable_in_target_env.Map.fold
      (fun var (canonicals_in_joined_envs, kind) acc ->
        (f [@inlined hint])
          (Name.var (var :> Variable.t))
          { Simples_at_join.canonicals_in_joined_envs;
            external_ids = t.external_ids
          }
          kind acc)
      t.canonical_definitions_at_normal_mode init
end

let cut_and_n_way_join_with_analysis ~n_way_join_type ~meet_expanded_head
    ~cut_after source_env joined_envs =
  if Flambda_features.debug_flambda2 ()
  then Format.eprintf "cut_and_n_way_join_with_analysis: START@.";
  let external_ids, joined_envs, equations_to_join, symbol_projections_to_join =
    Index.fold_list
      (fun index (external_id, typing_env)
           (( external_ids,
              joined_envs,
              equations_to_join,
              symbol_projections_to_join ) as acc) ->
        (* Skip bottom environments -- we should have detected the impossibility
           and replaced them with an invalid earlier, but if we did not, they
           won't bring anything but subtleties to the join. *)
        if TE.is_bottom typing_env
        then acc
        else
          let equations, symbol_projections =
            cut_for_join typing_env ~cut_after
          in
          ( Index.Map.add index external_id external_ids,
            Index.Map.add index typing_env joined_envs,
            Index.Map.add index (typing_env, equations) equations_to_join,
            Index.Map.add index symbol_projections symbol_projections_to_join ))
      joined_envs
      (Index.Map.empty, Index.Map.empty, Index.Map.empty, Index.Map.empty)
  in
  let source_env = ME.create source_env in
  let target_env, bindings =
    cut_and_n_way_join0 ~n_way_join_type ~meet_expanded_head ~cut_after
      source_env joined_envs equations_to_join symbol_projections_to_join
  in
  let target_env = ME.typing_env target_env in
  let join_analysis = Analysis.create ~external_ids ~joined_envs bindings in
  target_env, join_analysis

(** {2:callbacks Callbacks for the join of types} *)

let cut_and_n_way_join ~n_way_join_type ~meet_expanded_head ~cut_after
    source_env joined_envs =
  let joined_envs, equations_to_join, symbol_projections_to_join =
    Index.fold_list
      (fun index typing_env
           ((joined_envs, equations_to_join, symbol_projections_to_join) as acc)
         ->
        (* Skip bottom environments -- we should have detected the impossibility
           and replaced them with an invalid earlier, but if we did not, they
           won't bring anything but subtleties to the join. *)
        if TE.is_bottom typing_env
        then acc
        else
          let equations, symbol_projections =
            cut_for_join typing_env ~cut_after
          in
          ( Index.Map.add index typing_env joined_envs,
            Index.Map.add index (typing_env, equations) equations_to_join,
            Index.Map.add index symbol_projections symbol_projections_to_join ))
      joined_envs
      (Index.Map.empty, Index.Map.empty, Index.Map.empty)
  in
  let target_env, _ =
    cut_and_n_way_join0 ~n_way_join_type ~meet_expanded_head ~cut_after
      source_env joined_envs equations_to_join symbol_projections_to_join
  in
  target_env

let joined_env t index = Joined_envs.get_nth_joined_env t.joined_envs index

let machine_width t =
  Source_env.machine_width (Bindings_in_target_env.source_env t.bindings)

(* Exposed to the outside world with a different name *)
let import_type env ty = import_type_transitive env ty

let n_way_join_simples t kind simples : _ Or_bottom.t * t =
  match simples with
  | [] -> Bottom, t
  | _ :: _ -> (
    match simples with
    | [] -> Misc.fatal_errorf "N-way join of zero simples"
    | (_, simple) :: simples
      when List.for_all
             (fun (_, simple') -> Simple.equal simple simple')
             simples ->
      Ok simple, import_simple_transitive t simple
    | _ :: _ -> (
      let canonicals =
        Joined_envs.get_canonical_simples_ignoring_name_mode t.joined_envs
          simples
      in
      match get_canonical_in_target_env t canonicals kind with
      | Canonical_in_source_env canonical -> Ok (canonical :> Simple.t), t
      | Import_from_all_joined_envs canonical ->
        let env = import_simple_transitive t (canonical :> Simple.t) in
        Ok (canonical :> Simple.t), env
      | Existential_for_these_simples (existential_var, env) ->
        Ok (Simple.var (existential_var :> Variable.t)), env))

let n_way_join_env_extension ~n_way_join_type:_ ~meet_expanded_head:_ t
    extensions : _ Or_bottom.t =
  (* Don't try to do something complicated for the join of env extensions for
     now: simply import the content of the env extension if it is the same in
     all joined environments (in particular, always import env extensions when
     there is a single joined environment). *)
  match extensions with
  | [] -> Bottom
  | (_, first_extension) :: other_extensions ->
    if
      List.for_all
        (fun (_, ext) ->
          Name.Map.equal ( == ) (TEE.to_map ext) (TEE.to_map first_extension))
        other_extensions
    then
      let t =
        TEE.fold first_extension t ~equation:(fun name ty env ->
            import_type_transitive (import_name_transitive env name) ty)
      in
      Ok (first_extension, t)
    else Ok (TEE.empty, t)
