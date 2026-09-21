open Datalog_imports

type 'a variable

module Variable : sig
  type 'a t = 'a variable

  val print : Format.formatter -> 'a t -> unit

  val create : string -> 'a t

  val name : 'a t -> string

  include Heterogenous_list.S with type 'a t := 'a t

  module Id : sig
    type t

    val equal : t -> t -> bool

    val hash : t -> int

    module Set : Container_types.Set with type elt = t

    module Map : Container_types.Map with type key = t

    module Tbl : Hashtbl.S with type key = t
  end

  val uid : 'a t -> Id.t

  val provably_equal : 'a t -> 'b t -> ('a, 'b) Type.eq option

  (* Raises [Misc.Fatal_error] if the two variables are not equal.

     Variables with the same [uid] are guaranteed to be equal. *)
  val must_be_equal : 'a t -> 'b t -> ('a, 'b) Type.eq
end

type 'a term =
  | Variable of 'a variable
  | Literal of 'a

val print_term :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a term -> unit

val var : 'a variable -> 'a term

val lit : 'a -> 'a term

module Term : sig
  type 'a t = 'a term

  include Heterogenous_list.S with type 'a t := 'a t
end

type ('k, 'v) relation =
  | Table : (_, 'k, 'v) Table.Id.t -> ('k, 'v) relation
  | Unless : (_, 'k, 'v) Table.Id.t -> ('k, unit) relation
  | Distinct : (_, 'k, _) Column.id -> ('k -> 'k -> nil, unit) relation
  | Filter : ('k Constant.hlist -> bool) * string -> ('k, unit) relation
  | Callback_with_bindings :
      (Bytecode.bindings_ref -> 'k Constant.hlist -> unit) * string
      -> ('k, unit) relation

type atom =
  | Atom : ('k, 'v) relation * 'k Term.hlist * 'v variable option -> atom
      (** Relations have values in a poset for type ['v], i.e. a relation of
          type [('k, 'v) relation] is actually a partial function from
          ['k]-tuples to the poset ['v].

          An atom with a value component [Atom (relation, args, Some term)],
          written {m relation(args) <= value}, represents the predicate:

          {m exists v. (args, v) \in relation /\ v <= term}

          i.e. [args] is in the domain of [relation] and maps to a value that is
          less than or equal to [term] in the poset for type ['v].

          An atom without a value component [Atom (relation, args, None)],
          written {m relation(args)}, represents the predicate:

          {m exists v. (args, v) \in relation }

          i.e. [args] is in the domain of [relation] and maps to any value in
          the poset for type ['v].

          {b Note}: Variables in the value component of a body atom are in
          binding position and are called "late-bound variables" (because they
          can only be bound once all of the variables in the arguments of the
          atom have been bound).

          If the same variable appears as a late-bound variable in multiple
          atoms, it will be bound to the smallest value that satisfy {b all} of
          the predicates associated with the atoms, i.e. the join of the values
          stored in relations. This semantic is forced by monotonicity
          constraints.

          {b Examples}

          To compute {m R(x, y) <- max P(x) Q(y)}, use the following rule:

          R(x, y) <= z :- P(x) <= z, Q(y) <= z.

          To compute {m R(x, y) <- min P(x) Q(y)}, use this rule instead:

          R(x, y) <= a, R(x, y) <= b :- P(x) <= a, Q(y) <= b. *)

val print_atom : Format.formatter -> atom -> unit

val print_neg_atom : Format.formatter -> atom -> unit

val atom : ('k, 'v) relation -> 'k Term.hlist -> atom

val table : (_, 'k, 'v) Table.Id.t -> 'k Term.hlist -> atom

val unless : (_, 'k, 'v) Table.Id.t -> 'k Term.hlist -> atom

val distinct : (_, 'k, _) Column.id -> 'k term -> 'k term -> atom

val filter :
  ?name:string -> ('k Constant.hlist -> bool) -> 'k Term.hlist -> atom

val less_than_or_equal :
  (_, 'k, 'v) Table.Id.t -> 'k Term.hlist -> 'v variable -> atom

val callback_with_bindings :
  name:string ->
  (Bytecode.bindings_ref -> 'k Constant.hlist -> unit) ->
  'k Term.hlist ->
  atom

type rule =
  { head : atom iarray;
    body : atom iarray
  }

val print_rule : Format.formatter -> rule -> unit

val rule : head:atom list -> body:atom list -> rule
