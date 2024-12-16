type relation

(** Create a new relation with the given arity. *)
val create_relation :
  arity:int ->
  ?print:(Format.formatter -> int array -> unit) ->
  string ->
  relation

type term

type symbol

val create_symbol : int -> symbol

type variable = string

val symbol : symbol -> term

val variable : variable -> term

type fact

val create_fact : relation -> symbol array -> fact

type atom

val create_atom : relation -> term array -> atom

type query

val create_query :
  variables:variable array ->
  ?existentials:variable array ->
  ?negate:atom array ->
  atom array ->
  query

type rule

(** [create_rule ~variables action ?existentials hyps] creates a new rule to
    apply the action [action] whenever all the atoms in [hyps] are in the
    database.

    The order in which variables are matched respect the [variables] ordering,
    followed by the [existentials] ordering.

    The existential variables in [existentials] can only be used in the
    hypotheses [hyps]; their value is not available to the [action]. *)
val create_rule :
  variables:variable array ->
  atom ->
  ?existentials:variable array ->
  ?negate:atom array ->
  atom array ->
  rule

val create_deletion_rule :
  variables:variable array ->
  atom ->
  ?existentials:variable array ->
  ?negate:atom array ->
  atom array ->
  rule

type database

val print_database : Format.formatter -> database -> unit

val create : unit -> database

val add_fact : database -> fact -> database

val add_rule : database -> rule -> database

val saturate : database -> database

module Schedule : sig
  type t

  val saturate : rule list -> t

  val list : t list -> t

  val fixpoint : t -> t
end

val run_schedule : database -> Schedule.t -> database * Schedule.t

val bind_query : database -> query -> unit

type tuple

val tuple_arity : tuple -> int

val tuple_get : tuple -> int -> symbol

val query_current : query -> tuple option

val query_advance : database -> query -> unit

val relation_name : relation -> string

val filter_database : (relation -> bool) -> database -> database

val register_index : database -> relation -> int array -> database

val set_schedule : database -> Schedule.t -> database

val mem_fact : database -> fact -> bool

val print_fact : Format.formatter -> fact -> unit

val table_size : database -> relation -> int
