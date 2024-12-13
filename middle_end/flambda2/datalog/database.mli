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
  atom array ->
  query

(** [action]s are used in rules to perform an effect when the right-hand side of
    the rule matches. *)
type action

(** [add_atom atom] adds the fact obtained by substituting variables in [atom]
    to the database. *)
val add_atom : atom -> action

(** [action_sequence actions] performs all the actions in [actions] in order. *)
val action_sequence : action list -> action

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
  atom array ->
  rule

type database

val print_database : Format.formatter -> database -> unit

val create : unit -> database

val add_fact : database -> fact -> database

val add_rule : database -> rule -> database

val saturate : database -> database

val bind_query : database -> query -> unit

type tuple

val tuple_arity : tuple -> int

val tuple_get : tuple -> int -> symbol

val query_current : query -> tuple option

val query_advance : query -> unit
