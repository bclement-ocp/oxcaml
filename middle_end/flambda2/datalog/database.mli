type relation

(** Create a new relation with the given arity. *)
val create_relation : arity:int -> relation

type term

type symbol

val create_symbol : int -> symbol

type variable

val create_variable : unit -> variable

val symbol : symbol -> term

val variable : variable -> term

type fact

val create_fact : relation -> symbol array -> fact

type atom

val create_atom : relation -> term array -> atom

type rule

val create_rule :
  variables:variable array ->
  ?existentials:variable array ->
  atom ->
  atom array ->
  rule

type query

val create_query :
  variables:variable array ->
  ?existentials:variable array ->
  atom array ->
  query

type database

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
