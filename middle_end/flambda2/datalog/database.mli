type relation

type index

(** Create a new relation with the given arity. *)
val create_relation : arity:int -> relation

(** Create an index for the given permutation of the relation's arguments.

      {b Warning}: The permutation provided to [create_index] must not be
      modified. *)
val create_index : int array -> relation -> index

type term

type symbol

val create_symbol : unit -> symbol

type variable

val create_variable : unit -> variable

val symbol : symbol -> term

val variable : variable -> term

type fact

val create_fact : relation -> symbol array -> fact

type atom

val create_atom : relation -> term array -> atom

val fact : fact -> atom

type rule

val create_rule : variables:variable array -> atom -> atom array -> rule

type query

val create_query : variables:variable array -> atom array -> query

type database

val create : unit -> database

val add_fact : database -> fact -> database

val add_rule : database -> rule -> database

val saturate : database -> database

val query : init:'a -> f:(fact -> 'a) -> database -> query -> 'a
