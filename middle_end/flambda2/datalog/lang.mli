type variable

val print_variable : Format.formatter -> variable -> unit

type builder

val index : builder -> variable -> variable -> variable

val index' : ?default:string -> builder -> variable -> variable -> variable

val if' : builder -> variable -> unit

val map : builder -> variable -> variable

val eq : builder -> variable -> variable -> variable

val constant : builder -> 'a -> variable

val with_builder :
  parameters:string list ->
  variables:string list ->
  (parameters:variable list -> variables:variable list -> builder -> unit) ->
  unit
