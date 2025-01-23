(* This module provides facilities for checking that two types are equal, for a
   {b semantic} definition of equality: aliases are resolved with respect to a
   typing environment.

   {b Warning}: This module should only be used for debugging purposes. It has
   high computational complexity, and no guarantees is made on the precision of
   the equality test, in particular for types containing env extensions. *)

val equal_type :
  meet_type:Typing_env.meet_type ->
  Typing_env.t ->
  Type_grammar.t ->
  Type_grammar.t ->
  bool

val equal_env_extension :
  meet_type:Typing_env.meet_type ->
  Typing_env.t ->
  Typing_env_extension.t ->
  Typing_env_extension.t ->
  bool

(* Variables defined by the levels are treated as existentials. *)
val equal_level_ignoring_name_mode :
  meet_type:Typing_env.meet_type ->
  Typing_env.t ->
  Typing_env_level.t ->
  Typing_env_level.t ->
  bool
