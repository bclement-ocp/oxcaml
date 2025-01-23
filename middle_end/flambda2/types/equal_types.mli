val equal_type :
  meet_type:Typing_env.meet_type ->
  Typing_env.t ->
  Typing_env.t ->
  Type_grammar.t ->
  Type_grammar.t ->
  bool

val equal_env_extension :
  meet_type:Typing_env.meet_type ->
  Typing_env.t ->
  Typing_env.t ->
  Typing_env_extension.t ->
  Typing_env_extension.t ->
  bool

val equal_level :
  meet_type:Typing_env.meet_type ->
  Typing_env.t ->
  Typing_env.t ->
  Typing_env_level.t ->
  Typing_env_level.t ->
  bool
