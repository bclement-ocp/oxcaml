type t

val print : Format.formatter -> t -> unit

val empty : t

val apply_renaming : t -> Renaming.t -> t

type difference

val print_extension : Format.formatter -> difference -> unit

val empty_extension : difference

val is_empty_extension : difference -> bool

type snapshot

val empty_snapshot : snapshot

val apply_renaming_snapshot : snapshot -> Renaming.t -> snapshot

val tick : t -> snapshot * difference

val from_snapshot : snapshot -> t

val concat_extension : earlier:difference -> later:difference -> difference

module Aliases0 : sig
  type t =
    { aliases : Aliases.t;
      demotions : Simple.t Name.Map.t
    }
end

val make_demotions : t -> Type_grammar.t Name.Map.t -> Simple.t Name.Map.t

val rebuild :
  demotions:Simple.t Name.Map.t ->
  binding_time_resolver:(Name.t -> Binding_time.With_name_mode.t) ->
  binding_times_and_modes:('a * Binding_time.With_name_mode.t) Name.Map.t ->
  Aliases0.t ->
  t ->
  (t * Aliases0.t) Or_bottom.t

val add_relation :
  binding_time_resolver:(Name.t -> Binding_time.With_name_mode.t) ->
  binding_times_and_modes:('a * Binding_time.With_name_mode.t) Name.Map.t ->
  Aliases0.t ->
  t ->
  Type_grammar.relation ->
  Name.t ->
  Simple.t ->
  (t * Aliases0.t) Or_bottom.t

val add_continuation_use : Continuation.t -> Apply_cont_rewrite_id.t -> t -> t

type relation_extension

val fold_relations :
  (Type_grammar.relation -> relation_extension -> 'a -> 'a) ->
  difference ->
  'a ->
  'a

val fold_relation_extension :
  (Name.t -> Simple.t -> 'a -> 'a) -> relation_extension -> 'a -> 'a

val continuation_uses : t -> Apply_cont_rewrite_id.Set.t Continuation.Map.t

val add_switch_on_relation :
  Type_grammar.relation ->
  Name.t ->
  ?default:Apply_cont_rewrite_id.Set.t Continuation.Map.t ->
  arms:Apply_cont_rewrite_id.Set.t Continuation.Map.t Reg_width_const.Map.t ->
  t ->
  t Or_bottom.t

val add_switch_on_name :
  Name.t ->
  ?default:Apply_cont_rewrite_id.Set.t Continuation.Map.t ->
  arms:Apply_cont_rewrite_id.Set.t Continuation.Map.t Reg_width_const.Map.t ->
  t ->
  t Or_bottom.t

val interreduce :
  previous:snapshot -> current:t -> difference:difference -> t Or_bottom.t

val switch_on_scrutinee :
  t ->
  scrutinee:Simple.t ->
  Apply_cont_rewrite_id.Set.t Continuation.Map.t Reg_width_const.Map.t
  Or_unknown.t

val add_extension : t -> difference -> t
