module type Heterogenous = sig
  type 'a t

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist
end

module ColumnType : sig
  include Heterogenous

  val int : int t

  val make : string -> print:(Format.formatter -> int -> unit) -> int t
end

module Constant : sig
  include Heterogenous with type 'a t := 'a
end

(** {2 Facts database} *)

type database

val print : Format.formatter -> database -> unit

val empty : database

type 'k relation

val create_relation :
  name:string -> ('k -> 'r) ColumnType.hlist -> ('k -> 'r) relation

type 'a rel1 = ('a -> unit option) relation

type ('a, 'b) rel2 = ('a -> 'b -> unit option) relation

type ('a, 'b, 'c) rel3 = ('a -> 'b -> 'c -> unit option) relation

val add_fact : 'k relation -> 'k Constant.hlist -> database -> database

(** {2 Query language} *)

module Variable : sig
  type t = string

  include Heterogenous with type 'a t := t * 'a ColumnType.t
end

module Term : sig
  include Heterogenous

  val variable : Variable.t -> 'a t

  val constant : 'a -> 'a t
end

type 'a atom

val atom : 'k relation -> 'k Term.hlist -> unit atom

module Cursor : sig
  type ('p, 'v) with_parameters

  type 'v t = (unit option, 'v) with_parameters

  val create :
    'v Variable.hlist ->
    ?negate:('v Term.hlist -> unit atom list) ->
    ('v Term.hlist -> unit atom list) ->
    'v t

  val fold :
    'v t -> database -> init:'a -> f:('v Constant.hlist -> 'a -> 'a) -> 'a

  val iter : 'v t -> database -> f:('v Constant.hlist -> unit) -> unit

  val create_with_parameters :
    parameters:'p Variable.hlist ->
    'v Variable.hlist ->
    ?negate:('p Term.hlist -> 'v Term.hlist -> unit atom list) ->
    ('p Term.hlist -> 'v Term.hlist -> unit atom list) ->
    ('p, 'v) with_parameters

  val fold_with_parameters :
    ('p, 'v) with_parameters ->
    'p Constant.hlist ->
    database ->
    init:'a ->
    f:('v Constant.hlist -> 'a -> 'a) ->
    'a

  val iter_with_parameters :
    ('p, 'v) with_parameters ->
    'p Constant.hlist ->
    database ->
    f:('v Constant.hlist -> unit) ->
    unit
end

(** {2 Inference rules} *)

module Rule : sig
  type t

  val create :
    variables:string list ->
    ?existentials:string list ->
    unit atom ->
    ?negate:unit atom list ->
    unit atom list ->
    t

  val delete :
    variables:string list ->
    ?existentials:string list ->
    unit atom ->
    ?negate:unit atom list ->
    unit atom list ->
    t
end

module Schedule : sig
  type t

  val fixpoint : t -> t

  val list : t list -> t

  val saturate : Rule.t list -> t

  val run : t -> database -> database
end
