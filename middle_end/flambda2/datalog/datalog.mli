module type Heterogenous = sig
  type 'a t

  type (_, _) hlist =
    | [] : ('a, 'a) hlist
    | ( :: ) : 'a t * ('b, 'c) hlist -> ('a -> 'b, 'c) hlist
end

module ColumnType : sig
  include Heterogenous

  val int : int t

  val make : string -> print:(Format.formatter -> int -> unit) -> int t
end

module Relation : sig
  type ('k, 'v) t

  val create : name:string -> ('k, unit) ColumnType.hlist -> ('k, 'v) t
end

module Constant : sig
  include Heterogenous with type 'a t := 'a
end

type database

val empty : database

val add_fact :
  ('a, unit) Relation.t -> ('a, unit) Constant.hlist -> database -> database

module Variable : sig
  type t = string

  include Heterogenous with type 'a t := t * 'a ColumnType.t
end

module Term : sig
  include Heterogenous

  val variable : Variable.t -> 'a t

  val constant : 'a -> 'a t
end

module Atom : sig
  type 'a t

  val create : ('k, 'v) Relation.t -> ('k, unit) Term.hlist -> 'v t
end

module Query : sig
  type ('p, 'v) t

  val create :
    parameters:('p, unit) Variable.hlist ->
    variables:('v, unit) Variable.hlist ->
    unit Atom.t list ->
    ('p, 'v) t

  val fold :
    ('p, 'v) t ->
    ('p, unit) Constant.hlist ->
    database ->
    init:'a ->
    f:(('v, unit) Constant.hlist -> 'a -> 'a) ->
    'a

  val iter :
    ('p, 'v) t ->
    ('p, unit) Constant.hlist ->
    database ->
    f:(('v, unit) Constant.hlist -> unit) ->
    unit
end

module Rule : sig
  type t

  val create :
    variables:string list ->
    ?existentials:string list ->
    unit Atom.t ->
    ?negate:unit Atom.t list ->
    unit Atom.t list ->
    t

  val delete :
    variables:string list ->
    ?existentials:string list ->
    unit Atom.t ->
    ?negate:unit Atom.t list ->
    unit Atom.t list ->
    t
end

module Schedule : sig
  type t

  val fixpoint : t -> t

  val list : t list -> t

  val saturate : Rule.t list -> t

  val run : t -> database -> database
end

val print : Format.formatter -> database -> unit
