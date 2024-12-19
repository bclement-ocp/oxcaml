module ColumnType : sig
  type 'a t

  type _ hlist =
    | [] : unit hlist
    | ( :: ) : 'a t * 'b hlist -> ('a * 'b) hlist

  val int : int t

  val make : string -> print:(Format.formatter -> int -> unit) -> int t
end

module Relation : sig
  type ('k, 'v) t

  val create : name:string -> 'k ColumnType.hlist -> ('k, 'v) t
end

module Constant : sig
  type _ hlist =
    | [] : unit hlist
    | ( :: ) : 'a * 'b hlist -> ('a * 'b) hlist
end

type database

val empty : database

val add_fact :
  ('a, unit) Relation.t -> 'a Constant.hlist -> database -> database

module Variable : sig
  type t = string

  type _ hlist =
    | [] : unit hlist
    | ( :: ) : (t * 'a ColumnType.t) * 'b hlist -> ('a * 'b) hlist
end

module Term : sig
  type 'a t

  val variable : Variable.t -> 'a t

  val constant : 'a -> 'a t

  type _ hlist =
    | [] : unit hlist
    | ( :: ) : 'a t * 'b hlist -> ('a * 'b) hlist
end

module Atom : sig
  type 'a t

  val create : ('k, 'v) Relation.t -> 'k Term.hlist -> 'v t
end

module Query : sig
  type ('p, 'v) t

  val create :
    parameters:'p Variable.hlist ->
    variables:'v Variable.hlist ->
    unit Atom.t list ->
    ('p, 'v) t

  val fold :
    ('p, 'v) t ->
    'p Constant.hlist ->
    database ->
    init:'a ->
    f:('v Constant.hlist -> 'a -> 'a) ->
    'a

  val iter :
    ('p, 'v) t ->
    'p Constant.hlist ->
    database ->
    f:('v Constant.hlist -> unit) ->
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
