module type Iterator = sig
  type 'a t

  val current : 'a t -> 'a option

  val advance : 'a t -> unit

  val seek : 'a t -> 'a -> unit

  val init : 'a t -> unit

  val accept : 'a t -> unit

  val equal_key : 'a t -> 'a -> 'a -> bool

  val compare_key : 'a t -> 'a -> 'a -> int
end

module type Heterogenous = sig
  type 'a t

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist
end

module Heterogenous (X : sig
  type 'a t
end) =
struct
  type 'a t = 'a X.t

  type _ hlist =
    | [] : 'a option hlist
    | ( :: ) : 'a t * 'b hlist -> ('a -> 'b) hlist
end

module Constant = Heterogenous (struct
  type 'a t = 'a
end)

module Ref = struct
  include Heterogenous (struct
    type 'a t = 'a ref
  end)

  let rec get_hlist : type a. a hlist -> a Constant.hlist = function
    | [] -> []
    | r :: rs -> !r :: get_hlist rs
end
