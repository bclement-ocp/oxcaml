type _ hlist =
  | [] : unit hlist
  | ( :: ) : 'a * 'b hlist -> ('a * 'b) hlist

module Tuple : sig
  type 'a t

  type ('a, 'b) field

  val get_field : 'a t -> ('a, 'b) field -> 'b

  val set_field : 'a t -> ('a, 'b) field -> 'b -> unit

  type (_, _) fields =
    | [] : ('a, unit) fields
    | ( :: ) : ('a, 'b) field * ('a, 'c) fields -> ('a, 'b * 'c) fields

  val get_fields : 'a t -> ('a, 'b) fields -> 'b hlist

  val set_fields : 'a t -> ('a, 'b) fields -> 'b hlist -> unit

  val create : 'a hlist -> 'a t * ('a, 'a) fields

  val copy : 'a t -> 'a t
end = struct
  module T0 : sig
    type 'a t

    type ('a, 'b) field

    val unsafe_field : int -> ('a, 'b) field

    val get_field : 'a t -> ('a, 'b) field -> 'b

    val set_field : 'a t -> ('a, 'b) field -> 'b -> unit
  end = struct
    type not_float = private
      | Imm
      | Addr of Obj.t

    type 'a t = private not_float array

    type ('a, 'b) field = int

    let unsafe_field field = field

    external opaque : 'a t -> 'a t = "%opaque"

    external get_field : 'a t -> ('a, 'b) field -> 'b = "%obj_field"

    external set_field : 'a t -> ('a, 'b) field -> 'b -> unit = "%obj_set_field"
  end

  include T0

  type (_, _) fields =
    | [] : ('a, unit) fields
    | ( :: ) : ('a, 'b) field * ('a, 'c) fields -> ('a, 'b * 'c) fields

  let rec get_fields : type a b. a t -> (a, b) fields -> b hlist =
   fun obj fields ->
    match fields with
    | [] -> []
    | field :: fields -> get_field obj field :: get_fields obj fields

  let rec set_fields : type a b. a t -> (a, b) fields -> b hlist -> unit =
   fun obj fields values ->
    match fields, values with
    | [], [] -> ()
    | field :: fields, value :: values ->
      set_field obj field value;
      set_fields obj fields values

  let create : type a. a hlist -> a t * (a, a) fields =
   fun values ->
    match values with
    | [] -> failwith "nope"
    | _ :: _ ->
      let rec loop : type b. b hlist -> int ref -> int -> (a, b) fields =
       fun values length ofs ->
        match values with
        | [] ->
          length := ofs;
          []
        | _value :: values -> unsafe_field ofs :: loop values length (ofs + 1)
      in
      let length = ref (-1) in
      let fields = (loop [@unrolled 10]) values length 0 in
      assert (!length > 0);
      let obj : a t = Obj.obj (Obj.new_block 0 !length) in
      set_fields obj fields values;
      obj, fields

  let copy : type a. a t -> a t =
   fun obj : a t -> Obj.obj (Obj.dup (Obj.repr obj))
end

let () =
  let tup, [a; b; c] = Tuple.create [1; 2; 3] in
  Tuple.set_field tup a 7;
  let [a'; b'; c'] = Tuple.get_fields tup [a; b; c] in
  Format.eprintf "(%d, %d, %d)@." a' b' c'
