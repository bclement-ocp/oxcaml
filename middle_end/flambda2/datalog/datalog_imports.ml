(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                     Nathanaëlle Courant, OCamlPro                      *)
(*                                                                        *)
(*   Copyright 2024--2025 OCamlPro SAS                                    *)
(*   Copyright 2024--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type 'a with_name =
  { value : 'a;
    name : string
  }

type 'a with_names =
  { values : 'a;
    names : string list
  }

include Heterogenous_list

module Sender = struct
  module T0 = struct
    type 'a t = 'a Channel.Uninitialized.sender
  end

  include T0
  include Heterogenous_list.Make (T0)

  let send = Channel.Uninitialized.send

  let rec send_many : type s. s hlist -> s Constant.hlist -> unit =
   fun refs values ->
    match refs, values with
    | [], [] -> ()
    | r :: rs, v :: vs ->
      send r v;
      send_many rs vs
end

module Receiver = struct
  module T0 = struct
    type 'a t = 'a Channel.Uninitialized.receiver
  end

  include T0
  include Heterogenous_list.Make (T0)

  let recv = Channel.Uninitialized.recv

  let rec recv_many : type s. s hlist -> s Constant.hlist = function
    | [] -> []
    | r :: rs -> recv r :: recv_many rs
end

let create_channel = Channel.Uninitialized.create

(* This is the [Type] module from OCaml 5's Stdlib *)
module Type : sig
  type (_, _) eq = Equal : ('a, 'a) eq

  module Id : sig
    type !'a t

    val make : unit -> 'a t

    val uid : 'a t -> int

    val provably_equal : 'a t -> 'b t -> ('a, 'b) eq option
  end
end = struct
  type (_, _) eq = Equal : ('a, 'a) eq

  module Id = struct
    type _ id = ..

    module type ID = sig
      type t

      type _ id += Id : t id
    end

    type !'a t = (module ID with type t = 'a)

    let make (type a) () : a t =
      (module struct
        type t = a

        type _ id += Id : t id
      end)

    let[@inline] uid (type a) ((module A) : a t) : int =
      Obj.Extension_constructor.id [%extension_constructor A.Id]

    let provably_equal (type a b) ((module A) : a t) ((module B) : b t) :
        (a, b) eq option =
      match A.Id with B.Id -> Some Equal | _ -> None
  end
end
