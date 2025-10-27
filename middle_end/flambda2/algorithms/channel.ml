(******************************************************************************
 *                                  OxCaml                                    *
 *                        Basile Clément, OCamlPro                            *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2025 OCamlPro SAS                                            *
 * Copyright (c) 2025 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

module type S = sig
  type 'a sender

  val send : 'a sender -> 'a -> unit

  type 'a receiver

  val recv : 'a receiver -> 'a
end

module Dummy : sig
  type 'stamp dummy

  type fresh_dummy = Fresh : 'stamp dummy -> fresh_dummy

  val fresh : unit -> fresh_dummy

  module Ref : sig
    type 'a t

    val create : 'dummy dummy -> 'a t

    external set : 'a t -> 'a -> unit = "%setfield0"

    val get : 'a t -> 'a
  end
end = struct
  type 'stamp dummy = < >

  type fresh_dummy = Fresh : 'stamp dummy -> fresh_dummy

  let fresh () =
    let r = ref None in
    let dummy =
      object
        val x = r
      end
    in
    r := Some dummy;
    Fresh dummy

  type ('a, 'stamp) or_dummy

  external from_dummy : 'stamp dummy -> ('a, 'stamp) or_dummy = "%opaque"

  external unsafe_to_val : ('a, 'stamp) or_dummy -> 'a = "%opaque"

  module Ref = struct
    type 'a t =
      | Ref :
          { mutable contents : ('a, 'stamp) or_dummy;
            dummy : 'stamp dummy
          }
          -> 'a t

    let create dummy = Ref { contents = from_dummy dummy; dummy }

    external set : 'a t -> 'a -> unit = "%setfield0"

    let get (Ref { contents; dummy }) =
      if contents == from_dummy dummy
      then Misc.fatal_error "Trying to read from uninitialized reference"
      else unsafe_to_val contents
  end
end

module Initialized : sig
  include S

  val create : 'a -> 'a sender * 'a receiver
end = struct
  type 'a sender = 'a ref

  type 'a receiver = 'a ref

  let send = ( := )

  let recv = ( ! )

  let create v =
    let r = ref v in
    r, r
end

module Uninitialized : sig
  include S

  val create : unit -> 'a sender * 'a receiver
end = struct
  let global_dummy = Dummy.fresh ()

  type 'a sender = 'a Dummy.Ref.t

  type 'a receiver = 'a Dummy.Ref.t

  let create v =
    ignore v;
    let (Fresh dummy) = global_dummy in
    let r = Dummy.Ref.create dummy in
    r, r

  let send = Dummy.Ref.set

  let recv = Dummy.Ref.get
end

include Initialized
