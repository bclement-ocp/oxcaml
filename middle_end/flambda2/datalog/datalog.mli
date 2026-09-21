(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Basile Clément, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2024--2025 OCamlPro SAS                                    *)
(*   Copyright 2024--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Heterogenous_list

(** {2 Query language} *)

(** Fact retrieval is supported through a query expressed using (typed) Datalog
    queries. *)

module Term : sig
  include
    Heterogenous_list.S
      with type 'a t = 'a Lang.Term.t
       and type 'a hlist = 'a Lang.Term.hlist

  val constant : 'a -> 'a t
end

module String : sig
  include Heterogenous_list.S with type 'a t := string
end

(** The type [('p, 'v) program] is the type of programs returning values of type
    ['v] with parameters ['p].

    The output of programs is either queries or rules; the use of a shared types
    allows writing combinators that work in both cases. *)
type ('p, 'a) program

val compile : 'v String.hlist -> ('v Term.hlist -> (nil, 'a) program) -> 'a

val compile_with_parameters :
  'p String.hlist ->
  'v String.hlist ->
  ('p Term.hlist -> 'v Term.hlist -> ('p, 'a) program) ->
  'a

val foreach :
  'a String.hlist -> ('a Term.hlist -> ('p, 'b) program) -> ('p, 'b) program

val where_atom : Lang.atom -> ('p, 'a) program -> ('p, 'a) program

val yield : 'v Term.hlist -> ('p, ('p, 'v) Cursor.With_parameters.t) program

val deduce : Lang.atom list -> (nil, Schedule.rule) program
