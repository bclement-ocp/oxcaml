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

module Int = struct
  include Numbers.Int
  module Tree = Patricia_tree.Make (Numbers.Int)
  module Map = Tree.Map
end

(* This is the [Type] module from OCaml 5's Stdlib *)
module Type = struct
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

type _ result_repr =
  | Unit_repr : unit result_repr
  | Custom_repr :
      { print : Format.formatter -> 'a -> unit;
        meet : 'a -> 'a -> 'a;
        join_or_null : 'a -> 'a -> 'a Or_null.t;
        diff_or_null : 'a -> 'a -> 'a Or_null.t
      }
      -> 'a result_repr

let unit_repr = Unit_repr

let custom_repr ~print ~meet ~join_or_null ?diff_or_null () =
  let diff_or_null =
    match diff_or_null with
    | Some diff_or_null -> diff_or_null
    | None -> fun v1 v2 -> if v1 == v2 then Or_null.null else Or_null.this v1
  in
  Custom_repr { print; meet; join_or_null; diff_or_null }
[@@inline]

let provably_unit_repr : type t. t result_repr -> (t, unit) Type.eq option =
  function
  | Unit_repr -> Some Equal
  | Custom_repr _ -> None

let result_repr_print (type t) (repr : t result_repr) :
    Format.formatter -> t -> unit =
  match repr with
  | Unit_repr -> fun ppf () -> Format.fprintf ppf "()"
  | Custom_repr { print; _ } -> print

let result_repr_join_or_null (type t) (repr : t result_repr) :
    t -> t -> t Or_null.t =
  match repr with
  | Unit_repr -> fun () () -> Or_null.this ()
  | Custom_repr { join_or_null; _ } -> join_or_null

let union_total0 : type t k v.
    (t, k, v) Column.hlist -> (v -> v -> v) -> t -> t -> t =
 fun columns union_total_result t1 t2 ->
  let rec union_total : type t k. (t, k, v) Column.hlist -> t -> t -> t =
   fun columns t1 t2 ->
    match columns with
    | [] -> (union_total_result [@inlined hint]) t1 t2
    | column :: columns -> Column.union_total column (union_total columns) t1 t2
  in
  union_total columns t1 t2
[@@inline]

let union : type t k v. (t, k, v) Column.hlist -> v result_repr -> t -> t -> t =
 fun columns repr ->
  match repr with
  | Unit_repr -> union_total0 columns (fun () () -> ())
  | Custom_repr { meet = union_total_result; _ } ->
    union_total0 columns union_total_result

let diff_or_null0 : type t k v.
    (t, k, v) Column.hlist -> (v -> v -> v Or_null.t) -> t -> t -> t Or_null.t =
 fun columns diff_or_null_result t1 t2 ->
  let rec diff_or_null : type t k.
      (t, k, v) Column.hlist -> t -> t -> t Or_null.t =
   fun columns t1 t2 ->
    match columns with
    | [] -> (diff_or_null_result [@inlined hint]) t1 t2
    | column :: columns ->
      Column.diff_or_null column (diff_or_null columns) t1 t2
  in
  diff_or_null columns t1 t2
[@@inline]

let diff_or_null : type t k v.
    (t, k, v) Column.hlist -> v result_repr -> t -> t -> t Or_null.t =
 fun columns repr ->
  match repr with
  | Unit_repr -> diff_or_null0 columns (fun () () -> Or_null.null)
  | Custom_repr { diff_or_null = diff_or_null_result; _ } ->
    diff_or_null0 columns diff_or_null_result

let rec concat : type t k v. (t, k, v) Column.hlist -> earlier:t -> later:t -> t
    =
 fun columns ~earlier ~later ->
  match columns with
  | [] -> later
  | column :: columns ->
    Column.union_total column
      (fun earlier later -> concat columns ~earlier ~later)
      earlier later

module Id = struct
  type (!'t, !'k, !'v) t =
    { id : ('t * 'k) Type.Id.t;
      name : string;
      columns : ('t, 'k, 'v) Column.hlist;
      result_repr : 'v result_repr;
      provenance : bool
    }

  let name { name; _ } = name

  type ('k, 'v) poly = Id : ('t, 'k, 'v) t -> ('k, 'v) poly

  let print ppf t = Format.fprintf ppf "%s" t.name

  let hash { id; _ } = Hashtbl.hash (Type.Id.uid id)

  let equal { id = id1; _ } { id = id2; _ } = Type.Id.uid id1 = Type.Id.uid id2

  let[@inline] provably_equal_keys_exn (type a k v a' k' v') (r1 : (a, k, v) t)
      (r2 : (a', k', v') t) : (k, k') Type.eq =
    match Type.Id.provably_equal r1.id r2.id with
    | Some Equal -> Equal
    | None -> Misc.fatal_error "Inconsistent type for uid."

  let[@inline] provably_equal_exn (type a k v a' k' v') (r1 : (a, k, v) t)
      (r2 : (a', k', v') t) : (a, a') Type.eq =
    match Type.Id.provably_equal r1.id r2.id with
    | Some Equal -> Equal
    | None -> Misc.fatal_error "Inconsistent type for uid."

  let compare { id = id1; _ } { id = id2; _ } =
    compare (Type.Id.uid id1) (Type.Id.uid id2)

  let create ~provenance ~name ~columns ~result_repr =
    { id = Type.Id.make (); name; columns; result_repr; provenance }

  let has_provenance { provenance; _ } = provenance

  let[@inline] result_repr { result_repr; _ } = result_repr

  let[@inline] columns { columns; _ } = columns

  let[@inline] uid { id; _ } = Type.Id.uid id

  let[@inline] cast_exn (type a b k v k' v') (r1 : (a, k, v) t)
      (r2 : (b, k', v') t) (t : a) : b =
    match Type.Id.provably_equal r1.id r2.id with
    | Some Equal -> t
    | None -> Misc.fatal_error "Inconsistent type for uid."
end

let iter id f table =
  let columns = Id.columns id in
  Column.iter_hlist columns f table

let print id ?(pp_sep = Format.pp_print_cut) pp_row ppf table =
  let first = ref true in
  iter id
    (fun keys value ->
      if !first then first := false else pp_sep ppf ();
      pp_row keys value)
    table

let print_equals_value (type v) (repr : v result_repr) ppf v =
  match provably_unit_repr repr with
  | Some Equal -> ()
  | None -> Format.fprintf ppf " = @[%a@]" (result_repr_print repr) v

let print_table (id : (_, _, _) Id.t) ppf table =
  Format.fprintf ppf "@[<v>%a@]"
    (print id (fun keys value ->
         Format.fprintf ppf "@[%a(%a)%a.@]" Id.print id
           (Column.print_keys id.columns)
           keys
           (print_equals_value (Id.result_repr id))
           value))
    table

let print id ppf table =
  let header = Format.asprintf "%a" Id.print id in
  Format.fprintf ppf "@[<v>%s@ %s@ %a@]" header
    (String.make (String.length header) '=')
    (print_table id) table

module Map = struct
  type binding = Binding : ('t, 'k, 'v) Id.t * 't -> binding

  type t = binding Int.Map.t

  let print ppf tables =
    let first = ref true in
    Format.fprintf ppf "@[<v>";
    Int.Map.iter
      (fun _ (Binding (id, table)) ->
        if !first then first := false else Format.fprintf ppf "@ @ ";
        print id ppf table)
      tables;
    Format.fprintf ppf "@]"

  let get_or_null (type t k v) (id : (t, k, v) Id.t) tables : t Or_null.t =
    match Int.Map.find_opt (Id.uid id) tables with
    | Some (Binding (existing_id, table)) ->
      Or_null.this (Id.cast_exn existing_id id table)
    | None -> Or_null.null

  let set (type t k v) (id : (t, k, v) Id.t) (table : t) tables =
    if Column.is_empty_hlist (Id.columns id) table
    then Int.Map.remove (Id.uid id) tables
    else Int.Map.add (Id.uid id) (Binding (id, table)) tables

  let set_or_null id (table : _ Or_null.t) tables =
    match table with
    | Null -> Int.Map.remove (Id.uid id) tables
    | This table -> set id table tables

  let empty = Int.Map.empty

  let is_empty = Int.Map.is_empty

  let concat ~earlier:tables1 ~later:tables2 =
    Int.Map.union_total
      (fun _ (Binding (id1, table1)) (Binding (id2, table2)) ->
        let table =
          concat (Id.columns id1) ~earlier:table1
            ~later:(Id.cast_exn id2 id1 table2)
        in
        Binding (id1, table))
      tables1 tables2

  let fold ~f m ~init = Int.Map.fold (fun _ binding acc -> f binding acc) m init
end
