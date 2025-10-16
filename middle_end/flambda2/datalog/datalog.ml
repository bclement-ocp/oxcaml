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

open Datalog_imports

module String = struct
  include String

  include Heterogenous_list.Make (struct
    type 'a t = string
  end)
end

let fresh_stamp =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    !cnt

module Parameter = struct
  module T0 = struct
    type 'a t =
      { name : string;
        stamp : int;
        sender : 'a Sender.t;
        receiver : 'a Receiver.t
      }
  end

  include T0
  include Heterogenous_list.Make (T0)

  let name { name; _ } = name

  let create name =
    let sender, receiver = create_channel () in
    { name; stamp = fresh_stamp (); sender; receiver }

  let rec list : type a. a String.hlist -> a hlist = function
    | [] -> []
    | name :: names -> create name :: list names

  let get_sender { sender; _ } = sender

  let get_receiver { receiver; _ } = receiver

  let rec to_senders : type a. a hlist -> a Sender.hlist = function
    | [] -> []
    | p :: ps -> get_sender p :: to_senders ps
end

module Variable = struct
  module T0 = struct
    type 'a t =
      { name : string;
        stamp : int;
        mutable repr : 'a Value.repr option;
        mutable level : 'a Cursor.Level.t option
      }
  end

  include T0
  include Heterogenous_list.Make (T0)

  let name { name; _ } = name

  let create name = { name; stamp = fresh_stamp (); repr = None; level = None }

  let rec list : type a. a String.hlist -> a hlist = function
    | [] -> []
    | name :: names -> create name :: list names

  let repr var =
    match var.repr with
    | None ->
      Misc.fatal_errorf "Missing representation for datalog variable %s"
        var.name
    | Some repr -> repr

  let set_repr var repr =
    match var.repr with
    | None -> var.repr <- Some repr
    | Some existing_repr ->
      if not (existing_repr == repr)
      then
        Misc.fatal_errorf
          "Datalog variable %s used with different value representations (of \
           the same type)"
          var.name
end

module Term = struct
  module T0 = struct
    type _ t =
      | Constant : 'a -> 'a t
      | Parameter : 'a Parameter.t -> 'a t
      | Variable : 'a Variable.t -> 'a t
  end

  include T0
  include Heterogenous_list.Make (T0)

  let parameter param = Parameter param

  let rec parameters : type a. a Parameter.hlist -> a hlist = function
    | [] -> []
    | param :: params -> parameter param :: parameters params

  let variable var = Variable var

  let rec variables : type a. a Variable.hlist -> a hlist = function
    | [] -> []
    | var :: vars -> variable var :: variables vars

  let constant cte = Constant cte

  let set_repr term repr =
    match term with
    | Constant _ | Parameter _ -> ()
    | Variable var -> Variable.set_repr var repr

  let rec set_repr_hlist : type t k v. k hlist -> (t, k, v) Column.hlist -> unit
      =
   fun terms columns ->
    match terms, columns with
    | [], [] -> ()
    | term :: terms, column :: columns ->
      set_repr term (Column.value_repr column);
      set_repr_hlist terms columns
end

type atom = Atom : ('t, 'k, unit) Table.Id.t * 'k Term.hlist -> atom

type condition =
  | Where_atom : ('t, 'k, 'v) Table.Id.t * 'k Term.hlist -> condition

let print_terms columns ppf terms =
  let rec loop :
      type a b c.
      bool ->
      (a, b, c) Column.hlist option ->
      Format.formatter ->
      b Term.hlist ->
      unit =
   fun first columns ppf terms ->
    match terms with
    | [] -> ()
    | term :: terms -> (
      if not first then Format.fprintf ppf ",@ ";
      (match term, columns with
      | Constant cte, Some (column :: _) -> Column.print_key column ppf cte
      | Constant _, None -> Format.fprintf ppf "<cte>"
      | Variable v, _ -> Format.fprintf ppf "%s" (Variable.name v)
      | Parameter p, _ -> Format.fprintf ppf "%s" p.name);
      match columns with
      | None -> loop false None ppf terms
      | Some (_ :: columns) -> loop false (Some columns) ppf terms)
  in
  loop true columns ppf terms

let print_condition ppf condition =
  let (Where_atom (tid, args)) = condition in
  Format.fprintf ppf "@[%a@[(%a)@]@]" Table.Id.print tid
    (print_terms (Some (Table.Id.columns tid)))
    args

type filter =
  | Unless_atom : ('t, 'k, 'v) Table.Id.t * 'k Term.hlist -> filter
  | Unless_eq : 'k Value.repr * 'k Term.t * 'k Term.t -> filter
  | User : ('k Constant.hlist -> bool) * 'k Term.hlist -> filter

let print_filter ppf filter =
  match filter with
  | Unless_atom (tid, args) ->
    Format.fprintf ppf "@[!%a@[(%a)@]@]" Table.Id.print tid
      (print_terms (Some (Table.Id.columns tid)))
      args
  | Unless_eq (_repr, x1, x2) ->
    Format.fprintf ppf "%a != %a" (print_terms None) [x1] (print_terms None) [x2]
  | User (_fn, args) ->
    Format.fprintf ppf "@[<filter>@[(%a)@]@]" (print_terms None) args

type bindings = Bindings : 'a Variable.hlist * 'a Constant.hlist -> bindings

let print_bindings ppf (Bindings (vars, values)) =
  let rec loop :
      type a.
      first:bool ->
      Format.formatter ->
      a Variable.hlist ->
      a Constant.hlist ->
      unit =
   fun ~first ppf vars values ->
    match vars, values with
    | [], [] -> ()
    | var :: vars, value :: values ->
      if not first then Format.fprintf ppf ";@,";
      Format.fprintf ppf "@[<1>%s =@ %a@]" (Variable.name var)
        (Value.print_repr (Variable.repr var))
        value;
      loop ~first:false ppf vars values
  in
  Format.fprintf ppf "@[<2>{ @[<v>";
  loop ~first:true ppf vars values;
  Format.fprintf ppf "@] }@]"

type callback =
  | Callback :
      { func : 'a Constant.hlist -> unit;
        name : string;
        args : 'a Term.hlist
      }
      -> callback
  | Callback_with_bindings :
      { func : bindings -> 'a Constant.hlist -> unit;
        name : string;
        args : 'a Term.hlist
      }
      -> callback

let create_callback func ~name args = Callback { func; name; args }

let create_callback_with_bindings func ~name args =
  Callback_with_bindings { func; name; args }

type (_, _) terminator =
  | Yield :
      'v Term.hlist option
      -> ('p, ('p, 'v) Cursor.With_parameters.t) terminator
  | Map : ('p, 'a) terminator * ('a -> 'b) -> ('p, 'b) terminator

type levels = Levels : 'a Variable.hlist -> levels

let rec prepend_vars : type a. a Variable.hlist -> levels -> levels =
 fun vars levels ->
  match vars with
  | [] -> levels
  | var :: vars ->
    let (Levels vars') = prepend_vars vars levels in
    Levels (var :: vars')

type ('p, 'a) program =
  { conditions : condition list;
    filters : filter list;
    callbacks : callback list;
    terminator : ('p, 'a) terminator;
    levels : levels
  }

let print_program ppf { conditions; filters; callbacks; terminator; levels = _ }
    =
  Format.fprintf ppf "@[%a :- %a@]"
    (print_terminator callbacks)
    terminator
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
       (fun ppf pf -> pf ppf))
    (List.map (fun condition ppf -> print_condition ppf condition) conditions
    @ List.map (fun filter ppf -> print_filter ppf filter) filters)

let add_condition condition program =
  { program with conditions = condition :: program.conditions }

let add_filter filter program =
  { program with filters = filter :: program.filters }

let map_program prog fn = { prog with terminator = Map (prog.terminator, fn) }

let where_atom tid args body =
  Term.set_repr_hlist args (Table.Id.columns tid);
  add_condition (Where_atom (tid, args)) body

let unless_atom tid args body = add_filter (Unless_atom (tid, args)) body

let unless_eq repr x y body = add_filter (Unless_eq (repr, x, y)) body

let filter fn args body = add_filter (User (fn, args)) body

let yield args =
  { conditions = [];
    filters = [];
    callbacks = [];
    terminator = Yield (Some args);
    levels = Levels []
  }

let execute callbacks =
  { conditions = [];
    filters = [];
    callbacks;
    terminator = Yield None;
    levels = Levels []
  }

let foreach :
    type a p b.
    a String.hlist -> (a Term.hlist -> (p, b) program) -> (p, b) program =
 fun names f ->
  let vars = Variable.list names in
  let prog = f (Term.variables vars) in
  { prog with levels = prepend_vars vars prog.levels }

let bind_iterator actions var iterator =
  Cursor.add_action actions (Cursor.bind_iterator var iterator)

let rec bind_atom :
    type a.
    order:_ -> _ -> a Term.hlist -> a Trie.Iterator.hlist -> string list -> unit
    =
 fun ~order post_level args iterators iterator_names ->
  match args, iterators, iterator_names with
  | [], [], [] -> ()
  | [], [], _ :: _ -> Misc.fatal_error "Too many names in [bind_atom]"
  | _, _, [] -> Misc.fatal_error "Missing names in [bind_atom]"
  | ( this_arg :: other_args,
      this_iterator :: other_iterators,
      this_iterator_name :: other_iterators_names ) -> (
    let this_iterator = { value = this_iterator; name = this_iterator_name } in
    match this_arg with
    | Constant cte ->
      let sender, receiver = create_channel () in
      Sender.send sender cte;
      bind_iterator post_level
        { value = receiver; name = "<constant>" }
        this_iterator;
      bind_atom ~order post_level other_args other_iterators
        other_iterators_names
    | Parameter param ->
      bind_iterator post_level
        { value = Parameter.get_receiver param; name = param.name }
        this_iterator;
      bind_atom ~order post_level other_args other_iterators
        other_iterators_names
    | Variable var ->
      let level = Option.get var.level in
      let var_order = Cursor.Level.order level in
      if Cursor.Order.compare var_order order > 0
      then (
        Cursor.Level.add_iterator level this_iterator;
        bind_atom ~order:var_order
          (Cursor.Level.actions level)
          other_args other_iterators other_iterators_names)
      else (
        bind_iterator post_level (Cursor.Level.use_output level) this_iterator;
        bind_atom ~order post_level other_args other_iterators
          other_iterators_names))

let bind_atom post_level args iterator =
  bind_atom ~order:Cursor.Order.parameters post_level args iterator.values
    iterator.names

let rec find_last_binding0 : type a. order:_ -> _ -> a Term.hlist -> _ =
 fun ~order post_level args ->
  match args with
  | [] -> post_level
  | arg :: args -> (
    match arg with
    | Constant _ | Parameter _ -> find_last_binding0 ~order post_level args
    | Variable var ->
      let var = Option.get var.level in
      let var_order = Cursor.Level.order var in
      if Cursor.Order.compare var_order order > 0
      then find_last_binding0 ~order:var_order (Cursor.Level.actions var) args
      else find_last_binding0 ~order post_level args)

let find_last_binding post_level args =
  find_last_binding0 ~order:Cursor.Order.parameters post_level args

let compile_term : 'a Term.t -> 'a Receiver.t with_name = function
  | Constant cte ->
    let sender, receiver = create_channel () in
    Sender.send sender cte;
    { value = receiver; name = "<constant>" }
  | Parameter param ->
    { value = Parameter.get_receiver param; name = param.name }
  | Variable var ->
    let var = Option.get var.level in
    Cursor.Level.use_output var

let rec compile_terms : type a. a Term.hlist -> a Receiver.hlist with_names =
 fun vars ->
  match vars with
  | [] -> { values = []; names = [] }
  | term :: terms ->
    let { value; name } = compile_term term in
    let { values; names } = compile_terms terms in
    { values = value :: values; names = name :: names }

let compile_condition context condition =
  match condition with
  | Where_atom (id, args) ->
    let iterators = Cursor.add_iterator context id in
    bind_atom (Cursor.initial_actions context) args iterators

let compile_filter context filter =
  match filter with
  | Unless_atom (id, args) ->
    let refs = compile_terms args in
    let post_level = find_last_binding (Cursor.initial_actions context) args in
    let r = Cursor.add_naive_binder context id in
    Cursor.add_action post_level (Cursor.unless id r refs)
  | Unless_eq (repr, arg1, arg2) ->
    let ref1 = compile_term arg1 in
    let ref2 = compile_term arg2 in
    let post_level =
      find_last_binding (Cursor.initial_actions context) [arg1; arg2]
    in
    Cursor.add_action post_level (Cursor.unless_eq repr ref1 ref2)
  | User (fn, args) ->
    let refs = compile_terms args in
    let post_level = find_last_binding (Cursor.initial_actions context) args in
    Cursor.add_action post_level (Cursor.filter fn refs)

let rec cursor_call2 :
    type a b.
    name:string ->
    (a Constant.hlist -> b Constant.hlist -> unit) ->
    a Term.hlist ->
    b Term.hlist ->
    Cursor.call =
 fun ~name f xs ys ->
  match xs with
  | [] -> Cursor.create_call (f []) ~name (compile_terms ys)
  | x :: xs ->
    cursor_call2 ~name (fun xs' (x' :: ys) -> f (x' :: xs') ys) xs (x :: ys)

let rec compile_terminator :
    type p a.
    callbacks:_ -> _ -> _ -> p Parameter.hlist -> (p, a) terminator -> a =
 fun ~callbacks context levels parameters terminator ->
  match terminator with
  | Yield output ->
    let output = Option.map compile_terms output in
    let calls =
      List.map
        (function
          | Callback { func; name; args } ->
            Cursor.create_call func ~name (compile_terms args)
          | Callback_with_bindings { func; name; args } ->
            let (Levels vars) = levels in
            cursor_call2 ~name
              (fun level_values arg_values ->
                func (Bindings (vars, level_values)) arg_values)
              (Term.variables vars) args)
        callbacks
    in
    Cursor.With_parameters.create ~calls ?output
      ~parameters:(Parameter.to_senders parameters)
      context
  | Map (terminator, fn) ->
    fn (compile_terminator ~callbacks context levels parameters terminator)

let rec bind_vars : type a. _ -> a Variable.hlist -> unit =
 fun context vars ->
  match vars with
  | [] -> ()
  | var :: vars ->
    let level = Cursor.add_new_level context var.name in
    var.level <- Some level;
    bind_vars context vars

let bind_levels context (Levels vars) = bind_vars context vars

let rec unbind_vars : type a. _ -> a Variable.hlist -> unit =
 fun context vars ->
  match vars with
  | [] -> ()
  | var :: vars ->
    var.level <- None;
    unbind_vars context vars

let unbind_levels context (Levels vars) = unbind_vars context vars

type any_parameter = Any_parameter : _ Parameter.t -> any_parameter
[@@unboxed]

let rec nparams :
    type a.
    (any_parameter, int) Hashtbl.t -> a Parameter.hlist -> int -> string list =
 fun cache parameters pos ->
  match parameters with
  | [] -> []
  | p :: ps ->
    Hashtbl.replace cache (Any_parameter p) pos;
    Parameter.name p :: nparams cache ps (pos + 1)

type any_variable = Any_variable : _ Variable.t -> any_variable [@@unboxed]

let rec nvars :
    type a.
    (any_variable, int) Hashtbl.t -> a Variable.hlist -> int -> string list =
 fun cache variables pos ->
  match variables with
  | [] -> []
  | p :: ps ->
    Hashtbl.replace cache (Any_variable p) pos;
    Variable.name p :: nvars cache ps (pos + 1)

let compile_program parameters
    { conditions; filters; callbacks; terminator; levels } =
  let () =
    let (Levels vars) = levels in
    let table_vars = Hashtbl.create 17 in
    let variables = nvars table_vars vars 0 in
    let table_parameters = Hashtbl.create 17 in
    let parameters = nparams table_parameters parameters 0 in
    let table_table = Hashtbl.create 17 in
    let _, rev_parameters =
      List.fold_left
        (fun (nb, rev_ps) (Where_atom (table, _)) ->
          let uid = Table.Id.uid table in
          if Hashtbl.mem table_table uid
          then nb, rev_ps
          else (
            Hashtbl.replace table_table uid nb;
            nb + 1, Table.Id.name table :: rev_ps))
        (List.length parameters, [])
        conditions
    in
    let parameters = parameters @ List.rev rev_parameters in
    let _, rev_parameters =
      List.fold_left
        (fun (nb, rev_ps) filter ->
          match filter with
          | Unless_eq _ | User _ -> nb, rev_ps
          | Unless_atom (table, _) ->
            let uid = Table.Id.uid table in
            if Hashtbl.mem table_table uid
            then nb, rev_ps
            else (
              Hashtbl.replace table_table uid nb;
              nb + 1, Table.Id.name table :: rev_ps))
        (List.length parameters, [])
        filters
    in
    let parameters = parameters @ List.rev rev_parameters in
    Lang_builder.with_builder ~parameters ~variables
      (fun ~parameters ~variables builder ->
        let table_vars' = Hashtbl.create 17 in
        Hashtbl.iter
          (fun a b -> Hashtbl.replace table_vars' a (List.nth variables b))
          table_vars;
        let table_params' = Hashtbl.create 17 in
        Hashtbl.iter
          (fun a b -> Hashtbl.replace table_params' a (List.nth parameters b))
          table_parameters;
        let table_table' = Hashtbl.create 17 in
        Hashtbl.iter
          (fun a b -> Hashtbl.replace table_table' a (List.nth parameters b))
          table_table;
        let getterm : type a. a Term.t -> Lang_builder.variable =
         fun term ->
          match term with
          | Constant c -> Lang_builder.constant builder c
          | Variable var -> Hashtbl.find table_vars' (Any_variable var)
          | Parameter param -> Hashtbl.find table_params' (Any_parameter param)
        in
        let rec add_lookup :
            type a. Lang_builder.variable -> a Term.hlist -> unit =
         fun Lang_buildervar terms ->
          match terms with
          | [] -> ()
          | Constant c :: terms ->
            let var = Lang_builder.constant builder c in
            add_lookup (Lang_builder.index builder Lang_buildervar var) terms
          | Variable var :: terms ->
            let key = Hashtbl.find table_vars' (Any_variable var) in
            add_lookup (Lang_builder.index builder Lang_buildervar key) terms
          | Parameter param :: terms ->
            let key = Hashtbl.find table_params' (Any_parameter param) in
            add_lookup (Lang_builder.index builder Lang_buildervar key) terms
        in
        let rec add_lookup' :
            type a.
            Lang_builder.variable -> a Term.hlist -> Lang_builder.variable =
         fun Lang_buildervar terms ->
          match terms with
          | [] -> Lang_buildervar
          | term :: terms ->
            let key =
              match term with
              | Constant c -> Lang_builder.constant builder c
              | Variable var -> Hashtbl.find table_vars' (Any_variable var)
              | Parameter param ->
                Hashtbl.find table_params' (Any_parameter param)
            in
            let Lang_buildervar, default =
              match terms with
              | [] -> Lang_builder.map builder Lang_buildervar, Some "true"
              | _ :: _ -> Lang_buildervar, None
            in
            add_lookup'
              (Lang_builder.index' ?default builder Lang_buildervar key)
              terms
        in
        List.iter
          (fun (Where_atom (table, args)) ->
            let Lang_buildervar =
              Hashtbl.find table_table' (Table.Id.uid table)
            in
            add_lookup Lang_buildervar args)
          conditions;
        List.iter
          (fun filter ->
            match filter with
            | Unless_atom (table, args) ->
              let Lang_buildervar =
                Hashtbl.find table_table' (Table.Id.uid table)
              in
              Lang_builder.if' builder (add_lookup' Lang_buildervar args)
            | Unless_eq (_, x, y) ->
              Lang_builder.if' builder
                (Lang_builder.eq builder (getterm x) (getterm y))
            | User _ -> ())
          filters;
        let printc = function
          | Callback { name; args; _ } ->
            Format.eprintf "call %s @[(" name;
            let rec loop : type a. bool -> a Term.hlist -> unit =
             fun first terms ->
              match terms with
              | [] -> ()
              | term :: terms ->
                if not first then Format.eprintf ",@ ";
                let var = getterm term in
                Format.eprintf "%a" Lang_builder.print_variable var;
                loop false terms
            in
            loop true args;
            Format.eprintf ")@]@."
          | Callback_with_bindings { name; args; _ } ->
            Format.eprintf "call %s @[(" name;
            let rec loop : type a. bool -> a Term.hlist -> unit =
             fun first terms ->
              match terms with
              | [] -> ()
              | term :: terms ->
                if not first then Format.eprintf ",@ ";
                let var = getterm term in
                Format.eprintf "%a" Lang_builder.print_variable var;
                loop false terms
            in
            loop true args;
            Format.eprintf ")@]@."
        in
        List.iter printc callbacks;
        let printt : type a b. (a, b) terminator -> unit =
         fun terminator ->
          match terminator with
          | Yield None | Map _ -> ()
          | Yield (Some ts) ->
            Format.eprintf "yield @[(";
            let rec loop : type a. bool -> a Term.hlist -> unit =
             fun first terms ->
              match terms with
              | [] -> ()
              | term :: terms ->
                if not first then Format.eprintf ",@ ";
                let var = getterm term in
                Format.eprintf "%a" Lang_builder.print_variable var;
                loop false terms
            in
            loop true ts;
            Format.eprintf ")@]@."
        in
        printt terminator)
  in
  let context = Cursor.create_context () in
  bind_levels context levels;
  Fun.protect
    ~finally:(fun () -> unbind_levels context levels)
    (fun () ->
      List.iter
        (fun condition -> compile_condition context condition)
        conditions;
      List.iter (fun filter -> compile_filter context filter) filters;
      compile_terminator ~callbacks context levels parameters terminator)

let compile_with_parameters0 ps f =
  let ps = Parameter.list ps in
  let prog = f (Term.parameters ps) in
  compile_program ps prog

let compile_with_parameters ps xs f =
  compile_with_parameters0 ps (fun ps -> foreach xs (fun xs -> f ps xs))

let compile xs f = compile_with_parameters [] xs (fun [] xs -> f xs)
