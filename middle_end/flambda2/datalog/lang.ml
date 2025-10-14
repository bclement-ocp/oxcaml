[@@@warning "-32-34-60-37"]

open! Datalog_imports

module Order : sig
  type t

  val print : Format.formatter -> t -> unit

  val compare : t -> t -> int

  val max : t -> t -> t

  val parameters : t

  val succ : t -> t
end = struct
  type t = int

  let print = Format.pp_print_int

  let compare = Int.compare

  let max = Int.max

  let parameters = -1

  let succ o = o + 1
end

module Variable : sig
  type _ t = private
    { name : string;
      stamp : int
    }

  type any = Any : _ t -> any [@@unboxed]

  val print : Format.formatter -> 'a t -> unit

  val equal : 'a t -> 'b t -> bool

  val hash : 'a t -> int

  val name : 'a t -> string

  val create : string -> 'a t
end = struct
  module T0 = struct
    type _ t =
      { name : string;
        stamp : int
      }

    let print ppf { name; stamp } = Format.fprintf ppf "%s/%d" name stamp

    let hash { stamp; _ } = Hashtbl.hash stamp

    let equal { stamp = stamp1; _ } { stamp = stamp2; _ } =
      Int.equal stamp1 stamp2

    let compare { stamp = stamp1; _ } { stamp = stamp2; _ } =
      Int.compare stamp1 stamp2
  end

  include T0

  type any = Any : _ t -> any [@@unboxed]

  let name { name; _ } = name

  let create =
    let cnt = ref 0 in
    fun () ->
      incr cnt;
      !cnt

  let create name = { name; stamp = create () }
end

type variable = unit Variable.t

module V7 = struct
  type lexpr =
    | Map of variable
    | Meet of variable list
    | Singleton of variable * variable
    | Eq of variable * variable

  let equal_lexpr lin1 lin2 =
    match lin1, lin2 with
    | Map x1, Map x2 -> Variable.equal x1 x2
    | Meet vars1, Meet vars2 ->
      List.length vars1 = List.length vars2
      && List.for_all2 Variable.equal vars1 vars2
    | Singleton (key1, value1), Singleton (key2, value2) ->
      Variable.equal key1 key2 && Variable.equal value1 value2
    | Eq (x1, y1), Eq (x2, y2) -> Variable.equal x1 x2 && Variable.equal y1 y2
    | (Map _ | Meet _ | Singleton _ | Eq _), _ -> false

  let hash_lexpr lin =
    match lin with
    | Map x -> Hashtbl.hash (0, Variable.hash x)
    | Meet vars -> Hashtbl.hash (1, List.map Variable.hash vars)
    | Singleton (key, value) ->
      Hashtbl.hash (2, Variable.hash key, Variable.hash value)
    | Eq (x, y) -> Hashtbl.hash (3, Variable.hash x, Variable.hash y)

  let print_lexpr pp ppf = function
    | Map x -> Format.fprintf ppf "map@ (fun _ -> false) %a" pp x
    | Meet [] -> Format.fprintf ppf "⊥"
    | Meet (_ :: _ as vars) ->
      Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.fprintf ppf " ∨@ ")
        pp ppf vars
    | Singleton (x, y) ->
      Format.fprintf ppf "@[<hov 1>{@ %a ->@ %a@ }@]" pp x pp y
    | Eq (x, y) -> Format.fprintf ppf "equal %a %a" pp x pp y

  type expr =
    | Hole
    | Sum of variable option * (variable option * variable) list * expr
    | Let of variable * lexpr * expr
    | If of variable * expr

  let rec compose e1 e2 =
    match e1 with
    | Hole -> e2
    | Sum (x1, args1, e1) -> Sum (x1, args1, compose e1 e2)
    | Let (x1, lin1, e1) -> Let (x1, lin1, compose e1 e2)
    | If (x1, e1) -> If (x1, compose e1 e2)

  let rec linearize ctx e =
    match e with
    | Hole -> rebuild ctx
    | Sum (x, args, body) ->
      let ctx, args =
        List.fold_left_map
          (fun ctx (x, v) ->
            match origin v with
            | Loop_key | Loop_val -> ctx, (x, v)
            | Parameter | Let_bound ->
              let ctx, v' = dedup_at_this_level ctx v in
              ctx, (x, v'))
          ctx args
      in
      let ctx = push_level ctx in
      let ctx = to_rebuild ctx (Sum_ctx (x, args)) in
      linearize ctx body
    | Let (x, e1, e2) ->
      let ctx = record_var x (Some e1) in
      let ctx = to_rebuild ctx (Let_ctx (x, e1)) in
      (* When rebuilding: introduce copies for each dedup level. *)
      linearize ctx e2
    | If (c, e) ->
      let ctx = to_rebuild ctx (If_ctx c) in
      linearize ctx e

  let rec print_expr pp ppf = function
    | Hole -> Format.fprintf ppf "⬚"
    | Sum (index, [], body) ->
      Format.fprintf ppf "@[<v>@[for %a do@]@;<1 2>@[<v>%a@]@ done@]"
        (Format.pp_print_option ~none:(fun ppf () -> Format.fprintf ppf "_") pp)
        index (print_expr pp) body
    | Sum (index, (_ :: _ as vars), body) ->
      Format.fprintf ppf
        "@[<v>@[<hv>@[for@;\
         <1 2>%a@ in@]@;\
         <1 2>@[%a@]@ do@]@;\
         <1 2>@[<v>%a@]@ done@]"
        (Format.pp_print_option ~none:(fun ppf () -> Format.fprintf ppf "_") pp)
        index
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf " ⨝@ ")
           (fun ppf (x, y) ->
             match x with
             | None -> pp ppf y
             | Some x -> Format.fprintf ppf "(%a : %a)" pp x pp y))
        vars (print_expr pp) body
    | Let (x, def_expr, body) ->
      Format.fprintf ppf "@[<v>@[<hv>let %a = %a@ @]in@ %a@]" pp x
        (print_lexpr pp) def_expr (print_expr pp) body
    | If (x, e) ->
      Format.fprintf ppf "@[<v 2>@[<hv>if %a@ @]then@ %a@]" pp x (print_expr pp)
        e

  type origin =
    | Loop_key
    | Other

  type variable_data =
    { origin : origin;
      order : Order.t
    }

  module OrderMap = Map.Make (Order)

  type prim =
    | Linear of lexpr
    | Call of variable * variable list
    | Index of variable * variable
    | Index_with_default of variable * variable

  let equal_prim prim1 prim2 =
    match prim1, prim2 with
    | Linear lin1, Linear lin2 -> equal_lexpr lin1 lin2
    | Call (fn1, args1), Call (fn2, args2) ->
      Variable.equal fn1 fn2
      && List.length args1 = List.length args2
      && List.for_all2 Variable.equal args1 args2
    | Index (table1, key1), Index (table2, key2) ->
      Variable.equal table1 table2 && Variable.equal key1 key2
    | Index_with_default (table1, key1), Index_with_default (table2, key2) ->
      Variable.equal table1 table2 && Variable.equal key1 key2
    | (Linear _ | Call _ | Index _ | Index_with_default _), _ -> false

  let hash_prim prim =
    match prim with
    | Linear lin -> hash_lexpr lin
    | Call (fn, args) ->
      Hashtbl.hash (0, Variable.hash fn, List.map Variable.hash args)
    | Index (table, key) ->
      Hashtbl.hash (1, Variable.hash table, Variable.hash key)
    | Index_with_default (table, key) ->
      Hashtbl.hash (2, Variable.hash table, Variable.hash key)

  module PrimTable = Hashtbl.Make (struct
    type t = prim

    let equal = equal_prim

    let hash = hash_prim
  end)

  module VarTable = Hashtbl.Make (struct
    type t = Variable.any

    let hash (Any v : t) = Variable.hash v

    let equal (Any v1 : t) (Any v2 : t) = Variable.equal v1 v2
  end)

  type level_data =
    { rev_contexts : expr list;
      conditions : (variable option * variable) list;
      key_var : variable option
    }

  type context =
    { primitives : variable PrimTable.t;
      variables : variable_data VarTable.t;
      mutable levels : level_data OrderMap.t;
      parameters : variable list
    }

  let build context =
    let levels = OrderMap.bindings context.levels in
    let hole =
      List.fold_right
        (fun (_order, level_data) hole ->
          let hole =
            List.fold_left
              (fun hole ctx -> compose ctx hole)
              hole level_data.rev_contexts
          in
          Sum (level_data.key_var, level_data.conditions, hole))
        levels Hole
    in
    Format.eprintf "%a@." (print_expr Variable.print) hole

  let create_context ~parameters ~variables =
    let var_table = VarTable.create 17 in
    let parameters =
      List.map
        (fun name ->
          let var = Variable.create name in
          VarTable.replace var_table (Any var)
            { origin = Other; order = Order.parameters };
          var)
        parameters
    in
    let variables = List.map Variable.create variables in
    let levels =
      OrderMap.singleton Order.parameters
        { rev_contexts = []; conditions = []; key_var = None }
    in
    let _, levels =
      List.fold_left
        (fun (order, levels) variable ->
          let order = Order.succ order in
          VarTable.replace var_table (Any variable) { origin = Loop_key; order };
          ( order,
            OrderMap.add order
              { rev_contexts = []; conditions = []; key_var = Some variable }
              levels ))
        (Order.parameters, levels) variables
    in
    ( { primitives = PrimTable.create 17;
        variables = var_table;
        levels;
        parameters
      },
      variables )

  let get_prim ctx prim = PrimTable.find_opt ctx.primitives prim

  let set_prim ctx prim var = PrimTable.replace ctx.primitives prim var

  let fold_variables f prim acc =
    match prim with
    | Linear (Map x) -> f x acc
    | Linear (Meet vars) -> List.fold_left (fun acc arg -> f arg acc) acc vars
    | Linear (Singleton (key, value)) -> f key (f value acc)
    | Call (fn, args) ->
      List.fold_left (fun acc arg -> f arg acc) (f fn acc) args
    | Index (table, key) -> f table (f key acc)
    | Index_with_default (table, key) -> f table (f key acc)
    | Linear (Eq (x, y)) -> f x (f y acc)

  let get_variable_data ctx var =
    match VarTable.find_opt ctx.variables (Any var) with
    | Some data -> data
    | None -> Misc.fatal_error "nope"

  let create_variable ctx name ~origin ~order =
    let var = Variable.create name in
    VarTable.replace ctx.variables (Any var) { origin; order };
    var

  let constant ctx _ =
    create_variable ctx "cte" ~origin:Other ~order:Order.parameters

  let var_order ctx var =
    let data = get_variable_data ctx var in
    data.order

  let prim_order ctx prim =
    fold_variables
      (fun var acc -> Order.max (var_order ctx var) acc)
      prim Order.parameters

  let update_level ctx f order =
    ctx.levels
      <- OrderMap.update order
           (function
             | None -> assert false | Some level_data -> Some (f level_data))
           ctx.levels

  let add_condition ctx order condition =
    update_level ctx
      (fun level_data ->
        { level_data with conditions = condition :: level_data.conditions })
      order

  let add_context ctx order context =
    update_level ctx
      (fun level_data ->
        { level_data with rev_contexts = context :: level_data.rev_contexts })
      order

  let add_or_create_linear ctx prim =
    match get_prim ctx (Linear prim) with
    | Some var -> var
    | None ->
      let order = prim_order ctx (Linear prim) in
      let var = create_variable ctx "Prim" ~origin:Other ~order in
      add_context ctx order (Let (var, prim, Hole));
      var

  let add_index table key ctx =
    let prim = Index (table, key) in
    match get_prim ctx prim with
    | Some var -> var
    | None -> (
      let key_data = get_variable_data ctx key in
      let table_data = get_variable_data ctx table in
      let order = Order.max key_data.order table_data.order in
      let var =
        create_variable ctx
          (Format.asprintf "%s.%s" (Variable.name table) (Variable.name key))
          ~origin:Other ~order
      in
      set_prim ctx prim var;
      match key_data.origin with
      | Loop_key when Order.compare table_data.order order < 0 ->
        assert (Order.compare order key_data.order = 0);
        add_condition ctx order (Some var, table);
        var
      | Loop_key | Other ->
        let unit =
          create_variable ctx "unit" ~origin:Other ~order:Order.parameters
        in
        let s = add_or_create_linear ctx (Singleton (key, unit)) in
        add_context ctx order (Sum (None, [Some var, table; None, s], Hole));
        var)

  let add_index' ?(default = "default") table key ctx =
    let prim = Index (table, key) in
    match get_prim ctx prim with
    | Some var -> var
    | None -> (
      let prim = Index_with_default (table, key) in
      match get_prim ctx prim with
      | Some var -> var
      | None ->
        let key_data = get_variable_data ctx key in
        let table_data = get_variable_data ctx table in
        let order = Order.max key_data.order table_data.order in
        let var =
          create_variable ctx
            (Format.asprintf "%s[%s]" (Variable.name table) (Variable.name key))
            ~origin:Other ~order
        in
        set_prim ctx prim var;
        let default =
          create_variable ctx default ~origin:Other ~order:Order.parameters
        in
        let ss = add_or_create_linear ctx (Singleton (key, default)) in
        let s = add_or_create_linear ctx (Meet [table; ss]) in
        add_context ctx order (Sum (None, [Some var, s; None, ss], Hole));
        var)

  let map ctx var = add_or_create_linear ctx (Map var)

  let eq ctx var1 var2 = add_or_create_linear ctx (Eq (var1, var2))

  let if' ctx var =
    let var_data = get_variable_data ctx var in
    let order = var_data.order in
    add_context ctx order (If (var, Hole))
end

include V7

type builder = context

let index builder table key = add_index table key builder

let index' ?default builder table key = add_index' ?default table key builder

let with_builder ~parameters ~variables f =
  let builder, variables = create_context ~parameters ~variables in
  f ~parameters:builder.parameters ~variables builder;
  build builder

let print_variable = Variable.print
