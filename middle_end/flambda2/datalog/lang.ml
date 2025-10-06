[@@@warning "-37-34-60-32"]

open Datalog_imports

module Bytecode = struct
  module Iterator = struct
    module T0 = Leapfrog.Join (Trie.Iterator)
    include T0
    include Heterogenous_list.Make (T0)
  end

  type ('t, 'k, 'v) table_cursor =
    't Channel.sender * 'k Trie.Iterator.t * 'v Channel.receiver

  type ('t, 'k, 'v) cursor =
    { senders : 't Sender.hlist;
      iterator : 'k Iterator.t;
      receivers : 'v Receiver.hlist
    }

  let create_dummy () = Obj.magic 0

  type 'a register =
    { name : string;
      mutable value : 'a
    }

  module Register = struct
    module T0 = struct
      type 'a t = 'a register

      let print ppf r = Format.pp_print_string ppf r.name
    end

    include T0
    include Heterogenous_list.Make (T0)

    let print_hlist ?(pp_sep = Format.pp_print_cut) ppf registers =
      let rec loop : type a. Format.formatter -> a hlist -> bool -> unit =
       fun ppf registers first ->
        match registers with
        | [] -> ()
        | register :: registers ->
          if not first then pp_sep ppf ();
          print ppf register;
          loop ppf registers false
      in
      loop ppf registers true

    let set r v = r.value <- v

    let get r = r.value

    let rec get_hlist : type a. a hlist -> a Constant.hlist = function
      | [] -> []
      | r :: rs -> get r :: get_hlist rs

    let rec send : type a. a Sender.hlist -> a hlist -> unit =
     fun senders registers ->
      match senders, registers with
      | [], [] -> ()
      | sender :: senders, register :: registers ->
        Channel.send sender (get register);
        send senders registers

    let rec receive : type a. a Receiver.hlist -> a hlist -> unit =
     fun receivers registers ->
      match receivers, registers with
      | [], [] -> ()
      | receiver :: receivers, register :: registers ->
        set register (Channel.recv receiver);
        receive receivers registers
  end

  type (_, _, _) join =
    | Zero : (nil, 'k, nil) join
    | Cons :
        ('t, 'k, 'v) table_cursor register * ('ts, 'k, 'vs) join
        -> ('t -> 'ts, 'k, 'v -> 'vs) join

  let print_join ppf join =
    let rec print_join :
        type a b c. Format.formatter -> (a, b, c) join -> bool -> unit =
     fun ppf join first ->
      match join with
      | Zero -> ()
      | Cons (r1, j) ->
        if not first then Format.pp_print_space ppf ();
        Register.print ppf r1;
        print_join ppf j false
    in
    print_join ppf join true

  type jump = int

  type naive_bind =
    | Naive_bind :
        ('t, 'k, 'v) table_cursor register * 't register
        -> naive_bind

  type seminaive_bind =
    | Seminaive_bind :
        ('t, 'k, 'v) Trie.is_trie
        * ('t, 'k, 'v) table_cursor register
        * 't register
        * 't register
        * 't register
        -> seminaive_bind

  type instruction =
    | Table_cursor :
        ('t, 'k, 'v) Column.id * ('t, 'k, 'v) table_cursor register
        -> instruction
    | Create_cursor :
        ('t, 'k, 'v) join * ('t, 'k, 'v) cursor register
        -> instruction
    | Bind_cursor : naive_bind list -> instruction
    (* jump if there are seminaive iterations to do, otherwise fall through
       (e.g. if any [current] value is empty)

       Note: [seminaive_init []] (with an empty [seminaive_bind] list) will
       always fall through and never jump! *)
    | Seminaive_init :
        seminaive_bind list register
        * bool register
        * seminaive_bind list
        * jump
        -> instruction
      (* NB: the registers in the [seminaive_bind] list must not have been
         udpated since the call to [seminaive_init] *)
    | Seminaive_next :
        seminaive_bind list register * bool register * jump
        -> instruction
    | Init_cursor : ('t, 'k, 'v) cursor register * jump -> instruction
    | Advance_cursor : ('t, 'k, 'v) cursor register * jump -> instruction
    | Seek_cursor :
        ('t, 'k, 'v) cursor register * 'k Register.t * jump
        -> instruction
    | Read_cursor :
        ('t, 'k, 'v) cursor register * 'k Register.t * 'v Register.hlist
        -> instruction
    | Call :
        ('a Constant.hlist -> 'b) register * 'a Register.hlist * 'b register
        -> instruction
    | Goto : jump -> instruction
    | Exit : instruction

  let print_naive_bind ppf (Naive_bind (c, arg)) =
    Format.fprintf ppf "(%a@ %a)" Register.print c Register.print arg

  let print ppf instruction =
    match instruction with
    | Table_cursor (c, r) ->
      Format.fprintf ppf "table_cursor@ %a,@ %s" Register.print r
        (Column.name c)
    | Create_cursor (j, c) ->
      Format.fprintf ppf "create_cursor@ %a,@ [@[%a@]]" Register.print c
        print_join j
    | Bind_cursor naive_binds ->
      Format.fprintf ppf "bind@ [@[%a@]]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
           print_naive_bind)
        naive_binds
    | Seminaive_init (_, _, _, _) -> Format.fprintf ppf "seminaive_init"
    | Seminaive_next (_, _, _) -> Format.fprintf ppf "seminaive_next"
    | Init_cursor (r, j) ->
      Format.fprintf ppf "init@ %a@ goto %d" Register.print r j
    | Advance_cursor (r, j) ->
      Format.fprintf ppf "advance@ %a@ goto %d" Register.print r j
    | Seek_cursor (c, k, j) ->
      Format.fprintf ppf "seek@ %a@ %a@ goto %d" Register.print c Register.print
        k j
    | Read_cursor (c, k, vs) ->
      Format.fprintf ppf "read@ %a@ [@[%a@]],@ %a" Register.print k
        (Register.print_hlist ~pp_sep:Format.pp_print_space)
        vs Register.print c
    | Call (fn, args, ret) ->
      Format.fprintf ppf "call@ %a,@ %a@ [@[%a@]]" Register.print ret
        Register.print fn
        (Register.print_hlist ~pp_sep:Format.pp_print_space)
        args
    | Goto j -> Format.fprintf ppf "goto %d" j
    | Exit -> Format.pp_print_string ppf "exit"

  let print_array ppf prog =
    Format.fprintf ppf "@[<v>";
    Array.iteri
      (fun idx insn -> Format.fprintf ppf "%6d: @[<2>%a@]@ " idx print insn)
      prog;
    Format.fprintf ppf "@]"

  module Assembler = struct
    type label = jump option ref

    type register_ex = Register : _ register -> register_ex [@@unboxed]

    let print_register_ex ppf (Register r) = Register.print ppf r

    type context =
      { locals : register_ex list;
        params : register_ex list;
        rev_instructions : (unit -> instruction) list
      }

    let empty = { locals = []; params = []; rev_instructions = [] }

    let push instruction context =
      { context with
        rev_instructions = instruction :: context.rev_instructions
      }

    type 'a t = Assembler of (int -> context -> context * int * 'a)
    [@@unboxed]

    let assemble (Assembler f) =
      let context, len, () = f 0 empty in
      let arr =
        Array.of_list (List.rev_map (fun f -> f ()) context.rev_instructions)
      in
      assert (Array.length arr = len);
      List.rev context.params, List.rev context.locals, arr

    let return v = Assembler (fun loc before -> before, loc, v)

    let ( let* ) (Assembler m) f =
      Assembler
        (fun loc before ->
          let before, loc, x = m loc before in
          let (Assembler fx) = f x in
          fx loc before)

    let ( >> ) m1 m2 =
      let* () = m1 in
      m2

    let register name =
      Assembler
        (fun loc before -> before, loc, { name; value = create_dummy () })

    let param name =
      Assembler
        (fun loc before ->
          let r = { name; value = create_dummy () } in
          let before = { before with params = Register r :: before.params } in
          before, loc, r)

    let local name =
      Assembler
        (fun loc before ->
          let register = { name; value = create_dummy () } in
          let before =
            { before with locals = Register register :: before.locals }
          in
          before, loc, register)

    let label _name = Assembler (fun loc before -> before, loc, ref None)

    let resolve lab = Option.get !lab

    let emit (label : label) =
      Assembler
        (fun loc before ->
          assert (Option.is_none !label);
          label := Some loc;
          before, loc, ())

    let late_instruction f =
      Assembler (fun loc before -> push f before, loc + 1, ())

    let instruction f = late_instruction (fun () -> f)

    let table_cursor t r = instruction (Table_cursor (t, r))

    let create_cursor ts r = instruction (Create_cursor (ts, r))

    let bind_cursor c ts = instruction (Bind_cursor [Naive_bind (c, ts)])

    let naive_bind c ts = Naive_bind (c, ts)

    let bind_cursor' naive_binds = instruction (Bind_cursor naive_binds)

    let init_cursor rs lab =
      late_instruction (fun () -> Init_cursor (rs, resolve lab))

    let advance_cursor rs lab =
      late_instruction (fun () -> Advance_cursor (rs, resolve lab))

    let seek_cursor rs k lab =
      late_instruction (fun () -> Seek_cursor (rs, k, resolve lab))

    let read_cursor a b c = instruction (Read_cursor (a, b, c))

    let call fn args ret = instruction (Call (fn, args, ret))

    let goto lab = late_instruction (fun () -> Goto (resolve lab))

    let exit = instruction Exit

    (* ocamlformat produces unreadable code if using [>>] directly, so we use
       lists for readability because those are formatted properly *)
    let rec list = function [] -> return () | x :: xs -> x >> list xs

    let prog_test =
      let module C = Column.Make (struct
        let name = "id"

        let print = Format.pp_print_int
      end) in
      let id1 = C.datalog_column_id in
      let id2 = C.datalog_column_id in
      let* c1 = local "c1" in
      let* ct1 = local "ct1" in
      let* ct2 = local "ct2" in
      let* t1 = param "t1" in
      let* t2 = param "t2" in
      let* k1 = local "k1" in
      let* v1 = local "v1" in
      let* v2 = local "v2" in
      let* f = local "f" in
      let* r = local "r" in
      let* c1_start = label "c1_start" in
      let* c1_end = label "c1_end" in
      list
        [ table_cursor id1 ct1;
          table_cursor id2 ct2;
          create_cursor (Cons (ct1, Cons (ct2, Zero))) c1;
          bind_cursor' [naive_bind ct1 t1; naive_bind ct2 t2];
          init_cursor c1 c1_start;
          goto c1_end;
          emit c1_start;
          read_cursor c1 k1 [v1; v2];
          call f [k1; v1; v2] r;
          advance_cursor c1 c1_start;
          emit c1_end;
          exit ]

    let () =
      let params, locals, prog = assemble prog_test in
      Format.eprintf "@[<v>";
      Format.eprintf "@[<hv 2>params:@ %a@]@ "
        (Format.pp_print_list ~pp_sep:Format.pp_print_space print_register_ex)
        params;
      Format.eprintf "@[<hv 2>locals:@ %a@]@ "
        (Format.pp_print_list ~pp_sep:Format.pp_print_space print_register_ex)
        locals;
      Format.eprintf "%a@]@." print_array prog
  end

  let init : type k. k Iterator.t -> bool =
   fun iterator ->
    Iterator.init iterator;
    match Iterator.current iterator with Some _ -> true | None -> false

  let advance : type k. k Iterator.t -> bool =
   fun iterator ->
    Iterator.advance iterator;
    match Iterator.current iterator with None -> false | Some _ -> true

  let seek : type k. k Iterator.t -> k Register.t -> bool =
   fun iterator register ->
    Iterator.seek iterator (Register.get register);
    match Iterator.current iterator with None -> false | Some _ -> true

  let read : type k. k Iterator.t -> k Register.t -> bool =
   fun iterator register ->
    match Iterator.current iterator with
    | Some key ->
      Register.set register key;
      Iterator.accept iterator;
      true
    | None -> false

  let rec join :
      type a b v.
      (a, b, v) join ->
      a Sender.hlist * b Trie.Iterator.t list * v Receiver.hlist = function
    | Zero -> [], [], []
    | Cons (r, rest) ->
      let trie_sender, iterator, _value_receiver = Register.get r in
      let trie_senders, iterators, receivers = join rest in
      ( trie_sender :: trie_senders,
        iterator :: iterators,
        _value_receiver :: receivers )

  (*  e.g.
   *
   *  for (k1, k2, k3, k4) in (t1 & t2 & t3):
   *    f(k2, k4)
   *
   * ==>
   *
   *  0: create_cursor [id1; id2; id3] c
   *  1: bind_cursor c [t1; t2; t3]
   *  2: init_cursor c 4
   *  3: exit
   *  4: read_cursor c [k1; k2; k3; k4]
   *  5: call f [k2; k4]
   *  6: advance_cursor c 4
   *  7: exit
   *
   * nested version
   *
   * 0: create_cursor [id1_1; id2_1; id3_1] c1
   * 1: create_cursor [id1_2; id2_2; id3_2] c2
   * 2: create_cursor [id1_3; id2_3; id3_3] c3
   * 3: create_cursor [id1_4; id2_4; id3_4] c4
   * 4: bind_cursor c1 [t1; t2; t3]
   * 5: init_cursor c1 7
   * 6: goto 25
   * 7: read_cursor c1 k1 [t1_1; t2_1; t3_1]
   * 8: bind_cursor c2 [t1_1; t2_1; t3_1]
   * 9: init_cursor c2 11
   * 10: goto 24
   * 11: read_cursor c2 k2 [t1_2; t2_2; t3_2]
   * 12: bind_cursor c3 [t1_2; t2_2; t3_2]
   * 13: init_cursor c3 15
   * 14: goto 23
   * 15: read_cursor c3 k3 [t1_3; t2_3; t3_3]
   * 16: bind_cursor c4 [t1_3; t2_3; t3_3]
   * 17: init_cursor c4 19
   * 18: goto 22
   * 19: read_cursor c4 k4 [v1; v2; v3]
   * 20: call f [k2; k4]
   * 21: advance_cursor c4 19
   * 22: advance_cursor c3 15
   * 23: advance_cursor c2 11
   * 24: advance_cursor c1 7
   * 25: exit
   *
   *)

  let evaluate prog =
    try
      let pc = ref 0 in
      while true do
        let instruction = prog.(!pc) in
        incr pc;
        match instruction with
        | Table_cursor (column, r) ->
          let is_trie = Column.is_trie [column] in
          let trie_sender, trie_receiver =
            Channel.create (Trie.empty is_trie)
          in
          let value_sender, _value_receiver =
            Channel.create (create_dummy ())
          in
          let [iterator] =
            Trie.Iterator.create is_trie trie_receiver value_sender
          in
          Register.set r (trie_sender, iterator, _value_receiver)
        | Create_cursor (tables, r) ->
          let senders, iterators, receivers = join tables in
          let iterator = Iterator.create iterators in
          Register.set r { senders; iterator; receivers }
        | Bind_cursor naive_binds ->
          List.iter
            (fun (Naive_bind (cursor, table)) ->
              let send_trie, _, _ = Register.get cursor in
              Channel.send send_trie (Register.get table))
            naive_binds
        | Seminaive_init (r, b, seminaive_binds, j) ->
          let rec loop perform_initial_join seminaive_binds =
            match seminaive_binds with
            | [] -> perform_initial_join
            | Seminaive_bind (is_trie, cursor, previous, diff, current)
              :: seminaive_binds ->
              let previous = Register.get previous in
              let previous_is_empty = Trie.is_empty is_trie previous in
              let diff = Register.get diff in
              let diff_is_empty = Trie.is_empty is_trie diff in
              let perform_initial_join =
                perform_initial_join || (previous_is_empty && not diff_is_empty)
              in
              let send_trie, _, _ = Register.get cursor in
              if previous_is_empty || diff_is_empty
              then Channel.send send_trie (Register.get current)
              else Channel.send send_trie previous;
              loop perform_initial_join seminaive_binds
          in
          let perform_initial_join = loop false seminaive_binds in
          Register.set r seminaive_binds;
          Register.set b false;
          if perform_initial_join then pc := j
        | Seminaive_next (r, b, j) ->
          let rec loop b set_current seminaive_binds =
            match seminaive_binds with
            | [] -> []
            | Seminaive_bind (is_trie, cursor, previous, diff, current)
              :: seminaive_binds ->
              let previous = Register.get previous in
              let previous_is_empty = Trie.is_empty is_trie previous in
              let diff = Register.get diff in
              let diff_is_empty = Trie.is_empty is_trie diff in
              if previous_is_empty || diff_is_empty
              then loop b false seminaive_binds
              else
                let current = Register.get current in
                let send_trie, _, _ = Register.get cursor in
                if set_current
                then (
                  Channel.send send_trie current;
                  loop b false seminaive_binds)
                else (
                  Channel.send send_trie diff;
                  Register.set b true;
                  pc := j;
                  seminaive_binds)
          in
          Register.set r (loop b (Register.get b) (Register.get r))
        | Init_cursor (cursor, j) ->
          let cursor = Register.get cursor in
          if init cursor.iterator then pc := j
        | Advance_cursor (cursor, j) ->
          let cursor = Register.get cursor in
          if advance cursor.iterator then pc := j
        | Seek_cursor (cursor, key_registers, j) ->
          let cursor = Register.get cursor in
          if seek cursor.iterator key_registers then pc := j
        | Read_cursor (cursor, key_register, value_registers) ->
          let cursor = Register.get cursor in
          if read cursor.iterator key_register
          then Register.receive cursor.receivers value_registers
        | Call (fn, args, ret) ->
          let fn = Register.get fn in
          Register.set ret (fn (Register.get_hlist args))
        | Goto j -> pc := j
        | Exit -> raise Exit
      done
    with Exit -> ()
end

module Yipee = struct
  type variable =
    { name : string;
      stamp : int
    }

  let fresh_stamp =
    let cnt = ref 0 in
    fun () ->
      incr cnt;
      !cnt

  let fresh name = { name; stamp = fresh_stamp () }

  let print_variable ppf { name; stamp } = Format.fprintf ppf "%s/%d" name stamp

  type typ =
    | Primitive
    | Box of typ
    | Set of typ
    | Tuple of typ list
    | Function of typ list * typ

  let rec delta_type = function
    | Primitive | Box _ -> Tuple []
    | Set ty ->
      (* TODO: must be a lattice type! *)
      Set ty
    | Tuple typs -> Tuple (List.map delta_type typs)
    | Function (args, ret) ->
      let delta_args = List.map delta_type args in
      let delta_ret = delta_type ret in
      let args' =
        List.concat
          (List.map2 (fun arg delta -> [Box arg; delta]) args delta_args)
      in
      Function (args', delta_ret)

  type pat =
    | Var of variable * typ
    | Tup of pat list
    | Box of pat

  let rec pat_type = function
    | Var (_, ty) -> ty
    | Tup ps -> Tuple (List.map pat_type ps)
    | Box p -> (Box (pat_type p) : typ)

  let rec bind_pat ctx = function
    | Var (x, ty) ->
      let dx = fresh ("d" ^ x.name) in
      Hashtbl.add ctx x.stamp dx;
      Var (dx, delta_type ty)
    | Tup ps -> Tup (List.map (bind_pat ctx) ps)
    | Box p -> Box (bind_pat ctx p)

  let rec bottom_pat ctx = function
    | Var (x, ty) -> Hashtbl.add ctx x.stamp ty
    | Tup ps -> List.iter (bottom_pat ctx) ps
    | Box p -> bottom_pat ctx p

  let rec unbind_pat ctx = function
    | Var (x, _ty) -> Hashtbl.remove ctx x.stamp
    | Tup ps -> List.iter (unbind_pat ctx) ps
    | Box p -> unbind_pat ctx p

  let rec print_pat ppf = function
    | Var (var, _ty) -> print_variable ppf var
    | Tup ps ->
      Format.fprintf ppf "@[(%a)@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           print_pat)
        ps
    | Box p -> Format.fprintf ppf "[%a]" print_pat p

  type term =
    | Var of variable
    | Lam of pat list * term
    | App of term * term
    | Tup of term list
    | Product of term list
    | Prj of int * term
    | Box of term
    | Let of pat * term * term
    | Bot of typ
    | Union of term list
    | Set of typ * term list
    | For of pat list * term * term

  let is_bottom = function
    | Var _ | Lam _ | App _ | Tup _ | Prj _ | Box _ | Let _ | Union _ | Set _
    | For _ | Product _ ->
      false
    | Bot _ -> true

  let rec print_term ppf = function
    | Var var -> print_variable ppf var
    | Lam (pat, term) ->
      Format.fprintf ppf "@[<v 1>(fun @[%a@] ->@ %a)@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space print_pat)
        pat print_term term
    | App (e1, e2) -> Format.fprintf ppf "%a(%a)" print_term e1 print_term e2
    | Tup es ->
      Format.fprintf ppf "@[(%a)@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           print_term)
        es
    | Product es ->
      Format.fprintf ppf "@[(%a)@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf " ×@ ")
           (fun ppf t -> Format.fprintf ppf "(%a)" print_term t))
        es
    | Prj (n, e) -> Format.fprintf ppf "(%a).%d" print_term e n
    | Box term -> Format.fprintf ppf "[%a]" print_term term
    | Let (x, e1, e2) ->
      Format.fprintf ppf "@[<v>let @[[%a]@ = %a@ in@]@ %a@]" print_pat x
        print_term e1 print_term e2
    | Bot _ -> Format.fprintf ppf "⊥"
    | Union es ->
      Format.fprintf ppf "@[<hv>%a@]"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ∨@ ")
           print_term)
        es
    | Set (_, ts) ->
      Format.fprintf ppf "{%a}"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space print_term)
        ts
    | For (x, e1, e2) ->
      Format.fprintf ppf "@[<v 1>for @[%a ∈@ %a@]:@ @[<v>%a@]@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space print_pat)
        x print_term e1 print_term e2

  type context =
    { delta : (int, variable) Hashtbl.t;
      bottom : (int, typ) Hashtbl.t
    }

  let is_bottom = function[@warning "-4"] Bot _ -> true | _ -> false

  let rec phi ctx term =
    match term with
    | Var var -> Var var
    | Lam (x, e) -> Lam (x, phi ctx e)
    | App (e1, e2) -> App (phi ctx e1, phi ctx e2)
    | Tup es -> Tup (List.map (phi ctx) es)
    | Product es -> Product (List.map (phi ctx) es)
    | Prj (n, e) -> Prj (n, phi ctx e)
    | Box e -> Box (Tup [phi ctx e; delta ctx e])
    | Let (x, e1, e2) ->
      let e1 = phi ctx e1 in
      let dx = bind_pat ctx.delta x in
      let e = Let (Tup [x; dx], e1, phi ctx e2) in
      unbind_pat ctx.delta x;
      e
    | Bot ty -> Bot ty
    | Union es -> Union (List.map (phi ctx) es)
    | Set (ty, es) -> Set (ty, List.map (phi ctx) es)
    | For (x, e1, e2) ->
      let e1 = phi ctx e1 in
      List.iter (bottom_pat ctx.bottom) x;
      let e2 = phi ctx e2 in
      List.iter (unbind_pat ctx.bottom) x;
      For (x, e1, e2)

  and delta ctx term =
    match term with
    | Var var -> (
      try Var (Hashtbl.find ctx.delta var.stamp)
      with Not_found -> Bot (Hashtbl.find ctx.bottom var.stamp))
    | Lam (x, e) -> (
      let dx = List.map (bind_pat ctx.delta) x in
      let de = delta ctx e in
      List.iter (unbind_pat ctx.delta) x;
      let x =
        List.concat (List.map2 (fun x dx : pat list -> [Box x; dx]) x dx)
      in
      match[@warning "-4"] de with
      | Bot ty -> Bot (Function (List.map pat_type x, ty))
      | de -> Lam (x, de))
    | App (e1, e2) -> (
      let de1 = delta ctx e1 in
      let de2 = delta ctx e2 in
      let e2 = phi ctx e2 in
      match[@warning "-4"] de1, de2 with
      | Bot (Function (_, rty)), Bot _ -> Bot rty
      | _ -> App (App (de1, Box e2), de2))
    | Tup es ->
      let es = List.map (delta ctx) es in
      if List.for_all is_bottom es
      then
        Bot
          (Tuple
             (List.map
                (function[@warning "-4"] Bot ty -> ty | _ -> assert false)
                es))
      else Tup es
    | Product es ->
      let es_des = List.map (fun e -> phi ctx e, delta ctx e) es in
      let rec bilinear = function
        | [] -> []
        | (e, de) :: es_des ->
          (* Δ(e × es) = Δ(e) × es + (e + Δe) × Δ(es) *)
          (de :: List.map fst es_des)
          :: List.map (fun es -> Union [e; de] :: es) (bilinear es_des)
      in
      Union (List.map (fun es -> Product es) (bilinear es_des))
    | Prj (n, e) -> (
      match[@warning "-4"] delta ctx e with
      | Bot (Tuple tys) -> Bot (List.nth tys n)
      | de -> Prj (n, de))
    | Box _ -> Tup []
    | Let (x, e1, e2) -> (
      let e1 = phi ctx e1 in
      let dx = bind_pat ctx.delta x in
      let de2 = delta ctx e2 in
      unbind_pat ctx.delta x;
      match[@warning "-4"] de2 with
      | Bot ty -> Bot ty
      | de2 -> Let (Tup [x; dx], e1, de2))
    | Bot ty -> Bot (delta_type ty)
    | Union es -> (
      let des = List.map (delta ctx) es in
      let bot, not_bot = List.partition is_bottom des in
      match[@warning "-4"] bot, not_bot with
      | Bot ty :: _, [] -> Bot ty
      | _ -> Union not_bot)
    | Set (ty, _) -> Bot (Set ty)
    | For (x, e0, f) -> (
      let de = delta ctx e0 in
      let e = phi ctx e0 in
      List.iter (bottom_pat ctx.bottom) x;
      let df = delta ctx f in
      let f = phi ctx f in
      List.iter (unbind_pat ctx.bottom) x;
      match[@warning "-4"] df, de with
      | Bot ty, Bot _ -> Bot ty
      | Bot _, de -> For (x, de, f)
      | df, Bot _ -> For (x, e, df)
      | df, de ->
        (* Better factorization *)
        let un =
          match[@warning "-4"] e0 with
          | Product es ->
            Product (List.map (fun e -> Union [phi ctx e; delta ctx e]) es)
          | _ -> Union [e; de]
        in
        Union [For (x, de, f); For (x, un, df)])

  let create_context () =
    { delta = Hashtbl.create 17; bottom = Hashtbl.create 17 }

  let termite b =
    let t = fresh "t" in
    let s = fresh "s" in
    let u = fresh "u" in
    let v = fresh "v" in
    let x = fresh "x" in
    let y = fresh "y" in
    let z = fresh "z" in
    let w = fresh "w" in
    let p = fresh "p" in
    if b
    then
      Lam
        ( [ Var (t, Set Primitive);
            Var (s, Set Primitive);
            Var (u, Set Primitive);
            Var (v, Set Primitive) ],
          For
            ( [Var (x, Primitive)],
              Var t,
              For
                ( [Var (y, Primitive)],
                  Var s,
                  For
                    ( [Var (z, Primitive)],
                      Var u,
                      For
                        ( [Var (w, Primitive)],
                          Var v,
                          Tup [Var x; Var y; Var z; Var w] ) ) ) ) )
    else
      Lam
        ( [ Var (t, Set Primitive);
            Var (s, Set Primitive);
            Var (u, Set Primitive);
            Var (v, Set Primitive) ],
          Let
            ( Var (p, Primitive),
              Box (Product [Var t; Var s; Var u]),
              For
                ( [Var (x, Primitive); Var (y, Primitive); Var (z, Primitive)],
                  Var p,
                  For
                    ( [Var (w, Primitive)],
                      Var v,
                      Tup [Var x; Var y; Var z; Var w] ) ) ) )

  let diff_termite b =
    let ctx = create_context () in
    delta ctx (termite b)

  let nestite =
    let t = fresh "t" in
    let s = fresh "s" in
    let x = fresh "x" in
    let y = fresh "y" in
    let z = fresh "z" in
    Lam
      ( [Var (t, Set (Set Primitive)); Var (s, Set Primitive)],
        For
          ( [Var (x, Set Primitive)],
            Var t,
            For
              ( [Var (y, Primitive)],
                Var x,
                For ([Var (z, Primitive)], Var s, Var y) ) ) )

  let diff_nestite =
    let ctx = create_context () in
    delta ctx nestite

  let print_termite b =
    Format.eprintf "%a@." print_term (termite b);
    Format.eprintf "%a@." print_term (diff_termite b)

  let () =
    Format.eprintf "A:@.";
    print_termite true;
    Format.eprintf "B:@.";
    print_termite false

  let () =
    Format.eprintf "%a@." print_term nestite;
    Format.eprintf "%a@." print_term diff_nestite
end

let dummy : unit = ()
