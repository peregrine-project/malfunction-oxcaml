open Lambda

open Malfunction
open Malfunction_parser
open Malfunction_compat

(* List.map, but guarantees left-to-right evaluation *)
let rec lrmap f = function
| [] -> []
| (x :: xs) -> let r = f x in r :: lrmap f xs

let lprim p args = Lprim (p, args, loc_none)
let lbind n exp body =
  let id = fresh n in
  llet id exp (body (Lvar id))

(* Enforce left-to-right evaluation order by introducing 'let' bindings *)

let rec reorder = function
| Mvar _
| Mnum _
| Mstring _
| Mglobal _ as t -> `Pure, t

| Mlambda (params, body) ->
  `Pure, Mlambda (params, snd (reorder body))

| Mapply (f, xs) ->
   reorder_sub `Impure (fun ev ->
     let f = ev f in
     let xs = lrmap ev xs in
     Mapply (f, xs))

| Mlet (bindings, body) ->
   let bindings = reorder_bindings bindings in
   let _, body = reorder body in
   `Impure, Mlet (bindings, body)

| Mswitch (e, cases) ->
   `Impure, Mswitch (snd (reorder e), List.map (fun (c, e) -> c, snd (reorder e)) cases)

| Mnumop1(op, ty, t) ->
   reorder_sub `Pure (fun ev ->
     Mnumop1(op, ty, ev t))

| Mnumop2(op, ty, t1, t2) ->
   reorder_sub `Pure (fun ev ->
     let t1 = ev t1 in
     let t2 = ev t2 in
     Mnumop2(op, ty, t1, t2))

| Mconvert(src, dst, t) -> 
   reorder_sub `Pure (fun ev ->
     Mconvert(src, dst, ev t))

| Mvecnew(ty, len, def) ->
   reorder_sub `Pure (fun ev ->
     let len = ev len in
     let def = ev def in
     Mvecnew(ty, len, def))

| Mvecget(ty, vec, idx) ->
   reorder_sub `Impure (fun ev ->
     let vec = ev vec in
     let idx = ev idx in
     Mvecget(ty, vec, idx))

| Mvecset(ty, vec, idx, v) ->
   reorder_sub `Impure (fun ev ->
     let vec = ev vec in
     let idx = ev idx in
     let v = ev v in
     Mvecset(ty, vec, idx, v))

| Mveclen(ty, vec) ->
   reorder_sub `Pure (fun ev ->
     let vec = ev vec in
     Mveclen(ty, vec))

| Mblock (n, ts) ->
   reorder_sub `Pure (fun ev ->
     Mblock(n, lrmap ev ts))

| Mfield (n, t) ->
   reorder_sub `Impure (fun ev ->
     Mfield (n, ev t))

| Mlazy e ->
  `Pure, Mlazy (snd (reorder e))

| Mforce e ->
   reorder_sub `Impure (fun ev ->
     Mforce (ev e))

and reorder_bindings bindings =
  bindings
  |> lrmap (function
    | `Unnamed t -> `Unnamed (snd (reorder t))
    | `Named (v, t) -> `Named (v, snd (reorder t))
    | `Recursive _ as ts -> ts (* must be functions *))

and reorder_sub p f =
  let bindings = ref [] in
  let r = f (fun e ->
    match reorder e with
    | `Pure, e -> e
    | `Impure, e ->
       let id = fresh "tmp" in
       bindings := (`Named (id, e)) :: !bindings;
       Mvar id) in
  match List.rev !bindings with
  | [] -> p, r
  | bindings -> `Impure, (Mlet (bindings, r))

module IntSwitch = struct

  (* Convert a list of possibly-overlapping intervals to a list of disjoint intervals *)

  type action = int (* lower numbers more important *)

  (* cases is a sorted list
     cases that begin lower appear first
     when two cases begin together, more important appears first *)

  type case = int * int * action (* start position, end position, priority *)
  type cases = case list (* sorted by start position then priority *)

  (* the inactive list is a list of (endpoint, priority) pairs representing
     intervals that we are currently inside, but are overridden by a more important one.
     subsequent elements of the list have strictly higher priorities and strictly later endpoints *)
  type inactive = (int * action) list

  let rec insert_inactive max act = function
    | [] -> [(max, act)]
    | (max', act') as i' :: rest when act' < act ->
       (* this interval should appear before the new one *)
       i' ::
         (if max' <= max then
             (* new interval will never be active *)
             rest
          else
             insert_inactive max act rest)

    | (max', act') :: rest when max' <= max ->
       assert (act < act');
       (* this interval will is contained by the new one, so never becomes active *)
       insert_inactive max act rest

    | ov ->
       (* new interval both more important and ends sooner, so prepend *)
       (max, act) :: ov

  type state =
    | Hole (* not currently in any interval *)
    | Interval of (* in an interval... *)
      int (* since this position *)
      * int (* until here *)
      * action (* with this action *)
      * inactive (* overriding these inactive intervals *)

  let state_suc = function
    | Hole -> failwith "state_suc of Hole undefined"
    | Interval (_, _, _, []) -> Hole
    | Interval (_, s_max, _, (max', act') :: rest) ->
       assert (s_max < max');
       (* can compute s_max + 1 without overflow, because inactive interval ends later *)
       Interval (s_max + 1, max', act', rest)

  type result = case list (* may have duplicate actions, disjoint, sorted by position *)
  let rec to_disjoint_intervals c_state (c_cases : cases) : result =
    match c_state, c_cases with
    | Hole, [] -> []

    | Hole, ((min, max, act) :: cases) ->
       to_disjoint_intervals (Interval (min, max, act, [])) cases

    | Interval (entered, max, act, _) as state, [] ->
       (entered, max, act) :: to_disjoint_intervals (state_suc state) []

    | Interval (s_entered, s_max, s_act, _) as state,
      (((min, _max, _act) :: _) as cases) when s_max < min ->
       (* active interval ends before this case begins *)
       (s_entered, s_max, s_act) :: to_disjoint_intervals (state_suc state) cases

    (* below here, we can assume min <= i.s_max: active interval overlaps current case *)
    | Interval (s_entered, s_max, s_act, s_inactive), ((_min, max, act) :: cases) when s_act < act ->
       (* no change to active interval, but this case may become an inactive one *)
       to_disjoint_intervals (Interval (s_entered, s_max, s_act, insert_inactive max act s_inactive)) cases

    | Interval (s_entered, s_max, s_act, s_inactive), ((min, max, act) :: cases) ->
       (* new active interval, so old one becomes inactive *)
       assert (s_entered <= min); assert (min <= s_max); assert (act < s_act);
       let r =
         if s_entered = min then
           (* old interval was not active long enough to produce output *)
           []
         else
           [(s_entered, min - 1, s_act)] in
       r @ to_disjoint_intervals
         (Interval (min, max, act, insert_inactive s_max s_act s_inactive)) cases


  (* unfortunately, this is not exposed from matching.ml, so copy-paste *)
  module Switcher = Switch.Make (struct
    type primitive = Lambda.primitive
    type loc = Lambda.scoped_location
    type arg = Lambda.lambda
    type test = Lambda.lambda
    type act = Lambda.lambda
    type layout = Lambda.layout

    let eqint = pint_cmp int_ty Ceq
    let neint = pint_cmp int_ty Cne
    let leint = pint_cmp int_ty Cle
    let ltint = pint_cmp int_ty Clt
    let geint = pint_cmp int_ty Cge
    let gtint = pint_cmp int_ty Cgt

    let make_is_nonzero loc arg =
      (* https://github.com/ocaml/ocaml/pull/10681 *)
      Lprim (neint, [arg; lconst_int 0], loc)

    let arg_as_test (arg : arg) : test = arg

    let make_prim loc p args = Lprim (p, args, loc)
    let make_offset loc arg n = match n with
    | 0 -> arg
    | _ -> Lprim (pint_binop int_ty Add, [arg; lconst_int n], loc)

    let bind arg body =
      let newvar,newarg = match arg with
      | Lvar v -> v,arg
      | _      ->
          let newvar = fresh "switcher" in
          newvar,Lvar newvar in
      (* switch.ml only binds integer arguments *)
      bind_with_layout Alias (newvar, duid, Lambda.layout_int) arg (body newarg)
    let make_const _loc i = lconst_int i
    let make_isout loc h arg = Lprim (Pisout, [h ; arg], loc)
    let make_isin loc h arg = Lprim (Pnot, [make_isout loc h arg], loc)
    let make_if kind cond ifso ifnot = Lifthenelse (cond, ifso, ifnot, kind)
    let make_switch loc kind arg cases acts =
      let l = ref [] in
      for i = Array.length cases-1 downto 0 do
        l := (i,acts.(cases.(i))) ::  !l
      done ;
      Lswitch (arg,
        {sw_numconsts = Array.length cases ; sw_consts = !l ;
         sw_numblocks = 0 ; sw_blocks =  []  ;
         sw_failaction = None}, loc, kind)
    let make_catch kind d =
      match d with
      | Lstaticraise (i, []) -> i, (fun e -> e)
      | _ ->
         let i = next_raise_count () in
         i, fun e -> Lstaticcatch(e, (i, []), d, Same_region, kind)
    let make_exit i = Lstaticraise (i,[])
  end)

  let compile_int_switch scr overlapped_cases =
    assert (overlapped_cases <> []);
    let actions = Array.of_list (overlapped_cases |> List.map snd) in
    let cases = overlapped_cases
      |> List.mapi (fun idx (`Intrange (min, max), _) -> (min, max, idx))
      |> List.stable_sort (fun (min, _max, _idx) (min', _max', _idx') -> compare min min')
      |> to_disjoint_intervals Hole in
    let occurrences = Array.make (Array.length actions) 0 in
    let rec count_occurrences = function
      | [] -> assert false
      | [(_min, _max, act)] ->
         occurrences.(act) <- occurrences.(act) + 1
      | (_min, max, act) :: (((min', _max', _act') :: _) as rest) ->
         occurrences.(act) <- occurrences.(act) + 1;
         begin if max + 1 <> min' then
           (* When the interval list contains a hole, jump tables generated by
              switch.ml may contain spurious references to action 0.
              See PR#6805 *)
           occurrences.(0) <- occurrences.(0) + 1
         end;
         count_occurrences rest in
    count_occurrences cases;
    let open Switch in
    let store (*: Lambda.lambda t_store*) =
      { act_get = (fun () ->
          Array.copy actions);
        act_get_shared = (fun () ->
          actions |> Array.mapi (fun i act ->
            if occurrences.(i) > 1 then Shared act else Single act));
        act_store = (fun _ -> failwith "store unimplemented");
        act_store_shared = (fun _ -> failwith "store_shared unimplemented") } in
    let cases = Array.of_list cases in
    let (low, _, _) = cases.(0) and (_, high, _) = cases.(Array.length cases - 1) in
    Switcher.zyva loc_none layout (low, high) scr cases store
end

type global_value =
  | Glob_val of lambda
  | Glob_prim of Lambda.external_call_description
  | Identity

let lookup env v =
  let open Types in
  let open Primitive in
  let (path, descr, _) =
    try
      let (p, d, _) = Env.lookup_value ~loc:Location.none (*parse_loc loc*) v env in
      (p, d, ())
    with Not_found ->
      let rec try_stdlib = let open Longident in function
        | Lident s -> Ldot (Lident "Stdlib", s)
        | Ldot (id, s) -> Ldot (try_stdlib id, s)
        | Lapply _ as l -> l in
      try
        let (p, d, _) = Env.lookup_value ~loc:Location.none (try_stdlib v) env in
        (p, d, ())
      with Not_found ->
        failwith ("global not found: " ^ String.concat "." (Longident.flatten v)) in
  match descr.val_kind with
  | Val_reg _ -> Glob_val (transl_value_path loc_none env path)
  | Val_prim(p) ->
     (match p.prim_name with
     | "%equal" ->
        Glob_prim (simple_prim ~name:"caml_equal" ~arity:2 ~alloc:true)
     | "%compare" ->
        Glob_prim (simple_prim ~name:"caml_compare" ~arity:2 ~alloc:true)
     | "%identity" ->
        Identity
     | s when s.[0] = '%' ->
        failwith ("unimplemented primitive " ^ p.prim_name);
     | _ ->
        Glob_prim (external_call_of_primitive p))
  | _ -> failwith "unexpected kind of value"


let identity_to_lambda args =
  match args with
  | [] ->
     let param = fresh "prim" in
     lfunction [param] (Lvar param)
  | [x] -> x
  | fn :: args -> lapply fn args

let builtin env path args =
  let p = match path with
    | path1 :: pathrest ->
       List.fold_left (fun id s -> Longident.Ldot (id, s))
         (Longident.Lident path1) pathrest
    | _ -> assert false in
  match lookup env p with
  | Glob_val v ->
     lapply v args
  | Glob_prim p ->
     assert (p.prim_arity = List.length args);
     lprim (Pccall p) args
  | Identity ->
     identity_to_lambda args


let global_to_lambda = function
  | Glob_val v -> v
  | Glob_prim p ->
     (* Eta-expand this primitive. See translprim.ml. *)
     let rec make_params n =
       if n <= 0 then []
       else fresh "prim" :: make_params (n-1) in
     let params = make_params p.prim_arity in
     let body = lprim (Pccall p) (List.map (fun x -> Lvar x) params) in
     lfunction params body
  | Identity -> identity_to_lambda []

let rec to_lambda env = function
  | Mvar v ->
     Lvar v
  | Mlambda (params, e) ->
     lfunction params (to_lambda env e)
  | Mapply (fn, args) ->
     let ap_func fn = lapply fn (List.map (to_lambda env) args) in
     (match fn with
     | Mglobal v ->
        (match lookup env v with
        | Glob_prim p when p.prim_arity = List.length args ->
           lprim (Pccall p) (List.map (to_lambda env) args)
        | Identity -> identity_to_lambda (List.map (to_lambda env) args)
        | g -> ap_func (global_to_lambda g))
     | fn ->
        ap_func (to_lambda env fn))
  | Mlet (bindings, body) ->
     bindings_to_lambda env bindings (to_lambda env body)
  | Mnum (`Int n) ->
     lconst_int n
  | Mnum (`Int32 n) ->
     Lconst (Const_base (Typedtree.Const_int32 n))
  | Mnum (`Int64 n) ->
     Lconst (Const_base (Typedtree.Const_int64 n))
  | Mnum (`Bigint n) ->
     (match Z.to_int n with
     | n' ->
        assert (Obj.repr n = Obj.repr n');
        lconst_int n'
     | exception Z.Overflow ->
        builtin env ["Z"; "of_string"] [Lconst (Const_immstring (Z.to_string n))])
  | Mnum (`Float64 f) ->
     Lconst (Const_base (Typedtree.Const_float (string_of_float f)))
  | Mstring s ->
     Lconst (Const_immstring s)
  | Mglobal v ->
     global_to_lambda (lookup env v)
  | Mswitch (scr, cases) ->
     let scr = to_lambda env scr in
     let rec flatten acc = function
       | ([], _) :: _ -> assert false
       | ([sel], e) :: rest -> flatten ((sel, to_lambda env e) :: acc) rest
       | (sels, e) :: rest ->
          let i = next_raise_count () in
          let cases = List.map (fun s -> s, Lstaticraise(i, [])) sels in
          lstaticcatch (flatten (cases @ acc) rest) i (to_lambda env e)
       | [] ->
          let rec partition (ints, tags, deftag) = function
            | [] -> (List.rev ints, List.rev tags, deftag)
            | (`Tag _, _) as c :: cases -> partition (ints, c :: tags, deftag) cases
            | (`Deftag, _) as c :: cases -> partition (ints, tags, Some c) cases
            | (`Intrange _, _) as c :: cases -> partition (c :: ints, tags, deftag) cases in
          let (intcases, tagcases, deftag) = partition ([],[],None) (List.rev acc) in
          lbind "switch" scr (fun scr ->
            let tagswitch = match tagcases, deftag with
              | [], None -> None
              | [_,e], None | [], Some (_, e) -> Some e
              | tags, def ->
                 let numtags = match def with
                   | Some _ -> (max_tag :> int)
                   | None -> 1 + List.fold_left (fun s (`Tag i, _) -> max s (i :> int)) (-1) tags in
                 Some (lswitch scr {
                   sw_numconsts = 0; sw_consts = []; sw_numblocks = numtags;
                   sw_blocks = List.map (fun (`Tag i, e) -> i, e) tags;
                   sw_failaction = match def with None -> None | Some (`Deftag,e) -> Some e
                 }) in
            let intswitch = match intcases with
              | [] -> None
              | [_,e] -> Some e
              | ints -> Some (IntSwitch.compile_int_switch scr ints) in
            match intswitch, tagswitch with
            | None, None -> assert false
            | None, Some e | Some e, None -> e
            | Some eint, Some etag ->
               lifthenelse (lprim pisint [scr]) eint etag) in
     flatten [] cases
  | Mnumop1 (op, ty, e) ->
     let e = to_lambda env e in
     let ones32 = Const_base (Typedtree.Const_int32 (Int32.of_int (-1))) in
     let ones64 = Const_base (Typedtree.Const_int64 (Int64.of_int (-1))) in
     let code = match op, ty with
       | `Neg, `Int -> lprim (pint_unop int_ty Neg) [e]
       | `Neg, `Int32 -> lprim (pint_unop int32_ty Neg) [e]
       | `Neg, `Int64 -> lprim (pint_unop int64_ty Neg) [e]
       | `Neg, `Bigint -> builtin env ["Z"; "neg"] [e]
       | `Neg, `Float64 -> lprim (pfloat_unop Neg) [e]
       | `Not, `Int -> lprim Pnot [e]
       | `Not, `Int32 ->
          lprim (pint_binop int32_ty Xor) [e; Lconst ones32]
       | `Not, `Int64 ->
          lprim (pint_binop int64_ty Xor) [e; Lconst ones64]
       | `Not, `Bigint -> builtin env ["Z"; "lognot"] [e]
       | `Not, `Float64 -> assert false in
     code
  | Mnumop2 (op, ((`Int|`Int32|`Int64) as ty), e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let t = match ty with
       | `Int -> int_ty | `Int32 -> int32_ty | `Int64 -> int64_ty in
     let prim = match op with
       | `Add -> pint_binop t Add | `Sub -> pint_binop t Sub
       | `Mul -> pint_binop t Mul
       | `Div -> pint_binop t (Div Safe) | `Mod -> pint_binop t (Mod Safe)
       | `And -> pint_binop t And | `Or -> pint_binop t Or
       | `Xor -> pint_binop t Xor
       | `Lsl -> pint_shift t Lsl | `Lsr -> pint_shift t Lsr
       | `Asr -> pint_shift t Asr
       | `Lt -> pint_cmp t Clt | `Gt -> pint_cmp t Cgt
       | `Lte -> pint_cmp t Cle | `Gte -> pint_cmp t Cge
       | `Eq -> pint_cmp t Ceq in
     lprim prim [e1; e2]
  | Mnumop2 (op, `Bigint, e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let fn = match op with
       | `Add -> "add" | `Sub -> "sub"
       | `Mul -> "mul" | `Div -> "div" | `Mod -> "rem"
       | `And -> "logand" | `Or -> "logor" | `Xor -> "logxor"
       | `Lsl -> "shift_left" | `Lsr -> "shift_right" | `Asr -> "shift_right"
       | `Lt -> "lt" | `Gt -> "gt"
       | `Lte -> "leq" | `Gte -> "geq" | `Eq -> "equal" in
     builtin env ["Z"; fn] [e1; e2]
  | Mnumop2 (op, `Float64, e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     begin match op with
     | #binary_bitwise_op -> assert false
     | `Add -> lprim (pfloat_binop Add) [e1; e2]
     | `Sub -> lprim (pfloat_binop Sub) [e1; e2]
     | `Mul -> lprim (pfloat_binop Mul) [e1; e2]
     | `Div -> lprim (pfloat_binop Div) [e1; e2]
     | `Mod -> builtin env ["Stdlib"; "mod_float"] [e1; e2]
     | #binary_comparison as op ->
        let cmp : Scalar.Float_comparison.t =
          match op with
          | `Lt -> CFlt
          | `Gt -> CFgt
          | `Lte -> CFle
          | `Gte -> CFge
          | `Eq -> CFeq
        in
        lprim (pfloat_cmp cmp) [e1; e2]
     end
  | Mconvert (src, dst, e) ->
     let e = to_lambda env e in
     begin match src, dst with
       | `Bigint, `Bigint
       | `Int, `Int
       | `Int32, `Int32
       | `Int64, `Int64
       | `Float64, `Float64 -> e
       | `Bigint, ((`Int|`Int32|`Int64) as dst) ->
          (* Zarith raises exceptions on overflow, but we truncate conversions. Not fast. *)
          let width = match dst with 
            | `Int -> Sys.word_size - 1
            | `Int32 -> 32
            | `Int64 -> 64 in
          let range = Z.(shift_left (of_int 1) width) in
          let truncated =
            lbind "range"
             (builtin env ["Z"; "of_string"] [Lconst (Const_immstring (Z.to_string range))])
             (fun range ->
               lbind "masked"
                 (builtin env ["Z"; "logand"] [e;
                      builtin env ["Z"; "sub"] [range;
                                                lconst_int 1]])
                 (fun masked ->
                   lifthenelse (builtin env ["Z"; "testbit"]
                                  [masked; lconst_int (width - 1)])
                                (builtin env ["Z"; "sub"] [masked; range])
                                masked)) in
          let fn = match dst with
            | `Int -> "to_int"
            | `Int32 -> "to_int32"
            | `Int64 -> "to_int64" in
          builtin env ["Z"; fn] [truncated]
       | ((`Int|`Int32|`Int64) as src), `Bigint ->
          let fn = match src with
            | `Int -> "of_int"
            | `Int32 -> "of_int32"
            | `Int64 -> "of_int64" in
          builtin env ["Z"; fn] [e]
       | `Int, `Int32 ->
          lprim (pcast ~src:(Scalar.integral int_ty) ~dst:(Scalar.integral int32_ty)) [e]
       | `Int, `Int64 ->
          lprim (pcast ~src:(Scalar.integral int_ty) ~dst:(Scalar.integral int64_ty)) [e]
       | `Int32, `Int ->
          lprim (pcast ~src:(Scalar.integral int32_ty) ~dst:(Scalar.integral int_ty)) [e]
       | `Int64, `Int ->
          lprim (pcast ~src:(Scalar.integral int64_ty) ~dst:(Scalar.integral int_ty)) [e]
       | `Int32, `Int64 ->
          lprim (pcast ~src:(Scalar.integral int32_ty) ~dst:(Scalar.integral int64_ty)) [e]
       | `Int64, `Int32 ->
          lprim (pcast ~src:(Scalar.integral int64_ty) ~dst:(Scalar.integral int32_ty)) [e]
       | `Int, `Float64 ->
          lprim (pcast ~src:(Scalar.integral int_ty) ~dst:(Scalar.floating float_ty)) [e]
       | `Int32, `Float64 ->
          builtin env ["Int32"; "to_float"] [e]
       | `Int64, `Float64 ->
          builtin env ["Int64"; "to_float"] [e]
       | `Bigint, `Float64 ->
          builtin env ["Z"; "to_float"] [e]
       (* FIXME: error handling on overflow *)
       | `Float64, `Int ->
          lprim (pcast ~src:(Scalar.floating float_ty) ~dst:(Scalar.integral int_ty)) [e]
       | `Float64, `Int32 ->
          builtin env ["Int32"; "of_float"] [e]
       | `Float64, `Int64 ->
          builtin env ["Int64"; "of_float"] [e]
       | `Float64, `Bigint ->
          builtin env ["Z"; "of_float"] [e]
     end
  | Mvecnew (`Array, len, def) ->
     builtin env ["Array"; "make"] [to_lambda env len; to_lambda env def]
  | Mvecnew (`Bytevec, len, def) ->
     builtin env ["String"; "make"] [to_lambda env len; to_lambda env def]
  | Mvecget (ty, vec, idx) ->
     let prim = match ty with
       | `Array -> Parrayrefs (Paddrarray_ref, Ptagged_int_index, Mutable)
       | `Bytevec -> Pbytesrefs
(*       | `Floatvec -> Parrayrefs Pfloatarray *) in
     lprim prim [to_lambda env vec; to_lambda env idx]
  | Mvecset (ty, vec, idx, v) ->
     let prim = match ty with
       | `Array -> Parraysets (Paddrarray_set modify_heap, Ptagged_int_index)
       | `Bytevec -> Pbytessets
(*       | `Floatvec -> Parraysets Pfloatarray *) in
     lprim prim [to_lambda env vec; to_lambda env idx; to_lambda env v]
  | Mveclen (ty, vec) ->
     let prim = match ty with
       | `Array -> Parraylength Paddrarray
       | `Bytevec -> Pbyteslength
(*       | `Floatvec -> Parraylength Pfloatarray *) in
     lprim prim [to_lambda env vec]
  | Mblock (tag, vals) ->
     lprim (pmakeblock tag Immutable) (List.map (to_lambda env) vals)
  | Mfield (idx, e) ->
      lprim (pfield idx) [to_lambda env e]
  | Mlazy e ->
     let fn = lfunction [fresh "param"] (to_lambda env e) in
     lprim (Pmakelazyblock Lazy_tag) [fn]
  | Mforce e ->
     Matching.inline_lazy_force (to_lambda env e) Rc_normal loc_none

and bindings_to_lambda env bindings body =
  List.fold_right (fun b rest -> match b with
  | `Unnamed e ->
     Lsequence (to_lambda env e, rest)
  | `Named (n, e) ->
     llet n (to_lambda env e) rest
  | `Recursive bs ->
     lletrec (List.map (fun (n, e) -> (n, to_lambda env e)) bs) rest)
    bindings body

let setup_options options =
  Clflags.native_code := true;
  Clflags.nopervasives := false;
  Clflags.dump_lambda := false;
  Clflags.dump_cmm := false;
  Clflags.keep_asm_file := false;
  Clflags.include_dirs :=
    [{ Clflags.path = Findlib.package_directory "zarith"; cmx_guaranteed = false }];
  Clflags.inlining_report := false;
  Clflags.dlcode := true;
  Clflags.shared := false;
  (* -O2/-O3 are handled by Oxcaml_flags (flambda2 inlining parameters) *)
  Clflags.Opt_flag_handler.set Oxcaml_flags.opt_flag_handler;

  (* Hack: disable the "no cmx" warning for zarith *)
  (* -55 (inlining-impossible): flambda2 reports every [@inline] on an
     external (e.g. Zarith) during cross-module inlining; pure noise here. *)
  let _ = Warnings.parse_options false "-58-55" in
  assert (not (Warnings.is_active (Warnings.No_cmx_file { missing_extension = ".cmx"; module_name = "asdf" })));

  (options |> List.iter @@ function
  | `Verbose ->
     Clflags.dump_lambda := true;
     Clflags.dump_cmm := true;
     Clflags.keep_asm_file := true;
     Clflags.inlining_report := true
  | `Shared ->
     Clflags.shared := true
  | `Package s ->
     let packages = String.split_on_char ',' s in
     let dirs = List.map (fun p ->
       { Clflags.path = Findlib.package_directory p; cmx_guaranteed = false }) packages in
     Clflags.include_dirs := dirs @ !Clflags.include_dirs
  | `ForPack s -> Clflags.for_package := Some s
  | `Dontlink _ -> ()
  | `Linkpkg -> ()
  | `Thread -> ()
  | `Optimize -> Clflags.set_o2 ()
  | `Bytecode -> Clflags.native_code := false
   );

  Compenv.(readenv Format.std_formatter (Before_compile "malfunction"));
  compmisc_init_path ();
  Compmisc.init_parameters ()

let module_to_lambda ~module_id:_ (Mmod (bindings, exports)) =
  let print_if flag printer arg =
    if !flag then Format.printf "%a@." printer arg;
    arg in

  let env = Compmisc.initial_env () in
  let bindings = reorder_bindings bindings in
  let exports = List.map (fun e -> snd (reorder e)) exports in
  (* flambda2 (like flambda1) takes the module block as the value of the
     initialisation code; see Translmod.transl_implementation. *)
  let module_size = List.length exports in
  let code =
    bindings_to_lambda env bindings
      (lprim (pmakeblock 0 Immutable) (List.map (to_lambda env) exports)) in

  let lambda = code
  |> print_if Clflags.dump_rawlambda Printlambda.lambda
  |> simplify_lambda
  |> print_if Clflags.dump_lambda Printlambda.lambda in

  (module_size, lambda)

type outfiles =
  | Out_native of {cmxfile: string; rest: string list}
  | Out_bytecode of {cmofile: string; rest: string list}

let delete_temps outfiles =
  let temps =
    match outfiles with
    | Out_native {cmxfile; rest} -> cmxfile::rest
    | Out_bytecode {cmofile; rest} -> cmofile::rest
  in
  List.iter Misc.remove_file temps

type options = [`Verbose | `Shared | `ForPack of string | `Package of string | `Dontlink of string | `Linkpkg | `Thread | `Optimize | `Bytecode] list

(* Make sure the unit's own .cmi is loaded (so that its CRC is recorded in
   the .cmx imports), generating an empty one if there is no .mli. *)
let ensure_cmi ~module_name ~filename =
  let cmi = module_name ^ ".cmi" in
  match load_path_find_uncap cmi with
  | file -> ignore (env_read_signature ~module_name ~file); None
  | exception Not_found ->
     let chop_ext =
         Misc.chop_extensions
       in
     let mlifile = chop_ext filename ^ !Config.interface_suffix in
     if Sys.file_exists mlifile then
       Typemod.(raise(Error(Location.in_file filename,
                            Env.empty,
                            Interface_not_compiled cmi)))
     else
       (* hackily generate an empty cmi file *)
       let cmifile = String.uncapitalize_ascii cmi in
       let mlifile = String.uncapitalize_ascii (module_name ^ ".mli") in
       let ch = open_out mlifile in
       output_string ch "(* autogenerated mli for malfunction *)\n";
       close_out ch;
       ignore (Sys.command ("ocamlc -c " ^ mlifile));
       Misc.remove_file mlifile;
       if not (Sys.file_exists cmifile) then failwith "Failed to generate empty cmi file";
       ignore (env_read_signature ~module_name ~file:cmifile);
       Some cmifile


let lambda_to_cmx ~filename ~prefixname ~module_name ~module_id (size, code) =
  let ppf = Format.std_formatter in
  let cmxfile = prefixname ^ ".cmx" in
  let objfile = prefixname ^ Config.ext_obj in
  let outfiles = ref [objfile] in
  try
    let cmifile = ensure_cmi ~module_name ~filename in
    outfiles := Option.to_list cmifile @ !outfiles;
    (* FIXME: may need to add modules referenced only by "external" to this.
       See Translmod.primitive_declarations and its use in Asmgen. *)
    let required_globals =
      Compilation_unit.Set.of_list (Env.get_required_globals ()) in
    let program = make_program ~module_id ~size ~required_globals code in
    compile_implementation ~filename ~prefixname ~ppf program;
    save_unit_info cmxfile program;
    Warnings.check_fatal ();
    Out_native {cmxfile; rest = !outfiles}
  with e ->
    let bt = Printexc.get_raw_backtrace () in
    delete_temps (Out_native {cmxfile; rest = !outfiles});
    Printexc.raise_with_backtrace e bt

let lambda_to_cmo ~filename:_ ~prefixname:_ ~module_name:_ ~module_id:_ (_size, _lambda) =
  (* OxCaml's Bytegen works on Blambda, not Lambda; bytecode output is not
     supported by this port. *)
  failwith "malfunction (OxCaml port): bytecode output (cmo) is not supported"

let compile_module ?(options=[]) ~filename modl =
  (* FIXME: do we really want to go through Clflags here? See Compenv.output_prefix *)
  let prefixname = Compenv.output_prefix filename in
  let module_name =
    prefixname
    |> Filename.basename
    |> Filename.remove_extension
    |> String.capitalize_ascii in
  let lambda_to_output =
    if List.mem `Bytecode options
    then lambda_to_cmo
    else lambda_to_cmx
  in
  if not (is_unit_name module_name) then
    raise (Invalid_argument ("Invalid module name " ^ module_name));
  setup_options options;
  let target = setup_unit ~filename ~prefixname in
  let module_id = Unit_info.modname target in
  modl
  |> module_to_lambda ~module_id
  |> lambda_to_output ~filename ~prefixname ~module_name ~module_id

let compile_file ~options filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  Lexing.(lexbuf.lex_curr_p <-
            { lexbuf.lex_curr_p with pos_fname = filename });
  let modl = Malfunction_parser.read_module lexbuf in
  compile_module ~options ~filename modl

let compile_cmx ?(options=[]) filename =
  compile_file ~options filename

let compile_cmo ?(options=[]) filename =
  compile_file ~options:(`Bytecode :: options) filename

let compile_and_load ?(options : options =[]) _e =
  (* Needs Asmlink.link_shared's new interface and a replacement for
     Compilenv.symbol_for_global; not ported. *)
  ignore options;
  failwith "malfunction (OxCaml port): compile_and_load is not supported"

let link_executable ?(options=[]) output tmpfiles =
   let cmxfile =
     match tmpfiles with
     | Out_native o -> o.cmxfile
     | Out_bytecode _ -> failwith "Bytecode linking unsupported"
   in
   let pkgs =
      options |> (List.filter_map @@
      function
      | `Package s -> Some s
      | _ -> None)
   in
   let linkpkg = options |> (List.exists @@ (function `Linkpkg -> true | _ -> false)) in
   let dontlink =
      options |> (List.filter_map @@
      function
      | `Dontlink s -> Some s
      | _ -> None)
   in
   let thread =
      options |> (List.exists @@
      function
      | `Thread -> true
      | _ -> false)
   in
   let pkgs =
     match pkgs with
     | [] -> []
     | pkgs -> ["-package"; String.concat "," pkgs] in
   let dontlink =
      if dontlink = [] then []
      else ["-dontlink"; String.concat "," dontlink]
   in
   let linkpkg = if linkpkg then ["-linkpkg"] else [] in
   let thread = if thread then ["-thread"] else [] in
   let opts = String.concat " " (thread @ linkpkg @ pkgs @ dontlink) in
   (* urgh *)
   Sys.command (Printf.sprintf "ocamlfind ocamlopt %s '%s' -o '%s'"
                 opts cmxfile output)
