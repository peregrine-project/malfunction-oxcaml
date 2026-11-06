(* Compatibility layer for OxCaml (ocaml-variants 5.2.0+ox, flambda2).

   This replaces the cppo-based malfunction_compat.cppo.ml of upstream
   Malfunction 0.7.1.  Everything here is OxCaml-specific; stock OCaml is
   not supported by this file. *)

open Lambda

let loc_none = Debuginfo.Scoped_location.Loc_unknown

(* Malfunction is untyped: every value has the generic boxed-value layout
   and lives on the heap. *)
let layout = Lambda.layout_any_value
let duid = Lambda.debug_uid_none

let lswitch (scr : lambda) (swi : lambda_switch) =
  Lswitch (scr, swi, loc_none, layout)

let llet id e body = Llet (Strict, layout, id, duid, e, body)

let lifthenelse c a b = Lifthenelse (c, a, b, layout)

let lstaticcatch e lbl d = Lstaticcatch (e, (lbl, []), d, Same_region, layout)

let lparam name =
  { name; debug_uid = duid; layout;
    attributes = default_param_attribute; mode = alloc_heap }

let lfunction' params body =
  Lambda.lfunction'
    ~kind:(Curried { nlocal = 0 })
    ~params:(List.map lparam params)
    ~return:layout
    ~body
    ~attr:default_function_attribute
    ~loc:loc_none
    ~mode:alloc_heap
    ~ret_mode:alloc_heap

let lfunction params body = Lfunction (lfunction' params body)

let lapply fn args =
  Lapply {
    ap_func = fn;
    ap_args = args;
    ap_result_layout = layout;
    ap_region_close = Rc_normal;
    ap_mode = alloc_heap;
    ap_loc = loc_none;
    ap_tailcall = Default_tailcall;
    ap_inlined = Default_inlined;
    ap_specialised = Default_specialise;
    ap_probe = None;
  }

(* OxCaml's Lletrec only accepts syntactic functions.  Malfunction's `rec`
   bindings are required to be lambdas, so we use Lletrec directly in that
   case (this is the fast path: flambda2 sees a proper set of mutually
   recursive closures and can make direct calls).  Anything else goes
   through Value_rec_compiler, like stock OCaml >= 5.2 does. *)
let lletrec bindings body =
  let as_fun = function
    | (id, Lfunction def) -> Some { id; debug_uid = duid; def }
    | _ -> None in
  match List.map as_fun bindings with
  | fns when List.for_all (fun x -> x <> None) fns ->
     Lletrec (List.map Option.get fns, body)
  | _ ->
     let bindings =
       List.map (fun (id, v) -> id, duid, Value_rec_types.Static, v) bindings in
     Value_rec_compiler.compile_letrec bindings body

(* Reads_vary is the conservative choice (upstream used [Mutable] here):
   Malfunction's `field` may be applied to mutable blocks obtained from
   OCaml globals.  For pure Rocq/peregrine output, Reads_agree would be
   sound and would allow more CSE. *)
let pfield ix = Pfield (ix, Pointer, Reads_vary)

let pmakeblock tag mut = Pmakeblock (tag, mut, All_value, alloc_heap)

let pisint = Pisint { variant_only = false }

let lconst_int n = Lconst (Const_base (Typedtree.Const_int n))

(* ---- Scalar arithmetic ---------------------------------------------------
   All integer/float primitives are now [Pscalar of _ Scalar.Operation.t]. *)
module S = Scalar
module Op = S.Operation

let int_ty : locality_mode S.Integral.t =
  S.Maybe_naked.Value (S.Integral.Width.Taggable S.Integral.Taggable.Width.Int)
let int32_ty : locality_mode S.Integral.t =
  S.Maybe_naked.Value (S.Integral.Width.Boxable (S.Integral.Boxable.Width.Int32 alloc_heap))
let int64_ty : locality_mode S.Integral.t =
  S.Maybe_naked.Value (S.Integral.Width.Boxable (S.Integral.Boxable.Width.Int64 alloc_heap))
let float_ty : locality_mode S.Floating.t =
  S.Maybe_naked.Value (S.Floating.Width.Float64 alloc_heap)

let pint_binop ty (op : Op.Binary.Int_op.t) =
  Pscalar (Op.Binary (Op.Binary.Integral (ty, op)))
let pint_shift ty (op : Op.Binary.Shift_op.t) =
  Pscalar (Op.Binary (Op.Binary.Shift (ty, op, Op.Binary.Shift_op.Rhs.Int)))
let pint_cmp ty (c : S.Integer_comparison.t) =
  Pscalar (Op.Binary (Op.Binary.Icmp (S.Integral.ignore_locality ty, c)))
let pint_unop ty (op : Op.Unary.Int_op.t) =
  Pscalar (Op.Unary (Op.Unary.Integral (ty, op)))
let pfloat_binop (op : Op.Binary.Float_op.t) =
  Pscalar (Op.Binary (Op.Binary.Floating (float_ty, op)))
let pfloat_cmp (c : S.Float_comparison.t) =
  Pscalar (Op.Binary (Op.Binary.Fcmp (S.Floating.ignore_locality float_ty, c)))
let pfloat_unop (op : Op.Unary.Float_op.t) =
  Pscalar (Op.Unary (Op.Unary.Floating (float_ty, op)))
let pcast ~(src : locality_mode S.t) ~(dst : locality_mode S.t) =
  Pscalar (Op.Unary (Op.Unary.Static_cast { src = S.ignore_locality src; dst }))

(* ---- C calls --------------------------------------------------------------
   [Pccall] now takes an [external_call_description] (reprs with Repr_poly
   compiled away); Env gives us a [Primitive.description].  This mirrors
   Translprim.to_lambda_prim, which is not exported. *)
let extern_repr_of_native_repr : Primitive.native_repr -> Lambda.extern_repr =
  function
  | Primitive.Repr_poly ->
     failwith "layout-polymorphic external primitives are not supported"
  | Same_as_ocaml_repr s -> Same_as_ocaml_repr s
  | Unboxed_float f -> Unboxed_float f
  | Unboxed_or_untagged_integer i -> Unboxed_or_untagged_integer i
  | Unboxed_vector v -> Unboxed_vector v
  | Unpacked_product s -> Same_as_ocaml_repr s

let external_call_of_primitive (p : Primitive.description)
    : Lambda.external_call_description =
  Primitive.make
    ~name:p.prim_name
    ~alloc:p.prim_alloc
    ~c_builtin:p.prim_c_builtin
    ~effects:p.prim_effects
    ~coeffects:p.prim_coeffects
    ~native_name:p.prim_native_name
    ~native_repr_args:
      (List.map (fun (m, r) -> m, extern_repr_of_native_repr r)
         p.prim_native_repr_args)
    ~native_repr_res:
      (let (m, r) = p.prim_native_repr_res in m, extern_repr_of_native_repr r)
    ~is_layout_poly:p.prim_is_layout_poly

let simple_prim ~name ~arity ~alloc =
  Lambda.simple_prim_on_values ~name ~arity ~alloc

(* ---- driver -------------------------------------------------------------- *)

let compmisc_init_path () = Compmisc.init_path ()

let simplify_lambda lam =
  Simplif.simplify_lambda lam
    ~restrict_to_upstream_dwarf:!Dwarf_flags.restrict_to_upstream_dwarf
    ~gdwarf_may_alter_codegen:!Dwarf_flags.gdwarf_may_alter_codegen

let load_path_find_uncap = Load_path.find_normalized

let for_pack_prefix () = Compilation_unit.Prefix.from_clflags ()

let env_read_signature ~module_name ~file =
  let a = Unit_info.Artifact.from_filename ~for_pack_prefix:(for_pack_prefix ()) file in
  assert (Compilation_unit.name_as_string (Unit_info.Artifact.modname a) = module_name);
  Env.read_signature (Global_module.Name.create_no_args module_name) a

let is_unit_name = Unit_info.is_unit_name

(* Create the Unit_info for the unit being compiled, make it current in Env
   and Compilenv.  Mirrors Compile_common.with_info / Optcompile. *)
let setup_unit ~filename ~prefixname =
  let target =
    Unit_info.make ~source_file:filename ~for_pack_prefix:(for_pack_prefix ())
      Impl prefixname in
  Env.set_unit_name (Some target);
  Compilenv.reset target;
  target

let unix = (module Unix : Compiler_owee.Unix_intf.S)

let make_program ~module_id ~size ~required_globals code =
  Lambda.{
    compilation_unit = module_id;
    main_module_block_format =
      Mb_struct { mb_repr = Module_value_only { field_count = size } };
    arg_block_idx = None;
    required_globals;
    code;
  }

(* The flambda2 pipeline, as in Optcompile.compile_from_tlambda:
   Slambda.eval -> Simplif -> Flambda2.lambda_to_cmm -> Asmgen. *)
let compile_implementation ~filename ~prefixname ~ppf (program : Lambda.program) =
  let code =
    program.code
    |> Slambda.eval (fun s -> s)
    |> fun { Slambda.slv_comptime = _; slv_runtime } -> slv_runtime in
  let program = { program with code } in
  Asmgen.compile_implementation unix
    ~pipeline:(Asmgen.Direct_to_cmm
                 (Flambda2.lambda_to_cmm
                    ~machine_width:Target_system.Machine_width.Sixty_four
                    ~keep_symbol_tables:false))
    ~sourcefile:(Some filename) ~prefixname ~ppf_dump:ppf program

let save_unit_info cmxfile (program : Lambda.program) =
  Compilenv.save_unit_info cmxfile
    ~main_module_block_format:program.main_module_block_format
    ~arg_descr:None
