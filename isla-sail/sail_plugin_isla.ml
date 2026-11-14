(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Libsail

open Ast
open Ast_util
open Interactive.State
open Jib
open Jib_util

let opt_isla_preserve = ref ([]:string list)
let opt_isla_output_dir : string option ref = ref None

let isla_options = [
    ( Flag.create ~prefix:["isla"] ~arg:"id" "preserve",
      Arg.String (fun id -> opt_isla_preserve := id :: !opt_isla_preserve),
      "do not remove the provided id when generating IR");
    ( Flag.create ~prefix:["isla"] ~arg:"directory" "output_dir",
      Arg.String (fun dir -> opt_isla_output_dir := Some dir),
      "set a custom directory to output generated Isla IR");
  ]

let isla_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "isla"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "c"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "c"; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("remove_not_pats", []);
    ("pattern_literals_typed", [Literal_arg "all"]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "c"])
  ]


module Ir_config : Jib_compile.CONFIG = struct
  open Type_check
  open Jib_compile

  let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
  let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

  let rec convert_typ ctx typ =
    let Typ_aux (typ_aux, l) as typ = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | Typ_id id when string_of_id id = "bool"   -> CT_bool
    | Typ_id id when string_of_id id = "int"    -> CT_lint
    | Typ_id id when string_of_id id = "nat"    -> CT_lint
    | Typ_id id when string_of_id id = "unit"   -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "real"   -> CT_real

    | Typ_id id when string_of_id id = "float16" -> CT_float 16
    | Typ_id id when string_of_id id = "float32" -> CT_float 32
    | Typ_id id when string_of_id id = "float64" -> CT_float 64
    | Typ_id id when string_of_id id = "float128" -> CT_float 128
    | Typ_id id when string_of_id id = "float_rounding_mode" -> CT_rounding_mode

    | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool

    | Typ_app (id, args) when string_of_id id = "itself" ->
       convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
    | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" ->
       begin match destruct_range Env.empty typ with
       | None -> assert false (* Checked if range type in guard *)
       | Some (kids, constr, n, m) ->
          let ctx = { ctx with local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env }in
          match nexp_simp n, nexp_simp m with
          | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
               when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
             CT_fint 64
          | n, m ->
             if prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n) && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64))) then
               CT_fint 64
             else
               CT_lint
       end

    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" ->
       CT_list (ctyp_suprema (convert_typ ctx typ))

    (* When converting a sail bitvector type into C, we have three options in order of efficiency:
       - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
       - If the length is less than 64, then use a small bits type, sbits.
       - If the length may be larger than 64, use a large bits type lbits. *)
    | Typ_app (id, [A_aux (A_nexp n, _)])
         when string_of_id id = "bitvector" ->
       begin match nexp_simp n with
       | Nexp_aux (Nexp_constant n, _) when Big_int.equal n Big_int.zero -> CT_lbits
       | Nexp_aux (Nexp_constant n, _) -> CT_fbits (Big_int.to_int n)
       | _ -> CT_lbits
       end

    | Typ_app (id, [A_aux (A_nexp n, _);
                    A_aux (A_typ typ, _)])
         when string_of_id id = "vector" ->
       begin match nexp_simp n with
       | Nexp_aux (Nexp_constant c, _) ->
          CT_fvector (Big_int.to_int c, convert_typ ctx typ)
       | _ ->
          CT_vector (convert_typ ctx typ)
       end

    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" ->
       CT_ref (convert_typ ctx typ)

    | Typ_id id when Bindings.mem id ctx.records -> CT_struct (id, [])
    | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
        let ctyp_args =
          List.filter_map
            (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
            typ_args
        in
        CT_struct (id, ctyp_args)

    | Typ_id id when Bindings.mem id ctx.variants -> CT_variant (id, []) |> transparent_newtype ctx
    | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
        let ctyp_args =
          List.filter_map
            (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
            typ_args
        in
        CT_variant (id, ctyp_args) |> transparent_newtype ctx
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum id

    | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)

    | Typ_exist _ ->
       (* Use Type_check.destruct_exist when optimising with SMT, to
          ensure that we don't cause any type variable clashes in
          local_env, and that we can optimize the existential based
          upon it's constraints. *)
       begin match destruct_exist (Env.expand_synonyms ctx.local_env typ) with
       | Some (kids, nc, typ) ->
          let env = add_existential l kids nc ctx.local_env in
          convert_typ { ctx with local_env = env } typ
       | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
       end

    | Typ_var kid -> CT_poly kid

    | _ -> Reporting.unreachable l  __POS__ ("No C type for type " ^ string_of_typ typ)

  let optimize_anf ctx aexp =
    let open Anf in
    (* 有限整数类型在 Jib 中退化为普通整数。首次使用时保留集合约束，
       避免从符号联合体参数引入 Sail 类型不允许的值。 *)
    let constrain (AE_aux (aux, annot) as exp) =
      let values = match aux with
        | AE_val v | AE_return (v, _) | AE_exit (v, _) | AE_throw (v, _)
        | AE_field (v, _, _) | AE_match (v, _, _) | AE_if (v, _, _, _)
        | AE_short_circuit (_, v, _) -> [v]
        | AE_app (_, values, _) -> values
        | AE_struct_update (v, fields, _) -> v :: List.map snd (Bindings.bindings fields)
        | _ -> []
      in
      let seen = ref NameSet.empty in
      let rec assumptions = function
        | AV_id (id, lvar) when not (NameSet.mem id !seen) ->
            seen := NameSet.add id !seen;
            let typ = Env.expand_synonyms annot.env (lvar_typ lvar) in
            let rec finite_sets value (NC_aux (nc, _)) = match nc with
              | NC_set (set_value, ints) when nexp_identical value set_value -> [ints]
              | NC_and (lhs, rhs) -> finite_sets value lhs @ finite_sets value rhs
              | _ -> []
            in
            let sets = match destruct_numeric typ with
              | Some (_, nc, value) ->
                  List.concat_map (finite_sets value) (nc :: Env.get_constraints annot.env)
              | None -> []
            in
            List.map (fun ints ->
                let ctyp = convert_typ { ctx with local_env = annot.env } typ in
                let tests = List.map (fun n ->
                    V_call (Eq, [V_id (id, ctyp); V_lit (VL_int n, ctyp)])) ints in
                let condition = List.fold_left (fun acc test -> V_call (Bor, [acc; test]))
                    (V_lit (VL_bool false, CT_bool)) tests in
                AE_aux (AE_app (Extern (mk_id "isla_type_assume", Some unit_typ),
                    [AV_cval (condition, bool_typ)], unit_typ), annot)
              ) sets
        | AV_tuple vs | AV_list (vs, _) | AV_vector (vs, _) -> List.concat_map assumptions vs
        | AV_record (fields, _) -> List.concat_map (fun (_, v) -> assumptions v) (Bindings.bindings fields)
        | _ -> []
      in
      match List.concat_map assumptions values with
      | [] -> exp
      | checks -> AE_aux (AE_block (checks, exp, aexp_typ exp), annot)
    in
    fold_aexp constrain aexp

  let unroll_loops = None
  let make_call_precise _ _ _ _ = true
  let ignore_64 = false
  let struct_value = true
  let tuple_value = true
  let track_throw = true
  let branch_coverage = None
  let use_real = false
  let use_void = false
  let eager_control_flow = false
  let preserve_types = IdSet.empty
  let assert_to_exception = false
  let fun_to_wires = Bindings.empty
end

let jib_of_ast env ast effect_info =
  let open Jib_compile in
  let module Jibc = Make(Ir_config) in
  let ctx = initial_ctx ~for_target:"c" env effect_info in
  Jibc.compile_ast ctx ast

let remove_casts cdefs =
  let module StringMap = Map.Make(String) in
  let conversions = ref StringMap.empty in

  let rec legal_cast = function
    | CT_fbits _, CT_lbits -> true
    | CT_lbits, CT_fbits _ -> true
    | CT_fvector (_, ctyp1), CT_vector ctyp2 -> ctyp_equal ctyp1 ctyp2 || legal_cast (ctyp1, ctyp2)
    | CT_vector ctyp1, CT_fvector (_, ctyp2) -> ctyp_equal ctyp1 ctyp2 || legal_cast (ctyp1, ctyp2)
    | CT_vector ctyp1, CT_vector ctyp2 -> legal_cast (ctyp1, ctyp2)
    | CT_fvector (n, ctyp1), CT_fvector (m, ctyp2) -> n = m && legal_cast (ctyp1, ctyp2)
    | _, _ -> false
  in

  let both_fbits = function
    | CT_fbits _, CT_fbits _ -> true
    | _, _ -> false
  in
  let fbits_cast cval = function
    | CT_fbits n, CT_fbits m when n > m -> V_call (Zero_extend n, [cval])
    | CT_fbits n, CT_fbits m when n < m -> V_call (Slice n, [cval; V_lit (VL_int Big_int.zero, CT_lint)])
    | _, _ -> cval
  in

  let remove_instr_casts = function
    | I_aux (I_copy (clexp, cval), aux) ->
       let ctyp_to = clexp_ctyp clexp in
       let ctyp_from = cval_ctyp cval in
       if ctyp_equal ctyp_to ctyp_from || legal_cast (ctyp_to, ctyp_from) then
         [I_aux (I_copy (clexp, cval), aux)]
       else if both_fbits (ctyp_to, ctyp_from) then
         [I_aux (I_copy (clexp, fbits_cast cval (ctyp_to, ctyp_from)), aux)]
       else (
         let fid = Printf.sprintf "%s->%s" (string_of_ctyp ctyp_from) (string_of_ctyp ctyp_to) in
         conversions := StringMap.add fid (ctyp_from, ctyp_to) !conversions;
         [I_aux (I_funcall (CR_one clexp, Call, (mk_id fid, []), [cval]), aux)]
       )
    | I_aux (I_init (ctyp_to, id, Init_cval cval), aux) ->
       let ctyp_from = cval_ctyp cval in
       if ctyp_equal ctyp_to ctyp_from || legal_cast (ctyp_to, ctyp_from) then
         [I_aux (I_init (ctyp_to, id, Init_cval cval), aux)]
       else if both_fbits (ctyp_to, ctyp_from) then
         [I_aux (I_init (ctyp_to, id, Init_cval (fbits_cast cval (ctyp_to, ctyp_from))), aux)]
       else (
         let fid = Printf.sprintf "%s->%s" (string_of_ctyp ctyp_from) (string_of_ctyp ctyp_to) in
         conversions := StringMap.add fid (ctyp_from, ctyp_to) !conversions;
         [I_aux (I_decl (ctyp_to, id), aux);
          ifuncall (snd aux) (CL_id (id, ctyp_to)) (mk_id fid, []) [cval]]
       )
    | instr -> [instr]
  in
  let cdefs = List.map (fun cdef -> cdef_concatmap_instr remove_instr_casts cdef) cdefs in
  let vals =
    List.map (fun (fid, (ctyp_from, ctyp_to)) ->
        CDEF_aux (CDEF_val (mk_id fid, [], [ctyp_from], ctyp_to, Some fid), mk_def_annot Parse_ast.Unknown ())
      ) (StringMap.bindings !conversions)
  in
  vals @ cdefs

(** Sail allows val x = "y" declarations to also have an
   implementation, which is used for some backends. Currently these
   can be preserved by the Sail->Jib compiler, so we remove any
   here. *)
let remove_extern_impls cdefs =
  let exts = ref IdSet.empty in
  List.iter
    (function
     | CDEF_aux (CDEF_val (id, _, _, _, Some _), _) -> exts := IdSet.add id !exts
     | _ -> ()
    ) cdefs;
  List.filter
    (function
     | CDEF_aux (CDEF_fundef (id, _, _, _), _) when IdSet.mem id !exts -> false
     | _ -> true
    ) cdefs

(** We need to fix up calls to the list cons function, as it's handled specially by Sail->C *)
let fix_cons cdefs =
  let all_list_ctyps = ref CTSet.empty in
  let cons_name ctyp = mk_id ("cons#" ^ string_of_ctyp ctyp) in

  let collect_cons_ctyps list_ctyps = function
    | I_aux (I_funcall (clexp, Extern _, (id, [ctyp]), args), aux) when string_of_id id = "sail_cons" ->
       list_ctyps := CTSet.add ctyp !list_ctyps;
       list_ctyps := CTSet.add ctyp !all_list_ctyps;
       I_aux (I_funcall (clexp, Call, (cons_name ctyp, []), args), aux)

    | instr -> instr
  in

  List.map (fun cdef ->
      let list_ctyps = ref CTSet.empty in
      let cdef = cdef_map_instr (collect_cons_ctyps list_ctyps) cdef in
      let vals =
        List.map (fun ctyp ->
            CDEF_aux (CDEF_val (cons_name ctyp, [], [ctyp; CT_list ctyp], CT_list ctyp, Some "cons"), mk_def_annot Parse_ast.Unknown ())
          ) (CTSet.elements (CTSet.diff !list_ctyps !all_list_ctyps)) in
      vals @ [cdef]
    ) cdefs
  |> List.concat

let isla_target out_file { ast; effect_info; env; _ } =
  let out_file = match out_file with Some out_file -> out_file ^ ".ir" | None -> "out.ir" in
  let props = Property.find_properties ast in
  Bindings.bindings props |> List.map fst |> IdSet.of_list |> Specialize.add_initial_calls;

  (* let ast, env = Specialize.(specialize typ_ord_specialization env ast) in *)
  let cdefs, ctx = jib_of_ast env ast effect_info in
  let assume = CDEF_aux (CDEF_val (mk_id "isla_type_assume", [], [CT_bool], CT_unit, Some "assume"),
      mk_def_annot Parse_ast.Unknown ()) in
  let cdefs = assume :: cdefs in
  let cdefs, _ = Jib_optimize.remove_tuples cdefs ctx in
  let cdefs = remove_casts cdefs |> remove_extern_impls |> fix_cons in
  let buf = Buffer.create 256 in
  Jib_ir.Flat_ir_formatter.output_defs buf cdefs;
  let out_info = Util.open_output_with_check ?directory:!opt_isla_output_dir out_file in
  output_string out_info.channel (Buffer.contents buf);
  Util.close_output_with_check out_info

let isla_initialize () =
  Preprocess.add_symbol "SYMBOLIC";

  (* These options are either needed for ARM, or increase performance significantly (memo_z3) *)
  Nl_flow.opt_nl_flow := true;
  Type_check.opt_no_lexp_bounds_check := true;
  Reporting.opt_warnings := false;
  Initial_check.opt_allow_internal := true;

  Specialize.add_initial_calls (IdSet.singleton (mk_id "isla_footprint"));
  Specialize.add_initial_calls (IdSet.singleton (mk_id "isla_footprint_no_init"));
  Specialize.add_initial_calls (IdSet.singleton (mk_id "isla_footprint_bare"));
  Specialize.add_initial_calls (IdSet.singleton (mk_id "isla_client"));
  List.iter (fun id ->
      Specialize.add_initial_calls (IdSet.singleton (mk_id id))
    ) !opt_isla_preserve

let _ =
  Target.register
    ~name:"isla"
    ~options:isla_options
    ~pre_parse_hook:isla_initialize
    ~rewrites:isla_rewrites
    isla_target
