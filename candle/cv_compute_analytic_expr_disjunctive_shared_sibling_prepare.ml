(* ========================================================================== *)
(* Reusable direct preparation for siblings sharing the case-16594 formula.  *)
(*                                                                            *)
(* The exact leaf proposition is produced by the authenticated production   *)
(* PREP tactic and iarg partition.  Certificate search remains untrusted;    *)
(* every retained result must later pass the reflected checker and exact     *)
(* source-proposition handoff.                                                *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_case16594_direct_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_shared_sibling_prepare = struct

open Certificate;;
open M_verifier_main;;
open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;

let rec candle_disjunctive_shared_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_shared_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_shared_production_target label index =
  let _,prep_tactic,needs_delta = Break_case_exec.get_case label in
  let prepare =
    Break_case_exec.run_generic
      (fun role ->
        prep_tactic role THEN Break_case_exec.check_tac role)
      needs_delta in
  Break_case_exec.get_one_iarg prepare (label,index);;

let candle_disjunctive_shared_fixture label index =
  let target =
    candle_disjunctive_shared_production_target label index in
  let reconstruction = candle_direct_ineqm_conv target in
  if not (aconv (lhand (concl reconstruction)) target) then
    failwith "shared sibling fixture: reconstruction source mismatch";
  let case_term = rand (concl reconstruction) in
  let expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC candle_direct_expand_ineq_case)
      case_term in
  let converted = rand (concl expansion) in
  let ineq,variable_names,bounds = M_verifier_main.dest_ineq converted in
  let standard = M_verifier_main.mk_standard_ineq [REAL_POW_1;real_pow] ineq in
  let terms = striplist dest_disj ((lhand o concl) standard) in
  if length terms <> 2 then
    failwith "shared sibling fixture: source disjunction drift";
  let functions,variable_vector =
    candle_direct_exprs_to_vector_fun (map lhand terms) in
  if length functions <> 2 ||
     not
       (candle_disjunctive_shared_aconv_lists functions
         candle_disjunctive_case16594_functions) ||
     not (aconv variable_vector candle_disjunctive_case16594_variable_vector)
  then failwith "shared sibling fixture: shared expression identity mismatch";
  target,reconstruction,expansion,converted,variable_names,bounds,standard,
  functions,variable_vector;;

let candle_disjunctive_shared_plan variable_names bounds functions
    variable_vector =
  let lo,hi = bounds in
  let sorted_variable_names =
    map (fst o dest_var) (M_taylor.dest_vector variable_vector) in
  let lo_list = dest_list lo and hi_list = dest_list hi in
  let named_bounds = zip variable_names (zip lo_list hi_list) in
  let ordered_bounds =
    itlist
      (fun name result -> assoc name named_bounds :: result)
      sorted_variable_names [] in
  let xx0,zz0 = unzip ordered_bounds in
  let xx = Misc_vars.mk_real_list xx0 and zz = Misc_vars.mk_real_list zz0 in
  let domain_subset,(xx1,zz1) = M_verifier_main.mk_float_domain 6 (xx,zz) in
  let xx2 = Informal_taylor.convert_to_float_list 6 true xx
  and zz2 = Informal_taylor.convert_to_float_list 6 false zz in
  if sorted_variable_names <>
       candle_disjunctive_case16594_plan_sorted_variable_names ||
     not
       (candle_disjunctive_shared_aconv_lists functions
         candle_disjunctive_case16594_functions) ||
     not (aconv variable_vector candle_disjunctive_case16594_variable_vector)
  then failwith "shared sibling plan: shared source drift";
  let search_options =
    Candle_informal_search_options.make
      !candle_disjunctive_case16594_plan_params.raw_intervals0
      1e-10 200 6 0 in
  let search_functions =
    map
      (fun f -> Candle_informal_verifier_record.f f,
        Candle_informal_verifier_record.taylor f)
      candle_disjunctive_case16594_plan_informal_functions in
  let informal_domain = Informal_taylor.mk_m_center_domain 6 xx2 zz2 in
  let certificate =
    Informal_search.construct_certificate
      search_options informal_domain search_functions in
  let stats = Certificate.result_stats certificate in
  let precision_tree,_ =
    Informal_verifier.m_verify_raw0
      6 1 6 candle_disjunctive_case16594_plan_informal_functions
      certificate xx2 zz2 in
  domain_subset,xx1,zz1,certificate,stats,precision_tree;;

let candle_disjunctive_shared_count_functions tree =
  let function0 = ref 0 and function1 = ref 0 in
  let rec count = function
    | P_result_pass (_,0,false) -> function0 := !function0 + 1
    | P_result_pass (_,1,false) -> function1 := !function1 + 1
    | P_result_glue (_,_,false,left,right) -> count left; count right
    | _ -> failwith "shared sibling plan: unexpected precision-tree node" in
  count tree;
  !function0,!function1;;

end;;
