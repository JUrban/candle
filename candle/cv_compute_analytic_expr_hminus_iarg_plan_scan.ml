(* ========================================================================== *)
(* Scan every Iarg of the first hminus source with one reused informal plan.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is untrusted certificate planning only.   *)
(* Every eventual leaf is independently replayed by the reflected checker.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_iarg0_plan_probe.ml";;

module Candle_cv_analytic_expr_hminus_iarg_plan_scan = struct

open Certificate;;
open Candle_cv_analytic_expr_hminus_parameter_support_probe;;
open Candle_cv_analytic_expr_hminus_iarg0_plan_probe;;

let scan_iarg iarg_index =
  try
    let target =
      Break_case_exec.get_one_iarg prepare (source_id,iarg_index) in
    let _,_,_,_,variable_names,bounds,_,expressions =
      candle_nl_hminus_parameter_fixture_from_target target in
    if length expressions <> length functions then
      failwith "hminus Iarg scan: disjunct count drift";
    let lower,upper = bounds in
    let lower_list = dest_list lower and upper_list = dest_list upper in
    let named_bounds = zip variable_names (zip lower_list upper_list) in
    let ordered_bounds =
      itlist
        (fun name result -> assoc name named_bounds :: result)
        sorted_names [] in
    let exact_lower,exact_upper = unzip ordered_bounds in
    let exact_lower_term = Misc_vars.mk_real_list exact_lower
    and exact_upper_term = Misc_vars.mk_real_list exact_upper in
    let informal_lower =
      Informal_taylor.convert_to_float_list 6 true exact_lower_term
    and informal_upper =
      Informal_taylor.convert_to_float_list 6 false exact_upper_term in
    let informal_domain =
      Informal_taylor.mk_m_center_domain
        6 informal_lower informal_upper in
    let certificate =
      Informal_search.construct_certificate
        search_options informal_domain search_functions in
    let stats = Certificate.result_stats certificate in
    let precision_tree,_ =
      Informal_verifier.m_verify_raw0
        6 1 6 informal_functions certificate informal_lower informal_upper in
    let function_counts = Array.make (length functions) 0 in
    let rec count_tree = function
      | P_result_pass (_,function_index,false) ->
          function_counts.(function_index) <-
            function_counts.(function_index) + 1
      | P_result_glue (_,_,false,left,right) ->
          count_tree left; count_tree right
      | P_result_mono _ ->
          failwith "hminus Iarg scan: monotonicity node"
      | P_result_pass (_,_,true) ->
          failwith "hminus Iarg scan: raw pass"
      | P_result_glue (_,_,true,_,_) ->
          failwith "hminus Iarg scan: convex glue"
      | P_result_ref _ ->
          failwith "hminus Iarg scan: reference node" in
    count_tree precision_tree;
    print_endline
      ("CANDLE_NL_HMINUS_IARG_PLAN_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
       " iarg=" ^ string_of_int iarg_index ^
       " pass=" ^ string_of_int stats.pass ^
       " glue=" ^ string_of_int stats.glue ^
       " function0=" ^ string_of_int function_counts.(0) ^
       " function1=" ^ string_of_int function_counts.(1) ^
       " function2=" ^ string_of_int function_counts.(2))
  with Failure message ->
    print_endline
      ("CANDLE_NL_HMINUS_IARG_PLAN_SCAN_ERROR DEVELOPMENT_NON_RELEASE" ^
       " iarg=" ^ string_of_int iarg_index ^
       " message=" ^ message)
  | Not_found ->
    print_endline
      ("CANDLE_NL_HMINUS_IARG_PLAN_SCAN_ERROR DEVELOPMENT_NON_RELEASE" ^
       " iarg=" ^ string_of_int iarg_index ^
       " message=Not_found");;

let _ = do_list scan_iarg (0--20);;

end;;
