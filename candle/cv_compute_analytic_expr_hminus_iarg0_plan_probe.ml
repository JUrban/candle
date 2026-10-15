(* ========================================================================== *)
(* Bounded real-certificate probe for the first hminus source Iarg.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Search is untrusted; the resulting precision  *)
(* tree is retained only as a plan for later proof-producing replay.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_parameter_support_probe.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

module Candle_cv_analytic_expr_hminus_iarg0_plan_probe = struct

open Certificate;;
open M_verifier_main;;
open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_hminus_parameter_support_probe;;
open Candle_cv_flyspeck_nonlinear_driver;;

let source_id = "prep-GLFVCVK4 2477216213 split(0/64)";;
let iarg_index = 0;;

let marker phase =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_PLAN DEVELOPMENT_NON_RELEASE phase=" ^ phase);;

let _,preparation,needs_delta = Break_case_exec.get_case source_id;;
let prepare =
  Break_case_exec.run_generic
    (fun role -> preparation role THEN Break_case_exec.check_tac role)
    needs_delta;;
let target = Break_case_exec.get_one_iarg prepare (source_id,iarg_index);;
let _ = marker "source-target";;

let _,_,_,_,variable_names,bounds,_,expressions =
  candle_nl_hminus_parameter_fixture_from_target target;;

let parameter_decimal_bounds =
  REWRITE_RULE [interval_arith] hminus_interval;;
let parameter_decimal_lower =
  let lower_bound,_ = dest_conj (concl parameter_decimal_bounds) in
  let lower,_ = dest_binop `(<=):real->real->bool` lower_bound in
  lower;;
let parameter_lower_identity =
  candle_reflected_nl_exact_component parameter_decimal_lower;;
let parameter_lower = rand (concl parameter_lower_identity);;

(* Certificate search is untrusted planning.  The legacy formal builder has
   neither an interpretation for opaque [hminus] nor a seven-dimensional
   inverse instance, so plan at one representative certified endpoint.  The
   later reflected leaf proof still checks the complete hminus interval as a
   seventh coordinate; no theorem depends on this planning substitution. *)
let planning_expressions =
  map
    (fun expression ->
      let source_expansion =
        REWRITE_CONV candle_nl_hminus_parameter_defs expression in
      let division_expansion =
        REWRITE_CONV [real_div] (rand (concl source_expansion)) in
      subst [parameter_lower,`hminus:real`]
        (rand (concl division_expansion)))
    expressions;;
let planning_expressions =
  map
    (fun expression ->
      rand
        (concl
          (REWRITE_CONV
            [Sphere.rotate2;Sphere.rotate3;
             Sphere.delta_x4;
             GSYM Nonlinear_lemma.sol0_over_pi_EQ_const1;Sphere.sol0]
            expression)))
    planning_expressions;;
let planning_expressions =
  map
    (fun expression ->
      rand (concl (REWRITE_CONV [real_div] expression)))
    planning_expressions;;
let functions,variable_vector =
  candle_direct_exprs_to_vector_fun planning_expressions;;

if length functions <> 3 then
  failwith "hminus Iarg0 plan: source disjunct count drift";;

let vector_dimension = length (M_taylor.dest_vector variable_vector);;
let scan_variables =
  Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
    (fst (dest_abs (hd functions))) vector_dimension;;
let _ =
  do_list
    (fun (index,function_term) ->
      let _,body = dest_abs function_term in
      let unsupported =
        candle_nl_hminus_parameter_scan_expression scan_variables body in
      print_endline
        ("CANDLE_NL_HMINUS_IARG0_PLAN DEVELOPMENT_NON_RELEASE" ^
         " phase=structural-scan function=" ^ string_of_int index ^
         " unsupported=" ^
         candle_nl_hminus_parameter_join "," unsupported))
    (zip (0--(length functions - 1)) functions);;
let lower,upper = bounds;;
let lower_list = dest_list lower and upper_list = dest_list upper;;
let named_bounds = zip variable_names (zip lower_list upper_list);;
let sorted_names =
  map (fst o dest_var) (M_taylor.dest_vector variable_vector);;
let ordered_bounds =
  itlist
    (fun name result -> assoc name named_bounds :: result)
    sorted_names [];;
let exact_lower,exact_upper = unzip ordered_bounds;;
let exact_lower_term = Misc_vars.mk_real_list exact_lower
and exact_upper_term = Misc_vars.mk_real_list exact_upper;;
let _ = marker "planning-domain";;

let informal_lower =
  Informal_taylor.convert_to_float_list 6 true exact_lower_term
and informal_upper =
  Informal_taylor.convert_to_float_list 6 false exact_upper_term;;

let params =
  ref
    {M_verifier_main.default_params with
       mono_pass_flag = false;
       convex_flag = false;
       allow_derivatives = false;
       eps = 1e-10};;

let rec build_informal_verification_functions index = function
  | [] -> []
  | function_term :: rest ->
      marker ("verification-taylor-" ^ string_of_int index);
      let _,taylor = M_verifier_main.mk_funs 6 6 function_term in
      marker ("verification-interval-" ^ string_of_int index);
      let eval0 = Informal_taylor.mk_eval_function 6 function_term in
      Candle_informal_verifier_record.make taylor eval0 ::
      build_informal_verification_functions (index + 1) rest;;
let informal_functions =
  build_informal_verification_functions 0 functions;;
let _ = marker "verification-functions";;

let search_options =
  Candle_informal_search_options.make
    !params.raw_intervals0 1e-10 200 6 0;;
let search_functions =
  map
    (fun verifier ->
      Candle_informal_verifier_record.f verifier,
      Candle_informal_verifier_record.taylor verifier)
    informal_functions;;
let informal_domain =
  Informal_taylor.mk_m_center_domain
    6 informal_lower informal_upper;;

let certificate =
  Informal_search.construct_certificate
    search_options informal_domain search_functions;;
let stats = Certificate.result_stats certificate;;
let _ = marker "certificate-search";;

let precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 informal_functions certificate informal_lower informal_upper;;

let function_counts = Array.make (length functions) 0;;
let rec count_tree = function
  | P_result_pass (_,function_index,false) ->
      function_counts.(function_index) <- function_counts.(function_index) + 1
  | P_result_glue (_,_,false,left,right) ->
      count_tree left; count_tree right
  | P_result_mono _ ->
      failwith "hminus Iarg0 plan: monotonicity node"
  | P_result_pass (_,_,true) ->
      failwith "hminus Iarg0 plan: raw pass"
  | P_result_glue (_,_,true,_,_) ->
      failwith "hminus Iarg0 plan: convex glue"
  | P_result_ref _ ->
      failwith "hminus Iarg0 plan: reference node";;

let _ = count_tree precision_tree;;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " pass=" ^ string_of_int stats.pass ^
   " glue=" ^ string_of_int stats.glue ^
   " function0=" ^ string_of_int function_counts.(0) ^
   " function1=" ^ string_of_int function_counts.(1) ^
   " function2=" ^ string_of_int function_counts.(2));;

end;;
