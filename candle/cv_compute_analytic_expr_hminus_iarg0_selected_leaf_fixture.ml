(* ========================================================================== *)
(* Lightweight fixture for the first selected leaf of hminus Iarg 0.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The split path is untrusted fixture data.  A   *)
(* separate plan-consistency test must match its resulting formal domain to   *)
(* the first leaf of the reconstructed real certificate precision tree.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_parameter_support_probe.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

module Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_hminus_parameter_support_probe;;
open Candle_cv_flyspeck_nonlinear_driver;;

let source_id = "prep-GLFVCVK4 2477216213 split(0/64)";;
let iarg_index = 0;;
let marker phase =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_SELECTED_LEAF_FIXTURE" ^
     " DEVELOPMENT_NON_RELEASE phase=" ^ phase);;

let _,preparation,needs_delta = Break_case_exec.get_case source_id;;
let prepare =
  Break_case_exec.run_generic
    (fun role -> preparation role THEN Break_case_exec.check_tac role)
    needs_delta;;
let target = Break_case_exec.get_one_iarg prepare (source_id,iarg_index);;
let _ = marker "source-target";;

let _,_,_,_,variable_names,bounds,_,expressions =
  candle_nl_hminus_parameter_fixture_from_target target;;
let source_functions,variable_vector =
  candle_direct_exprs_to_vector_fun expressions;;
let _ = marker "source-functions";;

if length source_functions <> 3 then
  failwith "hminus Iarg0 selected fixture: source disjunct count drift";;

let source_function0 = hd source_functions;;
let function0_normalization =
  let source_expansion =
    REWRITE_CONV candle_nl_hminus_parameter_defs source_function0 in
  let _ = marker "source-expanded" in
  let division_expansion =
    REWRITE_CONV [real_div] (rand (concl source_expansion)) in
  let _ = marker "division-expanded" in
  let late_expansion =
    REWRITE_CONV
      [Sphere.rotate2;Sphere.rotate3;
       Sphere.delta_x4;
       GSYM Nonlinear_lemma.sol0_over_pi_EQ_const1;Sphere.sol0]
      (rand (concl division_expansion)) in
  let _ = marker "late-expanded" in
  let final_expansion =
    REWRITE_CONV [real_div] (rand (concl late_expansion)) in
  TRANS source_expansion
    (TRANS division_expansion (TRANS late_expansion final_expansion));;
let function0 = rand (concl function0_normalization);;
let _ = marker "function-normalized";;

if length (M_taylor.dest_vector variable_vector) <> 6 then
  failwith "hminus Iarg0 selected fixture: function dimension drift";;

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
let domain_subset,(float_lower,float_upper) =
  M_verifier_main.mk_float_domain 6
    (exact_lower_term,exact_upper_term);;
let root_domain =
  M_taylor.mk_m_center_domain 6 6 float_lower float_upper;;
let _ = marker "root-domain";;

(* Zero-based informal split axes 4,5,1,2,3,4,5,1,2,3,4,5 become the
   one-based formal axes below.  Each step selects the left child. *)
let selected_path = [5;6;2;3;4;5;6;2;3;4;5;6];;

let rec follow_left domain = function
  | [] -> domain
  | split_index :: rest ->
      let left,_ = M_verifier.split_domain 6 6 split_index domain in
      follow_left left rest;;

let leaf_domain = follow_left root_domain selected_path;;
let _ = marker "leaf-domain";;
let leaf_pair,_,_ = M_taylor.dest_m_cell_domain (concl leaf_domain);;
let leaf_lower,leaf_upper = dest_pair leaf_pair;;
let normalized_lower,_ = candle_reflected_nl_normalize_vector leaf_lower;;
let normalized_upper,_ = candle_reflected_nl_normalize_vector leaf_upper;;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_SELECTED_LEAF_FIXTURE_OK" ^
   " DEVELOPMENT_NON_RELEASE path_length=" ^
   string_of_int (length selected_path));;

end;;
