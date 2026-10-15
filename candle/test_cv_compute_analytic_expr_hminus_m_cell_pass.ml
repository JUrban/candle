(* ========================================================================== *)
(* Put the genuine reflected hminus box through Flyspeck's m_cell contract.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The box is reached by 46 formal midpoint      *)
(* splits from the source root domain, rather than asserted as an unrelated   *)
(* pair of endpoint vectors.                                                  *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_hminus_genuine_box.ml";;

module Test_cv_compute_analytic_expr_hminus_m_cell_pass = struct

open Test_cv_compute_analytic_expr_hminus_genuine_box;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_append_parameter;;
open Candle_cv_analytic_expr_box_certificate_prepare;;

let _,_,_,_,source_variable_names,source_bounds,_,fixture_expressions =
  Candle_cv_analytic_expr_hminus_parameter_support_probe.
    candle_nl_hminus_parameter_source_fixture source_id;;

let rec aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head && aconv_lists left_tail right_tail
  | _ -> false;;

if not (aconv_lists fixture_expressions source_expressions) then
  failwith "hminus m_cell source fixture drift";;

let source_lower,source_upper = source_bounds;;
let source_lower_list = dest_list source_lower;;
let source_upper_list = dest_list source_upper;;
let source_named_bounds =
  zip source_variable_names (zip source_lower_list source_upper_list);;
let source_sorted_names =
  map (fst o dest_var) (M_taylor.dest_vector source_variable_vector);;
let source_ordered_bounds =
  itlist
    (fun name result -> assoc name source_named_bounds :: result)
    source_sorted_names [];;
let source_ordered_lower,source_ordered_upper =
  unzip source_ordered_bounds;;
let source_domain_subset,(root_lower,root_upper) =
  M_verifier_main.mk_float_domain 6
    (Misc_vars.mk_real_list source_ordered_lower,
     Misc_vars.mk_real_list source_ordered_upper);;

let root_domain =
  M_taylor.mk_m_center_domain 6 6 root_lower root_upper;;

let rec choose_right count axis domain =
  if count = 0 then domain else
  let _,right = M_verifier.split_domain 6 6 axis domain in
  choose_right (count - 1) axis right;;

let rec choose_left count axis domain =
  if count = 0 then domain else
  let left,_ = M_verifier.split_domain 6 6 axis domain in
  choose_left (count - 1) axis left;;

let split_domain = choose_right 6 1 root_domain;;
let split_domain = choose_left 8 2 split_domain;;
let split_domain = choose_left 8 3 split_domain;;
let split_domain = choose_left 8 4 split_domain;;
let split_domain = choose_left 8 5 split_domain;;
let split_domain = choose_left 8 6 split_domain;;

let split_pair,_,_ =
  M_taylor.dest_m_cell_domain (concl split_domain);;

let actual_lower,actual_upper = dest_pair split_pair;;
let normalized_lower,_ = candle_reflected_nl_normalize_vector actual_lower;;
let normalized_upper,_ = candle_reflected_nl_normalize_vector actual_upper;;

let rec positive_width lower upper =
  match lower,upper with
  | [],[] -> true
  | lower_head :: lower_tail,upper_head :: upper_tail ->
      Num.lt_num (rat_of_term lower_head) (rat_of_term upper_head) &&
      positive_width lower_tail upper_tail
  | _ -> false;;

if not (positive_width normalized_lower normalized_upper) then
  failwith "hminus m_cell split domain is not positive-width";;

let pass_theorem =
  candle_reflected_nl_source_pass_with six_function
    (fun lower upper ->
      let seven_lower = lower @ [parameter_lower]
      and seven_upper = upper @ [parameter_upper] in
      let domain_prepared =
        candle_q_dim_analytic_jet_prepare_box_seven
          seven_function seven_lower seven_upper in
      candle_reflected_nl_append_parameter_prove_box_six
        domain_prepared seven_function six_function `hminus:real`
        parameter_bounds lower upper)
    split_domain;;

if hyp pass_theorem <> [] then
  failwith "hminus m_cell pass theorem has assumptions";;

print_endline
  "CANDLE_CV_HMINUS_M_CELL_PASS_OK DEVELOPMENT_NON_RELEASE splits=46";;

end;;
