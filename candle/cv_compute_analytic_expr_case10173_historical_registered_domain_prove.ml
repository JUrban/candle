(* ========================================================================== *)
(* Exact root-domain identity for the registered genuine case-10173 result.  *)
(*                                                                            *)
(* The topology replay returns a rational box.  This adapter authenticates    *)
(* that box against the live verifier domain and the named domain consumed by *)
(* the final original-theorem bridge.                                          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_original_bridge.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

module Candle_cv_analytic_expr_case10173_historical_registered_domain_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_original_bridge;;

let candle_case10173_historical_registered_domain_prove root_boxes =
  let concrete_domain =
    rand (concl candle_case10173_hist_original_domain_def) in
  let actual_lower,actual_upper = dest_pair concrete_domain in
  let lower,actual_lower_theorem =
    candle_reflected_nl_normalize_vector actual_lower in
  let upper,actual_upper_theorem =
    candle_reflected_nl_normalize_vector actual_upper in
  let expected_boxes = candle_poly_fixture_q_boxes lower upper in
  if not (aconv root_boxes expected_boxes) then
    failwith "case10173 registered domain prove: root box mismatch";
  let lower_selector =
    `candle_q_box_lower_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let upper_selector =
    `candle_q_box_upper_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let lower_selector_theorem =
    candle_reflected_nl_selector_vector_identity
      lower_selector root_boxes lower in
  let upper_selector_theorem =
    candle_reflected_nl_selector_vector_identity
      upper_selector root_boxes upper in
  let lower_transport =
    TRANS lower_selector_theorem (SYM actual_lower_theorem) in
  let upper_transport =
    TRANS upper_selector_theorem (SYM actual_upper_theorem) in
  let concrete_identity =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `(,):real^6->real^6->real^6#real^6`)
      [lower_transport;upper_transport] in
  let identity =
    TRANS concrete_identity
      (SYM candle_case10173_hist_original_domain_def) in
  let expected =
    mk_eq
      (mk_pair
        (mk_comb (lower_selector,root_boxes),
         mk_comb (upper_selector,root_boxes)),
       `candle_case10173_hist_original_domain:real^6#real^6`) in
  if hyp identity <> [] || not (aconv (concl identity) expected) then
    failwith "case10173 registered domain prove: identity drift";
  identity;;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_DOMAIN_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
