(* ========================================================================== *)
(* Component probe for the first selected real hminus-family leaf.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This separates the final Taylor aggregation   *)
(* after the center and box jets have been computed.  It makes no theorem     *)
(* claim; its purpose is to identify the smallest failing execution boundary. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_iarg0_selected_leaf_fixture.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_split_certificate_check.ml";;

module Test_cv_compute_analytic_expr_hminus_iarg0_finish_components = struct

open Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_split_certificate_check;;

let marker phase =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_FINISH_COMPONENTS" ^
     " DEVELOPMENT_NON_RELEASE phase=" ^ phase);;

let compute tm =
  rand
    (concl
      (candle_q_dim_analytic_jet_compute
        candle_cv_q_dim_analytic_split_certificate_compute_eqs tm));;

let _ = marker "prepare";;
let prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    function0 normalized_lower normalized_upper;;
let instruction_count = length (dest_list prepared.program_term);;
let boxes = candle_poly_fixture_q_boxes normalized_lower normalized_upper;;
let boxes_representation =
  candle_q_dim_analytic_jet_boxes_encode_conv boxes;;
let boxes_term = rand (concl boxes_representation);;
let _ = marker "boxes-encoded";;

let center_environment =
  compute
    (mk_comb (`candle_cv_q_center_environment_list`,boxes_term));;
let _ = marker "center-environment-computed";;
let center =
  compute
    (list_mk_comb
      (`candle_cv_q_dim_analytic_first_program`,
       [center_environment;prepared.program_representation_term]));;
let _ = marker "center-jet-computed";;
let box =
  compute
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [boxes_term;prepared.program_representation_term]));;
let _ = marker "box-jet-computed";;

let center_domain =
  compute
    (mk_comb
      (`candle_cv_q_dim_analytic_first_result_domain`,center));;
let _ = marker "center-domain-computed";;
let box_domain =
  compute
    (mk_comb (`candle_cv_q_dim_analytic_result_domain`,box));;
let _ = marker "box-domain-computed";;
let inputs_valid =
  compute
    (list_mk_comb (`candle_cv_bool_and`,[center_domain;box_domain]));;
let _ = marker "inputs-valid-computed";;
let box_valid =
  compute (mk_comb (`candle_cv_q_box_valid_list`,boxes_term));;
let _ = marker "box-valid-computed";;

let radii =
  compute (mk_comb (`candle_cv_q_radius_list`,boxes_term));;
let _ = marker "radii-computed";;
let center_jet =
  mk_comb (`candle_cv_q_dim_analytic_first_result_jet`,center);;
let box_jet =
  mk_comb (`candle_cv_q_dim_analytic_result_jet`,box);;
let center_value =
  compute (mk_comb (`candle_cv_q_dim_first_jet_f`,center_jet));;
let _ = marker "center-value-computed";;
let center_gradient =
  compute (mk_comb (`candle_cv_q_dim_first_jet_gradient`,center_jet));;
let _ = marker "center-gradient-computed";;
let box_hessian =
  compute (mk_comb (`candle_cv_q_dim_jet_hessian`,box_jet));;
let _ = marker "box-hessian-computed";;

let gradient_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_dot_abs_upper_extended`,
       [radii;center_gradient]));;
let _ = marker "gradient-upper-computed";;
let hessian_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_weighted_rows_abs_upper_extended`,
       [radii;radii;box_hessian]));;
let _ = marker "hessian-upper-computed";;
let half_hessian =
  compute
    (list_mk_comb
      (`candle_cv_q_mul_normalized_extended`,
       [`candle_cv_q_half`;hessian_upper]));;
let _ = marker "half-hessian-computed";;
let derivative_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_add_normalized_extended`,
       [gradient_upper;half_hessian]));;
let _ = marker "derivative-upper-computed";;
let upper =
  compute
    (list_mk_comb
      (`candle_cv_q_add_normalized_extended`,
       [mk_comb (`Cexp_snd`,center_value);derivative_upper]));;
let _ = marker "upper-computed";;
let zero_le_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_le`,[`candle_cv_q_zero`;upper]));;
let _ = marker "upper-sign-computed";;
let finish =
  compute
    (list_mk_comb
      (`candle_cv_q_dim_whole_box_finish`,
       [inputs_valid;box_valid;upper]));;
let _ = marker "finish-computed";;

let verdict,_ = candle_q_dim_analytic_jet_dest_pair finish;;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_FINISH_COMPONENTS_OK" ^
   " DEVELOPMENT_NON_RELEASE instructions=" ^
   string_of_int instruction_count ^
   " verdict=" ^ string_of_term verdict ^
   " sign=" ^ string_of_term zero_le_upper);;

end;;
