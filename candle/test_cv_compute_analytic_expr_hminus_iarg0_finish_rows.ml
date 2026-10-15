(* ========================================================================== *)
(* Rounded-row final Taylor aggregation for the first selected hminus leaf.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Each exact nonnegative Hessian-row             *)
(* contribution is outward-rounded to the proved fixed denominator before    *)
(* accumulation.  Center and gradient uppers are rounded the same way.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_iarg0_selected_leaf_fixture.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_split_certificate_check.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_compute.ml";;

module Test_cv_compute_analytic_expr_hminus_iarg0_finish_rows = struct

open Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_split_certificate_check;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;

let marker phase =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_FINISH_ROWS" ^
     " DEVELOPMENT_NON_RELEASE phase=" ^ phase);;

let compute tm =
  rand
    (concl
      (candle_q_dim_analytic_jet_compute
        candle_cv_q_dim_taylor_model_compute_eqs tm));;

let rec dest_cexp_list tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] -> head :: dest_cexp_list tail
    | _ -> failwith "hminus finish rows: malformed cexp pair"
  else if aconv operator `Cexp_num` then []
  else failwith "hminus finish rows: malformed cexp list";;

let _ = marker "prepare";;
let prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    function0 normalized_lower normalized_upper;;
let instruction_count = length (dest_list prepared.program_term);;
let boxes = candle_poly_fixture_q_boxes normalized_lower normalized_upper;;
let boxes_representation =
  candle_q_dim_analytic_jet_boxes_encode_conv boxes;;
let boxes_term = rand (concl boxes_representation);;
let center_environment =
  compute
    (mk_comb (`candle_cv_q_center_environment_list`,boxes_term));;
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
let box_domain =
  compute
    (mk_comb (`candle_cv_q_dim_analytic_result_domain`,box));;
let inputs_valid =
  compute
    (list_mk_comb (`candle_cv_bool_and`,[center_domain;box_domain]));;
let box_valid =
  compute (mk_comb (`candle_cv_q_box_valid_list`,boxes_term));;
let radii =
  compute (mk_comb (`candle_cv_q_radius_list`,boxes_term));;
let center_jet =
  mk_comb (`candle_cv_q_dim_analytic_first_result_jet`,center);;
let box_jet =
  mk_comb (`candle_cv_q_dim_analytic_result_jet`,box);;
let center_value =
  compute (mk_comb (`candle_cv_q_dim_first_jet_f`,center_jet));;
let center_gradient =
  compute (mk_comb (`candle_cv_q_dim_first_jet_gradient`,center_jet));;
let box_hessian =
  compute (mk_comb (`candle_cv_q_dim_jet_hessian`,box_jet));;
let gradient_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_dot_abs_upper_extended`,
       [radii;center_gradient]));;
let rounded_center_upper =
  compute
    (mk_comb
      (`candle_cv_q_fixed_round_upper`,
       mk_comb (`Cexp_snd`,center_value)));;
let rounded_gradient_upper =
  compute (mk_comb (`candle_cv_q_fixed_round_upper`,gradient_upper));;
let _ = marker "shared-components-computed";;

let radius_values = dest_cexp_list radii;;
let hessian_rows = dest_cexp_list box_hessian;;

if length radius_values <> 6 || length hessian_rows <> 6 then
  failwith "hminus finish rows: unexpected dimension";;

let rec compute_row_contributions index weights rows =
  match weights,rows with
  | [],[] -> []
  | weight :: remaining_weights,row :: remaining_rows ->
      let _ = marker ("row-" ^ string_of_int index ^ "-dot-begin") in
      let dot =
        compute
          (list_mk_comb
            (`candle_cv_q_dot_abs_upper_extended`,[radii;row])) in
      let _ = marker ("row-" ^ string_of_int index ^ "-dot-end") in
      let contribution =
        compute
          (list_mk_comb
            (`candle_cv_q_mul_normalized_extended`,[weight;dot])) in
      let _ = marker ("row-" ^ string_of_int index ^ "-mul-end") in
      let rounded =
        compute (mk_comb (`candle_cv_q_fixed_round_upper`,contribution)) in
      let _ = marker ("row-" ^ string_of_int index ^ "-round-end") in
      rounded ::
        compute_row_contributions (index + 1)
          remaining_weights remaining_rows
  | _ -> failwith "hminus finish rows: row/radius length mismatch";;

let row_contributions =
  compute_row_contributions 0 radius_values hessian_rows;;

let rec sum_contributions index accumulator = function
  | [] -> accumulator
  | contribution :: rest ->
      let next =
        compute
          (list_mk_comb
            (`candle_cv_q_add_normalized_extended`,
             [accumulator;contribution])) in
      let _ = marker ("row-sum-" ^ string_of_int index) in
      sum_contributions (index + 1) next rest;;

let hessian_upper =
  sum_contributions 0 `candle_cv_q_zero` row_contributions;;
let _ = marker "hessian-upper-computed";;
let half_hessian =
  compute
    (list_mk_comb
      (`candle_cv_q_mul_normalized_extended`,
       [`candle_cv_q_half`;hessian_upper]));;
let derivative_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_add_normalized_extended`,
       [rounded_gradient_upper;half_hessian]));;
let upper =
  compute
    (list_mk_comb
      (`candle_cv_q_add_normalized_extended`,
       [rounded_center_upper;derivative_upper]));;
let _ = marker "upper-computed";;
let zero_le_upper =
  compute
    (list_mk_comb
      (`candle_cv_q_le`,[`candle_cv_q_zero`;upper]));;
let finish =
  compute
    (list_mk_comb
      (`candle_cv_q_dim_whole_box_finish`,
       [inputs_valid;box_valid;upper]));;
let _ = marker "finish-computed";;

let verdict,_ = candle_q_dim_analytic_jet_dest_pair finish;;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_FINISH_ROWS_OK" ^
   " DEVELOPMENT_NON_RELEASE instructions=" ^
   string_of_int instruction_count ^
   " verdict=" ^ string_of_term verdict ^
   " sign=" ^ string_of_term zero_le_upper ^
   " upper=" ^ string_of_term upper);;

end;;
