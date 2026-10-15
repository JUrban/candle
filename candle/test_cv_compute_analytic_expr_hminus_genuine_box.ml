(* ========================================================================== *)
(* A genuine positive-width Flyspeck hminus box through the seven-dimensional *)
(* reflected checker and back to the original six-dimensional source.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Run after the authenticated Flyspeck nonlinear *)
(* prerequisites have loaded [hminus_interval] and [Break_case_exec].          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_parameter_support_probe.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_append_parameter.ml";;

module Test_cv_compute_analytic_expr_hminus_genuine_box = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_append_parameter;;
open Candle_cv_analytic_expr_hminus_parameter_support_probe;;
open Candle_cv_flyspeck_nonlinear_driver;;

let source_id = "prep-GLFVCVK4 2477216213 split(0/64)";;

let source_expressions =
  candle_nl_hminus_parameter_source_expressions source_id;;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE source-expanded";;

let source_functions,source_variable_vector =
  candle_direct_exprs_to_vector_fun source_expressions;;

let six_function = List.nth source_functions 1;;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE source-vectorized";;

let seven_function =
  let six_vector,six_body = dest_abs six_function in
  let seven_vector = `z:real^7` in
  let six_components = candle_poly_vector_components six_vector 6 in
  let seven_components = candle_poly_vector_components seven_vector 7 in
  let replacements =
    zip (fst (chop_list 6 seven_components)) six_components @
    [List.nth seven_components 6,`hminus:real`] in
  mk_abs (seven_vector,subst replacements six_body);;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE parameter-appended";;

(* This is a strict subbox of the authenticated split(0/64) source domain:
   the top 1/64 of the first coordinate and the bottom 1/256 of each other
   coordinate.  Its positive width is important: this is not a point test. *)
let lower_six =
  [`&32491526066357 / &5120000000000`;
   `&4`;`&4`;`&4`;`&4`;`&4`];;

let upper_six =
  [`&2032128000021 / &320000000000`;
   `&328432128000021 / &81920000000000`;
   `&328432128000021 / &81920000000000`;
   `&328432128000021 / &81920000000000`;
   `&328432128000021 / &81920000000000`;
   `&328432128000021 / &81920000000000`];;

let parameter_decimal_bounds =
  REWRITE_RULE [interval_arith] hminus_interval;;

let parameter_decimal_lower,parameter_decimal_upper =
  let lower_bound,upper_bound =
    dest_conj (concl parameter_decimal_bounds) in
  let lower,_ = dest_binop `(<=):real->real->bool` lower_bound in
  let _,upper = dest_binop `(<=):real->real->bool` upper_bound in
  lower,upper;;

let parameter_lower_identity =
  candle_reflected_nl_exact_component parameter_decimal_lower;;

let parameter_upper_identity =
  candle_reflected_nl_exact_component parameter_decimal_upper;;

let parameter_bounds =
  REWRITE_RULE
    [parameter_lower_identity;parameter_upper_identity]
    parameter_decimal_bounds;;

let parameter_lower = rand (concl parameter_lower_identity);;
let parameter_upper = rand (concl parameter_upper_identity);;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE parameter-bounded";;

let seven_lower = lower_six @ [parameter_lower];;
let seven_upper = upper_six @ [parameter_upper];;

let prepared =
  candle_q_dim_analytic_jet_prepare_box_seven
    seven_function seven_lower seven_upper;;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE prepared";;

let seven_theorem =
  candle_q_dim_analytic_jet_prove_box_seven
    prepared seven_lower seven_upper;;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE seven-proved";;

let six_theorem =
  candle_reflected_nl_append_parameter_prove_box_six
    prepared seven_function six_function `hminus:real`
    parameter_bounds lower_six upper_six;;

let _ = print_endline "CANDLE_HMINUS_GENUINE_BOX_PHASE six-proved";;

if hyp seven_theorem <> [] || hyp six_theorem <> [] then
  failwith "hminus genuine-box reflected theorem has assumptions";;

let instruction_count = length (dest_list prepared.program_term);;

if instruction_count = 0 then
  failwith "hminus genuine-box reflected program is empty";;

print_endline
  ("CANDLE_CV_ANALYTIC_EXPR_HMINUS_GENUINE_BOX_OK" ^
   " DEVELOPMENT_NON_RELEASE instructions=" ^
   string_of_int instruction_count);;

end;;
