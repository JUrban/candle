(* ========================================================================== *)
(* Focused source/reifier regression for the authentic action-296 function.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This excludes certificate search, adaptive     *)
(* precision, numerical checking, and theorem reconstruction.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_action296_fixture.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_fixture;;

let candle_action296_prepare_variables =
  let vector,_ = dest_abs candle_action296_analytic_function in
  Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
    vector 6;;

let candle_action296_prepare_variable_sqrts =
  map (fun variable -> mk_comb (`sqrt:real->real`,variable))
    candle_action296_prepare_variables;;

let candle_action296_prepare_variable_sqrt_count = ref 0;;
let candle_action296_prepare_nested_sqrt_count = ref 0;;

let candle_action296_prepare_sqrt_interval tm =
  if exists (aconv tm) candle_action296_prepare_variable_sqrts then
    (candle_action296_prepare_variable_sqrt_count :=
       !candle_action296_prepare_variable_sqrt_count + 1;
     `((((2,0),0),((3,0),0)):
        ((num#num)#num)#((num#num)#num))`)
  else
    (candle_action296_prepare_nested_sqrt_count :=
       !candle_action296_prepare_nested_sqrt_count + 1;
     `((((50,0),0),((100,0),0)):
        ((num#num)#num)#((num#num)#num))`);;

let candle_action296_prepare_result =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_prepare_sqrt_interval
    candle_action296_analytic_function;;

let candle_action296_prepare_function_md5 =
  Digest.to_hex
    (Digest.string (string_of_term candle_action296_analytic_function));;

let candle_action296_prepare_instruction_count =
  length (dest_list candle_action296_prepare_result.program_term);;

if candle_action296_prepare_function_md5 <>
     "14a01d94a2d263608ca2bb5ce211078d" ||
   !candle_action296_prepare_variable_sqrt_count <> 6 ||
   !candle_action296_prepare_nested_sqrt_count <> 1 ||
   candle_action296_prepare_instruction_count <> 54 ||
   hyp candle_action296_prepare_result.valid_theorem <> [] ||
   hyp candle_action296_prepare_result.source_theorem <> [] then
  failwith "action296 focused preparation: authenticated state mismatch";;

print_endline
  ("CANDLE_ACTION296_FIXTURE_PREPARE_OK function_md5=" ^
   candle_action296_prepare_function_md5 ^
   " instructions=" ^
   string_of_int candle_action296_prepare_instruction_count ^
   " variable_sqrts=" ^
   string_of_int !candle_action296_prepare_variable_sqrt_count ^
   " nested_sqrts=" ^
   string_of_int !candle_action296_prepare_nested_sqrt_count);;
