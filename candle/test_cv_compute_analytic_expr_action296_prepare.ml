(* ========================================================================== *)
(* Prepare the exact action-296 analytic source as one shared-jet program.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_action296_fixture.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_fixture;;

let candle_action296_prepare_axioms_before = axioms ();;
let candle_action296_prepare_vector,
    candle_action296_prepare_body =
  dest_abs candle_action296_analytic_function;;
let candle_action296_prepare_variables =
  Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
    candle_action296_prepare_vector 6;;
let candle_action296_prepare_sqrt_variables =
  map (fun variable -> mk_comb (`sqrt:real->real`,variable))
    candle_action296_prepare_variables;;
let candle_action296_prepare_variable_sqrt_count = ref 0;;
let candle_action296_prepare_nested_sqrt_count = ref 0;;

let candle_action296_prepare_sqrt_interval tm =
  if exists (aconv tm) candle_action296_prepare_sqrt_variables then
    (candle_action296_prepare_variable_sqrt_count :=
       !candle_action296_prepare_variable_sqrt_count + 1;
     `((((2,0),0),((3,0),0)):
        ((num#num)#num)#((num#num)#num))`)
  else
    (candle_action296_prepare_nested_sqrt_count :=
       !candle_action296_prepare_nested_sqrt_count + 1;
     `((((50,0),0),((100,0),0)):
        ((num#num)#num)#((num#num)#num))`);;

let candle_action296_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_prepare_sqrt_interval
    candle_action296_analytic_function;;

let candle_action296_prepare_instruction_count =
  length (dest_list candle_action296_prepared.program_term);;

if Digest.to_hex
     (Digest.string (string_of_term candle_action296_analytic_function)) <>
     "14a01d94a2d263608ca2bb5ce211078d" ||
   !candle_action296_prepare_variable_sqrt_count <> 6 ||
   !candle_action296_prepare_nested_sqrt_count <> 1 ||
   candle_action296_prepare_instruction_count <= 0 ||
   hyp candle_action296_prepared.valid_theorem <> [] ||
   hyp candle_action296_prepared.source_theorem <> [] ||
   hyp candle_action296_prepared.compile_theorem <> [] ||
   hyp candle_action296_prepared.program_representation <> [] then
  failwith "action296 analytic fixture: authenticated preparation mismatch";;

let candle_action296_prepare_axioms_after = axioms ();;
if length candle_action296_prepare_axioms_after <>
     length candle_action296_prepare_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_action296_prepare_axioms_before)
       candle_action296_prepare_axioms_after) then
  failwith "action296 analytic preparation changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_ANALYTIC_PREPARE_RESULT functions=1 " ^
   "variable_sqrts=6 nested_sqrts=1 atn=1 pi_half=1 instructions=" ^
   string_of_int candle_action296_prepare_instruction_count ^
   " function_md5=14a01d94a2d263608ca2bb5ce211078d authenticated=1");;
print_endline "CANDLE_CV_ACTION296_ANALYTIC_PREPARE_OK";;
