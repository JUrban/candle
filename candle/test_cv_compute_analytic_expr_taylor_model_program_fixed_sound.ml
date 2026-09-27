(* ========================================================================== *)
(* Structural test for the fixed-polynomial analytic-invariant bridge.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_certified_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_certified_sound;;

let candle_fixed_program_sound_axioms_before = axioms ();;

let candle_fixed_program_sound_test =
  candle_fs_poly_program_to_q_analytic_invariant;;

let candle_fixed_program_compile_sound_test =
  candle_q_dim_taylor_model_fixed_compile_run_analytic_invariant;;

let candle_fixed_program_representation_test =
  candle_cv_fs_q_dim_taylor_model_program_correct;;

let candle_fixed_program_certified_check_test =
  candle_cv_fs_q_dim_taylor_model_certified_check_correct;;

let candle_fixed_program_certified_accept_test =
  candle_q_dim_taylor_model_fixed_certified_accept_sound;;

if hyp candle_fixed_program_sound_test <> [] ||
   hyp candle_fixed_program_compile_sound_test <> [] ||
   hyp candle_fixed_program_representation_test <> [] ||
   hyp candle_fixed_program_certified_check_test <> [] ||
   hyp candle_fixed_program_certified_accept_test <> [] then
  failwith "fixed program sound: unexpected theorem assumptions";;

let candle_fixed_program_sound_axioms_after = axioms ();;

if length candle_fixed_program_sound_axioms_after <>
     length candle_fixed_program_sound_axioms_before ||
   not
     (List.for_all
       (fun theorem -> List.mem theorem candle_fixed_program_sound_axioms_before)
       candle_fixed_program_sound_axioms_after) then
  failwith "fixed program sound: changed the global axiom set";;

print_endline "CANDLE_CV_FIXED_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;
