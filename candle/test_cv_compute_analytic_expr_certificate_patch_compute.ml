(* ========================================================================== *)
(* Focused representation test for executable certificate-data patching.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_patch_compute.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_patch;;
open Candle_cv_analytic_expr_certificate_patch_compute;;

let candle_analytic_certificate_patch_compute_test_axioms_before = axioms ();;

let candle_analytic_certificate_patch_compute_test_program =
 `[Candle_analytic_program_pi_half;
   Candle_analytic_program_sqrt
     (candle_analytic_sqrt_interval 1 0 0 2 0 0);
   Candle_analytic_program_neg;
   Candle_analytic_program_sqrt
     (candle_analytic_sqrt_interval 2 0 0 3 0 0)]`;;

let candle_analytic_certificate_patch_compute_test_intervals =
 `[candle_analytic_sqrt_interval 4 0 0 5 0 0;
   candle_analytic_sqrt_interval 6 0 0 7 0 0]`;;

let candle_analytic_certificate_patch_compute_test_exact =
  let representation =
    REWRITE_RULE
      [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
       candle_cv_q_def; candle_cv_lc_z_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_analytic_instruction_def;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_analytic_sqrt_interval_def;
       LET_DEF; LET_END_DEF; FST; SND]
      (SPECL
        [candle_analytic_certificate_patch_compute_test_program;
         candle_analytic_certificate_patch_compute_test_intervals]
        candle_cv_analytic_program_patch_sqrt_correct) in
  CONV_RULE
    (LAND_CONV
      (compute candle_cv_analytic_program_patch_sqrt_compute_eqs))
    representation;;

let _ =
  if hyp candle_analytic_certificate_patch_compute_test_exact <> [] ||
     hyp candle_cv_analytic_instruction_patch_sqrt_correct <> [] ||
     hyp candle_cv_analytic_program_patch_sqrt_correct <> [] then
    failwith "analytic certificate patch compute test: theorem assumptions";;

let candle_analytic_certificate_patch_compute_test_axioms_after = axioms ();;

if length candle_analytic_certificate_patch_compute_test_axioms_after <>
     length candle_analytic_certificate_patch_compute_test_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_analytic_certificate_patch_compute_test_axioms_before)
       candle_analytic_certificate_patch_compute_test_axioms_after) then
  failwith "analytic certificate patch compute test: changed global axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_CERTIFICATE_PATCH_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;
