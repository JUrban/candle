(* ========================================================================== *)
(* Focused fail-closed test for exact analytic certificate-slot matching.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_patch_exact.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_patch_exact;;

let candle_analytic_certificate_patch_exact_test_axioms_before = axioms ();;

let candle_analytic_certificate_patch_exact_test_program =
 `[Candle_analytic_program_pi_half;
   Candle_analytic_program_sqrt
     (candle_analytic_sqrt_interval 1 0 0 2 0 0);
   Candle_analytic_program_neg;
   Candle_analytic_program_sqrt
     (candle_analytic_sqrt_interval 2 0 0 3 0 0)]`;;

let candle_analytic_certificate_patch_exact_test_intervals =
 `[candle_analytic_sqrt_interval 4 0 0 5 0 0;
   candle_analytic_sqrt_interval 6 0 0 7 0 0]`;;

let candle_analytic_certificate_patch_exact_test_encode_program program =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_analytic_instruction_list_def;
         candle_cv_analytic_instruction_def;
         candle_analytic_sqrt_interval_def;
         candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
         FST; SND]
        (mk_comb (`candle_cv_analytic_instruction_list`,program))));;

let candle_analytic_certificate_patch_exact_test_encode_intervals intervals =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def;
         candle_analytic_sqrt_interval_def; FST; SND]
        (mk_comb (`candle_cv_q_interval_list`,intervals))));;

let candle_analytic_certificate_patch_exact_test_program_encoded =
  candle_analytic_certificate_patch_exact_test_encode_program
    candle_analytic_certificate_patch_exact_test_program;;

let candle_analytic_certificate_patch_exact_test_run intervals =
  let call =
    list_mk_comb
      (`candle_cv_analytic_program_sqrt_data_exact`,
       [candle_analytic_certificate_patch_exact_test_encode_intervals intervals;
        candle_analytic_certificate_patch_exact_test_program_encoded]) in
  compute candle_cv_analytic_program_sqrt_data_exact_compute_eqs call;;

let candle_analytic_certificate_patch_exact_test_pass =
  candle_analytic_certificate_patch_exact_test_run
    candle_analytic_certificate_patch_exact_test_intervals;;

let candle_analytic_certificate_patch_exact_test_missing =
  let items =
    dest_list candle_analytic_certificate_patch_exact_test_intervals in
  candle_analytic_certificate_patch_exact_test_run
    (mk_list ([hd items],type_of (hd items)));;

let candle_analytic_certificate_patch_exact_test_extra =
  let items = dest_list
    candle_analytic_certificate_patch_exact_test_intervals in
  candle_analytic_certificate_patch_exact_test_run
    (mk_list (hd items :: items,type_of (hd items)));;

let _ =
  if not
      (aconv
        (rand (concl candle_analytic_certificate_patch_exact_test_pass))
        `Cexp_num 1`) ||
     not
      (aconv
        (rand (concl candle_analytic_certificate_patch_exact_test_missing))
        `Cexp_num 0`) ||
     not
      (aconv
        (rand (concl candle_analytic_certificate_patch_exact_test_extra))
        `Cexp_num 0`) ||
     hyp candle_cv_analytic_program_sqrt_data_exact_correct <> [] then
    failwith "analytic certificate patch exact test: fail-closed mismatch";;

let candle_analytic_certificate_patch_exact_test_axioms_after = axioms ();;

if length candle_analytic_certificate_patch_exact_test_axioms_after <>
     length candle_analytic_certificate_patch_exact_test_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_analytic_certificate_patch_exact_test_axioms_before)
       candle_analytic_certificate_patch_exact_test_axioms_after) then
  failwith "analytic certificate patch exact test: changed global axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_CERTIFICATE_PATCH_EXACT_OK DEVELOPMENT_NON_RELEASE";;
