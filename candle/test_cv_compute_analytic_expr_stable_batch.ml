(* ========================================================================== *)
(* Focused empty-batch structural test for the stable analytic checker.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_batch.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_stable_batch;;

let candle_analytic_stable_batch_test_axioms_before = axioms ();;

let candle_analytic_stable_batch_test_expression =
 `Candle_analytic_sqrt 1 0 0 2 0 0
    (Candle_analytic_sqrt 2 0 0 3 0 0 Candle_analytic_pi_half)`;;

let candle_analytic_stable_batch_test_intervals =
 `[candle_analytic_sqrt_interval 4 0 0 5 0 0;
   candle_analytic_sqrt_interval 6 0 0 7 0 0]`;;

let candle_analytic_stable_batch_test_program =
  rand
    (concl
      (REWRITE_CONV
        [candle_analytic_compile_def; APPEND;
         candle_cv_analytic_instruction_list_def;
         candle_cv_analytic_instruction_def;
         candle_analytic_sqrt_interval_def;
         candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
         FST; SND]
        (mk_comb
          (`candle_cv_analytic_instruction_list`,
           mk_comb
             (`candle_analytic_compile`,
              candle_analytic_stable_batch_test_expression)))));;

let candle_analytic_stable_batch_test_encode_intervals intervals =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def;
         candle_analytic_sqrt_interval_def; FST; SND]
        (mk_comb (`candle_cv_q_interval_list`,intervals))));;

let candle_analytic_stable_batch_test_run intervals =
  let call =
    list_mk_comb
      (`candle_cv_fsa_stable_batch_check`,
       [candle_analytic_stable_batch_test_program;
        candle_analytic_stable_batch_test_encode_intervals intervals;
        `Cexp_num 0`]) in
  compute candle_cv_fsa_stable_batch_compute_eqs call;;

let candle_analytic_stable_batch_test_pass =
  candle_analytic_stable_batch_test_run
    candle_analytic_stable_batch_test_intervals;;

let candle_analytic_stable_batch_test_missing =
  let items = dest_list candle_analytic_stable_batch_test_intervals in
  candle_analytic_stable_batch_test_run
    (mk_list ([hd items],type_of (hd items)));;

let _ =
  if not
      (aconv (rand (concl candle_analytic_stable_batch_test_pass))
        `Cexp_num 1`) ||
     not
      (aconv (rand (concl candle_analytic_stable_batch_test_missing))
        `Cexp_num 0`) ||
     hyp candle_cv_fsa_stable_jobs_check_correct <> [] ||
     hyp candle_cv_fsa_stable_batch_check_correct <> [] then
    failwith "analytic stable batch test: structural result mismatch";;

let candle_analytic_stable_batch_test_axioms_after = axioms ();;

if length candle_analytic_stable_batch_test_axioms_after <>
     length candle_analytic_stable_batch_test_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_analytic_stable_batch_test_axioms_before)
       candle_analytic_stable_batch_test_axioms_after) then
  failwith "analytic stable batch test: changed global axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_STABLE_BATCH_OK DEVELOPMENT_NON_RELEASE";;
