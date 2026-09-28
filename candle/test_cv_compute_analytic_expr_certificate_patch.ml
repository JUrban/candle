(* ========================================================================== *)
(* Focused structural test for logical analytic certificate-data patching.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_patch.ml";;
needs "candle/cv_compute_analytic_expr_action296_plan.ml";;

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_certificate_patch;;

let candle_analytic_certificate_patch_test_axioms_before = axioms ();;

let _ =
  let expression =
    `Candle_analytic_sqrt 1 0 0 2 0 0
       (Candle_analytic_sqrt 2 0 0 3 0 0
         Candle_analytic_pi_half)` in
  let count =
    CONV_RULE (RAND_CONV NUM_REDUCE_CONV)
      (REWRITE_CONV[candle_analytic_sqrt_count_def]
        (mk_comb (`candle_analytic_sqrt_count`,expression))) in
  if hyp count <> [] || not (aconv (rand (concl count)) `2`) then
    failwith "analytic certificate patch test: square-root count drift";;

let _ =
  let erasure =
    SPECL
      [candle_action296_plan_prepared.expression_term;
       `[]:(((num#num)#num)#((num#num)#num))list`]
      candle_analytic_patch_sqrt_certificates_erasure in
  if hyp erasure <> [] ||
     hyp candle_analytic_program_patch_sqrt_append <> [] ||
     hyp candle_analytic_program_patch_sqrt_compile <> [] then
    failwith "analytic certificate patch test: theorem assumptions";;

let candle_analytic_certificate_patch_test_axioms_after = axioms ();;

if length candle_analytic_certificate_patch_test_axioms_after <>
     length candle_analytic_certificate_patch_test_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_analytic_certificate_patch_test_axioms_before)
       candle_analytic_certificate_patch_test_axioms_after) then
  failwith "analytic certificate patch test: changed global axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_CERTIFICATE_PATCH_OK DEVELOPMENT_NON_RELEASE";;
