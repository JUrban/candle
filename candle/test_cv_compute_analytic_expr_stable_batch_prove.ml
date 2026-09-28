(* Focused load and theorem-interface test for the stable batch adapter. *)

needs "candle/cv_compute_analytic_expr_stable_batch_prove.ml";;

open Candle_cv_analytic_expr_stable_batch_prove;;

let candle_stable_batch_prove_test_axioms_before = axioms ();;

if hyp candle_q_dim_taylor_model_stable_batch_sound_six <> [] then
  failwith "stable Taylor batch prover test: soundness assumptions";;

let candle_stable_batch_prove_test_axioms_after = axioms ();;

if length candle_stable_batch_prove_test_axioms_after <>
     length candle_stable_batch_prove_test_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_stable_batch_prove_test_axioms_before)
       candle_stable_batch_prove_test_axioms_after) then
  failwith "stable Taylor batch prover test: changed global axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_STABLE_BATCH_PROVE_OK DEVELOPMENT_NON_RELEASE";;
