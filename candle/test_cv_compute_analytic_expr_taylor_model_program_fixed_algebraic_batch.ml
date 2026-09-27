(* Focused proof/load regression for the algebraic one-verdict batch. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_fixed_algebraic_batch_axioms_before = axioms ();;

let candle_fixed_algebraic_batch_empty_compute =
  candle_q_dim_analytic_jet_compute candle_cv_fsa_batch_compute_eqs
    `candle_cv_fsa_batch_check (Cexp_num 0) (Cexp_num 0)`;;

if hyp candle_fixed_algebraic_batch_empty_compute <> [] ||
   rand (concl candle_fixed_algebraic_batch_empty_compute) <>
     `Cexp_num 1` ||
   hyp candle_q_dim_taylor_model_fixed_algebraic_batch_accept_iff <> [] ||
   hyp candle_q_dim_taylor_model_fixed_algebraic_batch_accept_mem <> [] ||
   hyp candle_q_dim_taylor_model_fixed_algebraic_batch_sound <> [] ||
   hyp candle_cv_fsa_batch_check_correct <> [] then
  failwith "fixed algebraic batch: theorem regression";;

let candle_fixed_algebraic_batch_axioms_after = axioms ();;

if length candle_fixed_algebraic_batch_axioms_after <>
     length candle_fixed_algebraic_batch_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_fixed_algebraic_batch_axioms_before)
       candle_fixed_algebraic_batch_axioms_after) then
  failwith "fixed algebraic batch: changed the global axiom set";;

print_endline
  "CANDLE_CV_FIXED_ALGEBRAIC_BATCH_OK DEVELOPMENT_NON_RELEASE";;
