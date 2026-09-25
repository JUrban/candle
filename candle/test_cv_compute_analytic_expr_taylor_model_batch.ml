(* Focused proof/load regression for the one-verdict certified Taylor batch. *)

needs "candle/cv_compute_analytic_expr_taylor_model_batch.ml";;

open Candle_cv_analytic_expr_taylor_model_batch;;

let candle_taylor_model_batch_axioms_before = axioms ();;

let candle_taylor_model_batch_empty_compute =
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_dim_taylor_model_batch_compute_eqs)
    `candle_cv_q_dim_taylor_model_batch_check
       (Cexp_num 0) (Cexp_num 0)`;;

if hyp candle_taylor_model_batch_empty_compute <> [] ||
   rand (concl candle_taylor_model_batch_empty_compute) <> `Cexp_num 1` then
  failwith "certified Taylor batch: empty computation mismatch";;

let candle_taylor_model_batch_empty_sound = prove
 (`!box_e root_boxes (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_batch_covers type_witness root_boxes []
     ==> !(p:real^N).
       p IN interval
         [candle_q_box_lower_vector root_boxes,
          candle_q_box_upper_vector root_boxes]
       ==> candle_analytic_denote_dim box_e p < &0`,
  REWRITE_TAC[candle_q_dim_taylor_model_batch_covers_def; MEM] THEN
  MESON_TAC[]);;

let candle_taylor_model_batch_axioms_after = axioms ();;

if length candle_taylor_model_batch_axioms_after <>
     length candle_taylor_model_batch_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_taylor_model_batch_axioms_before)
       candle_taylor_model_batch_axioms_after) then
  failwith "certified Taylor batch: changed the global axiom set";;

print_endline "CANDLE_CV_TAYLOR_MODEL_BATCH_OK DEVELOPMENT_NON_RELEASE";;
