(* ========================================================================== *)
(* Genuine action-296 fixed/rational schedule reuse discriminator.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The established stable-source proof benchmark *)
(* supplies authentic 1/8/32-cell batches.  This file evaluates the same     *)
(* batches with one source-shape schedule per compute call and then compares  *)
(* every complete scheduled result with the established result internally.   *)
(* It authorizes no theorem through the scheduled path.                       *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_stable_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_schedule.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_schedule;;

let candle_action296_schedule_axioms_before = axioms ();;

let candle_action296_schedule_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-source-schedule scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_schedule_encoded result =
  let box_encoding =
    candle_q_dim_analytic_jet_boxes_encode_conv
      result.stable_batch_box_intervals_term in
  let jobs =
    candle_q_dim_taylor_model_stable_batch_cval_list
      (map
        (fun cell -> cell.stable_batch_encoded_job_term)
        result.stable_batch_prepared_cells) in
  rand (concl box_encoding),jobs;;

let candle_action296_schedule_call checker result =
  let box_intervals,jobs = candle_action296_schedule_encoded result in
  list_mk_comb
    (checker,
     [result.stable_batch_prepared_source.program_representation_term;
      box_intervals;jobs]);;

let candle_action296_schedule_compute scope checker result =
  candle_action296_schedule_marker scope "kernel-compute" "begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fsa_scheduled_compute_eqs
      (candle_action296_schedule_call checker result) in
  candle_action296_schedule_marker scope "kernel-compute" "end";
  if hyp theorem <> [] ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) then
    failwith ("action296 schedule: rejected " ^ scope);
  theorem;;

let candle_action296_schedule_result_1 =
  candle_action296_schedule_compute "boxes-1-scheduled"
    `candle_cv_fsa_stable_batch_check_scheduled`
    candle_action296_stable_batch_prove_result_1;;

let candle_action296_schedule_result_8 =
  candle_action296_schedule_compute "boxes-8-scheduled"
    `candle_cv_fsa_stable_batch_check_scheduled`
    candle_action296_stable_batch_prove_result_8;;

let candle_action296_schedule_result_32 =
  candle_action296_schedule_compute "boxes-32-scheduled"
    `candle_cv_fsa_stable_batch_check_scheduled`
    candle_action296_stable_batch_prove_result_32;;

let candle_action296_schedule_equal_1 =
  candle_action296_schedule_compute "boxes-1-exact-equality"
    `candle_cv_fsa_stable_batch_schedule_equal`
    candle_action296_stable_batch_prove_result_1;;

let candle_action296_schedule_equal_8 =
  candle_action296_schedule_compute "boxes-8-exact-equality"
    `candle_cv_fsa_stable_batch_schedule_equal`
    candle_action296_stable_batch_prove_result_8;;

let candle_action296_schedule_equal_32 =
  candle_action296_schedule_compute "boxes-32-exact-equality"
    `candle_cv_fsa_stable_batch_schedule_equal`
    candle_action296_stable_batch_prove_result_32;;

let candle_action296_schedule_axioms_after = axioms ();;

if length candle_action296_schedule_axioms_after <>
     length candle_action296_schedule_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_schedule_axioms_before)
       candle_action296_schedule_axioms_after) then
  failwith "action296 schedule: axiom set changed";;

print_endline
  ("CANDLE_CV_ACTION296_SCHEDULE_RESULT boxes=1,8,32 accepted=41" ^
   " exact_result_equalities=41 theorem_authority=none");;
print_endline
  "CANDLE_CV_ACTION296_SCHEDULE_OK DEVELOPMENT_NON_RELEASE";;
