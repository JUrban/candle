(* ========================================================================== *)
(* Genuine action-296 fixed-outer numerical discriminator.                   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The established proof-producing benchmark     *)
(* supplies authentic 1/8/32-cell stable-source batches.  The experimental   *)
(* checker retains fixed scale through all algebraic operations.  It earns   *)
(* no theorem authority; this run measures acceptance and recurring compute. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_stable_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;

let candle_action296_fixed_outer_axioms_before = axioms ();;

let candle_action296_fixed_outer_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-outer scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_fixed_outer_encoded result =
  let box_encoding =
    candle_q_dim_analytic_jet_boxes_encode_conv
      result.stable_batch_box_intervals_term in
  let jobs =
    candle_q_dim_taylor_model_stable_batch_cval_list
      (map
        (fun cell -> cell.stable_batch_encoded_job_term)
        result.stable_batch_prepared_cells) in
  rand (concl box_encoding),jobs;;

let candle_action296_fixed_outer_call result =
  let box_intervals,jobs = candle_action296_fixed_outer_encoded result in
  list_mk_comb
    (`candle_cv_fso_stable_batch_check`,
     [result.stable_batch_prepared_source.program_representation_term;
      box_intervals;jobs]);;

let candle_action296_fixed_outer_compute scope result =
  candle_action296_fixed_outer_marker scope "kernel-compute" "begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_compute_eqs
      (candle_action296_fixed_outer_call result) in
  candle_action296_fixed_outer_marker scope "kernel-compute" "end";
  if hyp theorem <> [] ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) then
    failwith ("action296 fixed outer: rejected " ^ scope);
  theorem;;

let candle_action296_fixed_outer_result_1 =
  candle_action296_fixed_outer_compute "boxes-1-fixed-outer"
    candle_action296_stable_batch_prove_result_1;;

let candle_action296_fixed_outer_result_8 =
  candle_action296_fixed_outer_compute "boxes-8-fixed-outer"
    candle_action296_stable_batch_prove_result_8;;

let candle_action296_fixed_outer_result_32 =
  candle_action296_fixed_outer_compute "boxes-32-fixed-outer"
    candle_action296_stable_batch_prove_result_32;;

let candle_action296_fixed_outer_axioms_after = axioms ();;

if length candle_action296_fixed_outer_axioms_after <>
     length candle_action296_fixed_outer_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_outer_axioms_before)
       candle_action296_fixed_outer_axioms_after) then
  failwith "action296 fixed outer: axiom set changed";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_OUTER_RESULT boxes=1,8,32 accepted=41" ^
   " theorem_authority=none");;
print_endline
  "CANDLE_CV_ACTION296_FIXED_OUTER_OK DEVELOPMENT_NON_RELEASE";;

