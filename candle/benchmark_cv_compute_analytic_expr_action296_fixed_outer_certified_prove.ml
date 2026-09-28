(* ========================================================================== *)
(* Certified fixed-outer batches on 41 genuine action-296 cells.             *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_stable_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml";;

open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove;;

let candle_action296_fixed_outer_certified_axioms_before = axioms ();;

let candle_action296_fixed_outer_certified_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-outer-certified scope=" ^
     scope ^ " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_fixed_outer_certified_run scope cells =
  candle_action296_stable_batch_prove_scope := scope;
  candle_action296_fixed_outer_certified_marker
    scope "one-verdict-proof" "begin";
  let result =
    candle_q_dim_taylor_model_fixed_outer_stable_batch_prove_six
      candle_action296_plan_prepared
      candle_action296_stable_batch_prove_box_intervals_value cells in
  candle_action296_fixed_outer_certified_marker
    scope "one-verdict-proof" "end";
  result;;

let candle_action296_fixed_outer_certified_result_1 =
  candle_action296_fixed_outer_certified_run
    "candidate-boxes-1" candle_action296_stable_batch_prove_cells_1;;
let candle_action296_fixed_outer_certified_result_8 =
  candle_action296_fixed_outer_certified_run
    "candidate-boxes-8" candle_action296_stable_batch_prove_cells_8;;
let candle_action296_fixed_outer_certified_result_32 =
  candle_action296_fixed_outer_certified_run
    "candidate-boxes-32" candle_action296_stable_batch_prove_cells_32;;

let candle_action296_fixed_outer_certified_sources scope result cells =
  candle_action296_fixed_outer_certified_marker
    scope "source-theorem-extraction" "begin";
  let theorems =
    candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_sources_six
      result in
  if length theorems <> length cells then
    failwith
      "action296 fixed outer certified: source theorem cardinality drift";
  candle_action296_fixed_outer_certified_marker
    scope "source-theorem-extraction" "end";
  theorems;;

let candle_action296_fixed_outer_certified_sources_1 =
  candle_action296_fixed_outer_certified_sources
    "candidate-boxes-1" candle_action296_fixed_outer_certified_result_1
    candle_action296_stable_batch_prove_cells_1;;
let candle_action296_fixed_outer_certified_sources_8 =
  candle_action296_fixed_outer_certified_sources
    "candidate-boxes-8" candle_action296_fixed_outer_certified_result_8
    candle_action296_stable_batch_prove_cells_8;;
let candle_action296_fixed_outer_certified_sources_32 =
  candle_action296_fixed_outer_certified_sources
    "candidate-boxes-32" candle_action296_fixed_outer_certified_result_32
    candle_action296_stable_batch_prove_cells_32;;

let candle_action296_fixed_outer_certified_digest theorems =
  Digest.to_hex
    (Digest.string (String.concat "\n" (map string_of_thm theorems)));;

let candle_action296_fixed_outer_certified_digest_1 =
  candle_action296_fixed_outer_certified_digest
    candle_action296_fixed_outer_certified_sources_1;;
let candle_action296_fixed_outer_certified_digest_8 =
  candle_action296_fixed_outer_certified_digest
    candle_action296_fixed_outer_certified_sources_8;;
let candle_action296_fixed_outer_certified_digest_32 =
  candle_action296_fixed_outer_certified_digest
    candle_action296_fixed_outer_certified_sources_32;;

let candle_action296_fixed_outer_certified_expect_rejection label intervals =
  let rejected =
    try
      let _ =
        candle_q_dim_taylor_model_fixed_outer_stable_batch_prove_six
          candle_action296_plan_prepared intervals
          candle_action296_stable_batch_prove_cells_1 in
      false
    with Failure _ -> true in
  if not rejected then
    failwith
      ("action296 fixed outer certified: negative test accepted " ^ label);;

let _ =
  candle_action296_stable_batch_prove_scope := "candidate-adversarial";
  candle_action296_fixed_outer_certified_marker
    "candidate-adversarial" "payload-cardinality" "begin";
  candle_action296_fixed_outer_certified_expect_rejection
    "missing-whole-box-payload"
    (tl candle_action296_stable_batch_prove_box_intervals_value);
  candle_action296_fixed_outer_certified_expect_rejection
    "extra-whole-box-payload"
    (hd candle_action296_stable_batch_prove_box_intervals_value ::
     candle_action296_stable_batch_prove_box_intervals_value);
  candle_action296_fixed_outer_certified_marker
    "candidate-adversarial" "payload-cardinality" "end";;

let candle_action296_fixed_outer_certified_all_sources =
  candle_action296_fixed_outer_certified_sources_1 @
  candle_action296_fixed_outer_certified_sources_8 @
  candle_action296_fixed_outer_certified_sources_32;;

let candle_action296_fixed_outer_certified_axioms_after = axioms ();;

if length candle_action296_fixed_outer_certified_all_sources <> 41 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [])
       candle_action296_fixed_outer_certified_all_sources) ||
   hyp candle_action296_fixed_outer_certified_result_1.
         stable_batch_accept_theorem <> [] ||
   hyp candle_action296_fixed_outer_certified_result_8.
         stable_batch_accept_theorem <> [] ||
   hyp candle_action296_fixed_outer_certified_result_32.
         stable_batch_accept_theorem <> [] ||
   candle_action296_fixed_outer_certified_digest_1 <>
     candle_action296_stable_batch_prove_source_digest_1 ||
   candle_action296_fixed_outer_certified_digest_8 <>
     candle_action296_stable_batch_prove_source_digest_8 ||
   candle_action296_fixed_outer_certified_digest_32 <>
     candle_action296_stable_batch_prove_source_digest_32 ||
   length candle_action296_fixed_outer_certified_axioms_after <>
     length candle_action296_fixed_outer_certified_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_outer_certified_axioms_before)
       candle_action296_fixed_outer_certified_axioms_after) then
  failwith "action296 fixed outer certified: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_OUTER_CERTIFIED_RESULT boxes=1,8,32" ^
   " accepted=41 computes=3 source_theorems=41 stable_programs=1" ^
   " sqrt_slots=7 adversarial_rejections=2" ^
   " source_digest_1=" ^
     candle_action296_fixed_outer_certified_digest_1 ^
   " source_digest_8=" ^
     candle_action296_fixed_outer_certified_digest_8 ^
   " source_digest_32=" ^
     candle_action296_fixed_outer_certified_digest_32);;
print_endline
  "CANDLE_CV_ACTION296_FIXED_OUTER_CERTIFIED_OK DEVELOPMENT_NON_RELEASE";;
