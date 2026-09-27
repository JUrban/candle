(* ========================================================================== *)
(* One-verdict proof batch over eight genuine action-296 boxes.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_benchmark_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

let candle_action296_fixed_algebraic_batch_axioms_before = axioms ();;

let candle_action296_fixed_algebraic_batch_cells =
  map
    (fun (variant,lower,upper) ->
      {
        fixed_algebraic_batch_center_variant = variant;
        fixed_algebraic_batch_lower = lower;
        fixed_algebraic_batch_upper = upper;
      })
    candle_action296_instruction_profile_cases;;

let candle_action296_fixed_algebraic_batch_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-algebraic-batch" ^
     " scope=boxes-8 phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      if event =
           "fixed-algebraic-certified-taylor-batch-preparation-begin" then
        candle_action296_fixed_algebraic_batch_marker
          "adapter-preparation" "begin"
      else if event =
           "fixed-algebraic-certified-taylor-batch-preparation-end" then
        candle_action296_fixed_algebraic_batch_marker
          "adapter-preparation" "end"
      else if event =
           "fixed-algebraic-certified-taylor-batch-compute-begin" then
        candle_action296_fixed_algebraic_batch_marker
          "kernel-compute" "begin"
      else if event =
           "fixed-algebraic-certified-taylor-batch-compute-end" then
        candle_action296_fixed_algebraic_batch_marker
          "kernel-compute" "end"
      else if event =
           "fixed-algebraic-certified-taylor-batch-handoff-begin" then
        candle_action296_fixed_algebraic_batch_marker
          "theorem-handoff" "begin"
      else if event =
           "fixed-algebraic-certified-taylor-batch-handoff-end" then
        candle_action296_fixed_algebraic_batch_marker
          "theorem-handoff" "end"
      else ());;

let _ =
  candle_action296_fixed_algebraic_batch_marker
    "one-verdict-proof" "begin";;
let candle_action296_fixed_algebraic_batch_result_ref :
    candle_q_dim_taylor_model_fixed_algebraic_batch_result_six option ref =
  ref None;;
let _ =
  candle_action296_fixed_algebraic_batch_result_ref :=
    Some
      (candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
        candle_action296_instruction_profile_box_prepared
        candle_action296_fixed_algebraic_batch_cells);;
let _ =
  candle_action296_fixed_algebraic_batch_marker
    "one-verdict-proof" "end";;

let candle_action296_fixed_algebraic_batch_result () =
  match !candle_action296_fixed_algebraic_batch_result_ref with
  | Some result -> result
  | None -> failwith "action296 fixed algebraic batch: missing result";;

let candle_action296_fixed_algebraic_batch_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm
        (candle_action296_fixed_algebraic_batch_result ()).
          fixed_algebraic_batch_accept_theorem));;

let _ =
  candle_action296_fixed_algebraic_batch_marker
    "cell-source-extraction" "begin";;
let candle_action296_fixed_algebraic_batch_sources_ref : thm list option ref =
  ref None;;
let _ =
  candle_action296_fixed_algebraic_batch_sources_ref :=
    Some
      (map
        (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
          (candle_action296_fixed_algebraic_batch_result ()))
        candle_action296_fixed_algebraic_batch_cells);;
let _ =
  candle_action296_fixed_algebraic_batch_marker
    "cell-source-extraction" "end";;

let candle_action296_fixed_algebraic_batch_sources () =
  match !candle_action296_fixed_algebraic_batch_sources_ref with
  | Some sources -> sources
  | None -> failwith "action296 fixed algebraic batch: missing sources";;

let candle_action296_fixed_algebraic_batch_source_digest =
  Digest.to_hex
    (Digest.string
      (String.concat "\n"
        (map string_of_thm
          (candle_action296_fixed_algebraic_batch_sources ()))));;

let candle_action296_fixed_algebraic_batch_axioms_after = axioms ();;

if length candle_action296_fixed_algebraic_batch_cells <> 8 ||
   length
     (candle_action296_fixed_algebraic_batch_result ()).
       fixed_algebraic_batch_cells <> 8 ||
   candle_action296_fixed_algebraic_batch_digest <>
     "6952df94179b05c1e664b2ad9fe4f838" ||
   candle_action296_fixed_algebraic_batch_source_digest <>
     "7ae9333377ccb01b6087a9c71d155779" ||
   length (candle_action296_fixed_algebraic_batch_sources ()) <> 8 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [])
       (candle_action296_fixed_algebraic_batch_sources ())) ||
   hyp
     (candle_action296_fixed_algebraic_batch_result ()).
       fixed_algebraic_batch_accept_theorem <> [] ||
   length candle_action296_fixed_algebraic_batch_axioms_after <>
     length candle_action296_fixed_algebraic_batch_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_algebraic_batch_axioms_before)
       candle_action296_fixed_algebraic_batch_axioms_after) then
  failwith "action296 fixed algebraic batch: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_BATCH_RESULT boxes=8" ^
   " accepted=8 computes=1 theorem_digest=" ^
   candle_action296_fixed_algebraic_batch_digest ^
   " source_digest=" ^
   candle_action296_fixed_algebraic_batch_source_digest);;
print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_BATCH_OK DEVELOPMENT_NON_RELEASE";;
