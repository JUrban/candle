(* ========================================================================== *)
(* One-call production fast route to the original case-10173 Flyspeck goal. *)
(*                                                                            *)
(* Unlike the older 261-chunk ledger regression, this test presents the exact *)
(* complete checked-jobs call registered by the authenticated production      *)
(* evaluator.  The numerical theorem therefore has the same call and equation *)
(* identities as the fast kernel branch.                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_registered_original_prove.ml";;
needs "candle/benchmark_cv_compute_registered_hol4_export.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_input.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_registered_full_call_original_prove = struct

open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Candle_cv_analytic_expr_case10173_historical_registered_combine;;
open Candle_cv_analytic_expr_case10173_historical_registered_original_prove;;
open Candle_cv_analytic_expr_case10173_historical_registered_topology_prove;;
open Benchmark_cv_compute_registered_hol4_export;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_input;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture;;

let candle_case10173_registered_full_call_timed label action =
  let started = Unix.gettimeofday () in
  print_endline ("CANDLE_REGISTERED_FULL_CALL_" ^ label ^ "_BEGIN");
  let result = action () in
  let elapsed = Unix.gettimeofday () -. started in
  print_endline
    ("CANDLE_REGISTERED_FULL_CALL_" ^ label ^
     "_END elapsed_seconds=" ^ string_of_float elapsed);
  result,elapsed;;

let candle_case10173_registered_full_call_well_formed input =
  let call =
    mk_comb
      (`candle_cv_case10173_hist_jobs_well_formed`,
       input.registered_input_encoded_jobs) in
  let theorem =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_case10173_hist_jobs_well_formed_compute_eqs)
      call in
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`)
  then failwith "case10173 full-call original prove: structural guard failed";
  theorem;;

let _ =
  let axioms_before = axioms () in
  let input,preparation_seconds =
    candle_case10173_registered_full_call_timed "PREPARATION"
      candle_case10173_historical_registered_input in
  let equations,equation_slice_seconds =
    candle_case10173_registered_full_call_timed "EQUATION_SLICE"
      (fun () ->
        candle_registered_equation_slice
          candle_cv_case10173_hist_checked_program_compute_eqs
          input.registered_input_checked_call) in
  let well_formed,structural_seconds =
    candle_case10173_registered_full_call_timed "STRUCTURAL_GUARD"
      (fun () ->
        candle_case10173_registered_full_call_well_formed input) in
  let numerical,numerical_seconds =
    candle_case10173_registered_full_call_timed "REGISTERED_NUMERICAL"
      (fun () ->
        Kernel.compute
          (COMPUTE_INIT_THMS,equations)
          input.registered_input_checked_call) in
  let acceptance,acceptance_seconds =
    candle_case10173_registered_full_call_timed "ACCEPTANCE_HANDOFF"
      (fun () ->
        candle_case10173_hist_registered_acceptance_of_theorems
          input.registered_input_encoded_jobs
          input.registered_input_roots well_formed numerical) in
  let topology,topology_seconds =
    candle_case10173_registered_full_call_timed "TOPOLOGY_COMPUTE"
      candle_case10173_historical_registered_topology_capture in
  let theorem,handoff_seconds =
    candle_case10173_registered_full_call_timed "THEOREM_HANDOFF"
      (fun () ->
        let topology_result =
          candle_case10173_historical_registered_topology_prove
            acceptance.registered_acceptance_encoded_jobs
            acceptance.registered_acceptance_representation topology in
        candle_case10173_historical_registered_original_prove
          acceptance topology topology_result) in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  let call_digest =
    Digest.to_hex
      (Digest.string (string_of_term input.registered_input_checked_call)) in
  let axioms_after = axioms () in
  if length equations <> 344 ||
     acceptance.registered_acceptance_chunk_count <> 1 ||
     hyp numerical <> [] ||
     not
       (aconv
         (lhand (concl numerical))
         input.registered_input_checked_call) ||
     not (aconv (rand (concl numerical)) `Cexp_num 1`) ||
     hyp theorem <> [] ||
     not (aconv (concl theorem) candle_case10173_analytic_target) ||
     digest <> "48c97d39af116042909b7896d0d83123" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 full-call original prove: validation failed";
  let recurring_seconds =
    numerical_seconds +. acceptance_seconds +. topology_seconds +.
    handoff_seconds in
  let total_seconds =
    preparation_seconds +. equation_slice_seconds +. structural_seconds +.
    recurring_seconds in
  print_endline
    ("CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_FULL_CALL_ORIGINAL_PROVE_TEST_OK" ^
     " DEVELOPMENT_NON_RELEASE cells=4173 chunks=1 equations=344" ^
     " assumptions=0 axiom_growth=0 theorem_digest=" ^ digest ^
     " call_digest=" ^ call_digest ^
     " recurring_elapsed_seconds=" ^ string_of_float recurring_seconds ^
     " total_elapsed_seconds=" ^ string_of_float total_seconds);;

end;;
