(* ========================================================================== *)
(* Topology-only capture for the complete registered case-10173 certificate. *)
(*                                                                            *)
(* The numerical result is supplied separately by the registered ledger.     *)
(* This benchmark measures only the compact 8,345-token replay over the same  *)
(* 4,173 encoded jobs and retains its closed compute theorem for the final    *)
(* logical correspondence handoff.                                            *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_input.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_topology.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_topology;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_input;;

type candle_case10173_historical_registered_topology_capture = {
  registered_topology_tokens : term;
  registered_topology_encoded_tokens : term;
  registered_topology_encoded_root : term;
  registered_topology_compute_theorem : thm;
  registered_topology_elapsed_seconds : float;
};;

let candle_case10173_registered_topology_encode_token = function
  | Candle_case10173_complete_leaf -> `Cexp_num 0`
  | Candle_case10173_complete_glue axis ->
      candle_q_dim_stable_program_cval_pair
        (mk_comb (`Cexp_num`,mk_small_numeral axis)) `Cexp_num 0`;;

let candle_case10173_registered_topology_logical_token = function
  | Candle_case10173_complete_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_case10173_complete_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let candle_case10173_historical_registered_topology_capture_state :
    candle_case10173_historical_registered_topology_capture option ref =
  ref None;;

let candle_case10173_historical_registered_topology_capture () =
  match !candle_case10173_historical_registered_topology_capture_state with
  | Some captured -> captured
  | None ->
      let axioms_before = axioms () in
      let ledger = candle_case10173_historical_registered_ledger_input () in
      let token_data = candle_case10173_complete_token_data () in
      let leaf =
        `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` in
      let tokens =
        mk_list
          (map candle_case10173_registered_topology_logical_token token_data,
           type_of leaf) in
      let encoded_tokens =
        candle_q_dim_stable_program_cval_list
          (map candle_case10173_registered_topology_encode_token token_data) in
      let call =
        list_mk_comb
          (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
           [`Cexp_num 6`;encoded_tokens;
            ledger.registered_ledger_full_encoded_jobs;`Cexp_num 0`]) in
      print_endline
        "CANDLE_REGISTERED_TOPOLOGY_COMPUTE_BEGIN tokens=8345 jobs=4173";
      let started = Unix.gettimeofday () in
      let theorem =
        Kernel.compute
          (COMPUTE_INIT_THMS,
           candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs)
          call in
      let elapsed = Unix.gettimeofday () -. started in
      print_endline
        ("CANDLE_REGISTERED_TOPOLOGY_COMPUTE_END elapsed_seconds=" ^
         string_of_float elapsed);
      let success,payload =
        candle_q_dim_stable_program_dest_cval_pair
          "case10173 registered topology result" (rand (concl theorem)) in
      let remaining,stack =
        candle_q_dim_stable_program_dest_cval_pair
          "case10173 registered topology payload" payload in
      let root,tail =
        candle_q_dim_stable_program_dest_cval_pair
          "case10173 registered topology stack" stack in
      let axioms_after = axioms () in
      if length token_data <> 8345 || hyp theorem <> [] ||
         not (aconv (lhand (concl theorem)) call) ||
         not (aconv success `Cexp_num 1`) ||
         not (aconv remaining `Cexp_num 0`) ||
         not (aconv tail `Cexp_num 0`) ||
         length axioms_after <> length axioms_before ||
         not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
      then failwith "case10173 registered topology capture: validation failed";
      let captured = {
        registered_topology_tokens = tokens;
        registered_topology_encoded_tokens = encoded_tokens;
        registered_topology_encoded_root = root;
        registered_topology_compute_theorem = theorem;
        registered_topology_elapsed_seconds = elapsed;
      } in
      candle_case10173_historical_registered_topology_capture_state :=
        Some captured;
      print_endline
        "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_TOPOLOGY_CAPTURE_OK DEVELOPMENT_NON_RELEASE tokens=8345 jobs=4173 remaining=0 active_roots=1 assumptions=0 axiom_growth=0";
      captured;;

end;;
