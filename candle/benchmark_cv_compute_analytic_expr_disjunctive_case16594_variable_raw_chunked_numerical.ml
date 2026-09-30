(* Complete numerical case-16594 workload in bounded canonical raw chunks.  *)
(* This deliberately does not claim the still-missing compact root theorem. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_chunked_numerical = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let rec candle_disjunctive_case16594_variable_raw_split_chunks size items =
  if size <= 0 then invalid_arg "case16594 variable raw chunk size";
  let rec take remaining prefix suffix =
    if remaining = 0 then rev prefix,suffix
    else
      match suffix with
      | [] -> rev prefix,[]
      | head :: tail -> take (remaining - 1) (head :: prefix) tail in
  match items with
  | [] -> []
  | _ ->
      let prefix,suffix = take size [] items in
      prefix ::
      candle_disjunctive_case16594_variable_raw_split_chunks size suffix;;

let candle_disjunctive_case16594_variable_raw_cell_chunks =
  candle_disjunctive_case16594_variable_raw_split_chunks 32
    candle_disjunctive_case16594_variable_raw_plan_cells;;

let candle_disjunctive_case16594_variable_raw_chunk_axioms_before =
  axioms ();;
let candle_disjunctive_case16594_variable_raw_chunk_digests =
  ref ([]:string list);;
let candle_disjunctive_case16594_variable_raw_chunk_cells_checked = ref 0;;

let _ =
  if length candle_disjunctive_case16594_variable_raw_cell_chunks <> 28 then
    failwith "case16594 variable raw chunked: chunk count mismatch";
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-variable-raw-chunked" ^
         " phase=" ^ event));
  let index = ref 0 in
  List.iter
    (fun cells ->
      let current = !index in
      let count = length cells in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_CHUNK" ^
         " event=begin index=" ^ string_of_int current ^
         " total=28 cells=" ^ string_of_int count);
      let result =
        candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
          candle_disjunctive_case16594_engine_state.family_engine_prepared
          cells in
      let theorem = result.variable_raw_accept_theorem in
      if hyp theorem <> [] then
        failwith "case16594 variable raw chunked: theorem assumptions";
      let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
      candle_disjunctive_case16594_variable_raw_chunk_digests :=
        digest :: !candle_disjunctive_case16594_variable_raw_chunk_digests;
      candle_disjunctive_case16594_variable_raw_chunk_cells_checked :=
        !candle_disjunctive_case16594_variable_raw_chunk_cells_checked + count;
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_CHUNK" ^
         " event=end index=" ^ string_of_int current ^
         " total=28 cells=" ^ string_of_int count ^
         " theorem_digest=" ^ digest);
      index := current + 1)
    candle_disjunctive_case16594_variable_raw_cell_chunks;
  let axioms_after = axioms () in
  if !index <> 28 ||
     !candle_disjunctive_case16594_variable_raw_chunk_cells_checked <> 875 ||
     length !candle_disjunctive_case16594_variable_raw_chunk_digests <> 28 ||
     length axioms_after <>
       length candle_disjunctive_case16594_variable_raw_chunk_axioms_before ||
     not
       (List.for_all
         (fun theorem ->
           List.mem theorem
             candle_disjunctive_case16594_variable_raw_chunk_axioms_before)
         axioms_after) then
    failwith "case16594 variable raw chunked: final validation failed";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_NUMERICAL_COMPLETE_RESULT authenticated_leaves=860 numerical_cells=875 chunks=28 numerical_computes=28 host_representation_theorems=0 combined_root_theorem=0";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_NUMERICAL_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;

end;;
