(* ========================================================================== *)
(* Checkpointable reflected proof state for the 788-leaf disjunctive case.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The ordinary verifier plan fixes leaf order,  *)
(* selected function, and exact domains.  Each call advances monotonically   *)
(* and retains only kernel theorems plus compact measurements.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_family_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;

type candle_disjunctive_family_leaf_result = {
  disjunctive_family_leaf_index : int;
  disjunctive_family_leaf_attempts : int;
  disjunctive_family_leaf_proof : candle_disjunctive_fixed_outer_result;
};;

let candle_disjunctive_family_axioms_before = axioms ();;
let candle_disjunctive_family_prepared =
  List.nth candle_disjunctive_plan_prepared 1;;
let candle_disjunctive_family_function_term =
  candle_disjunctive_fixed_outer_function_term
    candle_disjunctive_family_prepared;;
let candle_disjunctive_family_point_plan =
  candle_q_dim_taylor_model_point_plan_six
    candle_disjunctive_family_prepared;;

let candle_disjunctive_family_results =
  ref ([]:candle_disjunctive_family_leaf_result list);;
let candle_disjunctive_family_next_index = ref 0;;
let candle_disjunctive_family_total_attempts = ref 0;;
let candle_disjunctive_family_total_cells = ref 0;;

if candle_disjunctive_fixed_outer_point_plan_program_count
     candle_disjunctive_family_point_plan <> 10 ||
   length candle_disjunctive_leaf_grouping_leaves <> 788 then
  failwith "disjunctive family proof: support identity drift";;

let candle_disjunctive_family_validate index leaf result =
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass
      (concl result.disjunctive_fixed_outer_theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl leaf.disjunctive_leaf_domain) in
  if leaf.disjunctive_leaf_function_index <> 1 ||
     functions <> [candle_disjunctive_family_function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp result.disjunctive_fixed_outer_theorem <> [] then
    failwith
      ("disjunctive family proof: theorem mismatch at leaf " ^
       string_of_int index);;

let candle_disjunctive_family_prove_one index =
  if index <> !candle_disjunctive_family_next_index ||
     index < 0 || index >= 788 then
    failwith "disjunctive family proof: nonsequential leaf request";
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves index in
  let attempts = ref 0 in
  let result =
    candle_disjunctive_fixed_outer_prove
      candle_disjunctive_family_prepared
      candle_disjunctive_family_point_plan
      ("family-leaf-" ^ string_of_int index) attempts 12
      leaf.disjunctive_leaf_domain in
  candle_disjunctive_family_validate index leaf result;
  let stored =
    {disjunctive_family_leaf_index = index;
     disjunctive_family_leaf_attempts = !attempts;
     disjunctive_family_leaf_proof = result} in
  candle_disjunctive_family_results :=
    stored :: !candle_disjunctive_family_results;
  candle_disjunctive_family_next_index := index + 1;
  candle_disjunctive_family_total_attempts :=
    !candle_disjunctive_family_total_attempts + !attempts;
  candle_disjunctive_family_total_cells :=
    !candle_disjunctive_family_total_cells +
    result.disjunctive_fixed_outer_cells;
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FAMILY_LEAF_RESULT" ^
     " leaf=" ^ string_of_int index ^
     " function=1 attempts=" ^ string_of_int !attempts ^
     " cells=" ^ string_of_int result.disjunctive_fixed_outer_cells ^
     " max_depth=" ^
     string_of_int result.disjunctive_fixed_outer_max_depth ^
     " theorem_digest=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm result.disjunctive_fixed_outer_theorem)));;

let candle_disjunctive_family_validate_state () =
  let axioms_after = axioms () in
  if length !candle_disjunctive_family_results <>
       !candle_disjunctive_family_next_index ||
     length axioms_after <> length candle_disjunctive_family_axioms_before ||
     not
       (List.for_all
         (fun theorem ->
           List.mem theorem candle_disjunctive_family_axioms_before)
         axioms_after) then
    failwith "disjunctive family proof: checkpoint state invalid";;

let candle_disjunctive_family_prove_next count =
  if count <= 0 then failwith "disjunctive family proof: empty chunk";
  let requested = !candle_disjunctive_family_next_index + count in
  let target = if requested > 788 then 788 else requested in
  let rec advance () =
    if !candle_disjunctive_family_next_index < target then begin
      candle_disjunctive_family_prove_one
        !candle_disjunctive_family_next_index;
      advance ()
    end in
  advance ();
  candle_disjunctive_family_validate_state ();
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FAMILY_PROGRESS" ^
     " proved=" ^ string_of_int !candle_disjunctive_family_next_index ^
     "/788 total_attempts=" ^
     string_of_int !candle_disjunctive_family_total_attempts ^
     " total_cells=" ^
     string_of_int !candle_disjunctive_family_total_cells ^
     " retained_theorems=" ^
     string_of_int (length !candle_disjunctive_family_results));;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-family" ^
       " scope=proof leaf=" ^
       string_of_int !candle_disjunctive_family_next_index ^
       " phase=" ^ event));;

print_endline
  "CANDLE_CV_DISJUNCTIVE_FAMILY_SUPPORT_OK next=0/788 DEVELOPMENT_NON_RELEASE";;

end;;
