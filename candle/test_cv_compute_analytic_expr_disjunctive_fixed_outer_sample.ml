(* ========================================================================== *)
(* Shared-preparation reflected proof of four ordinary disjunctive leaves.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The sample spans the exact 788-leaf plan.     *)
(* Source preparation and the point plan are built once; each theorem is     *)
(* checked against its authenticated function and domain identity.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml";;

open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;

type candle_disjunctive_sample_result = {
  disjunctive_sample_index : int;
  disjunctive_sample_attempts : int;
  disjunctive_sample_result : candle_disjunctive_fixed_outer_result;
};;

let candle_disjunctive_sample_indices = [0;197;394;787];;

let candle_disjunctive_sample_validate function_term index leaf result =
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass
      (concl result.disjunctive_fixed_outer_theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl leaf.disjunctive_leaf_domain) in
  if leaf.disjunctive_leaf_function_index <> 1 ||
     functions <> [function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp result.disjunctive_fixed_outer_theorem <> [] then
    failwith
      ("disjunctive fixed outer sample: theorem mismatch at leaf " ^
       string_of_int index);;

let candle_disjunctive_sample_prove
    prepared function_term point_plan index =
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves index in
  let attempts = ref 0 in
  let result =
    candle_disjunctive_fixed_outer_prove
      prepared point_plan ("leaf-" ^ string_of_int index) attempts 12
      leaf.disjunctive_leaf_domain in
  candle_disjunctive_sample_validate
    function_term index leaf result;
  let theorem_digest =
    Digest.to_hex
      (Digest.string
        (string_of_thm result.disjunctive_fixed_outer_theorem)) in
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_SAMPLE_LEAF_RESULT" ^
     " leaf=" ^ string_of_int index ^
     " function=1 attempts=" ^ string_of_int !attempts ^
     " cells=" ^ string_of_int result.disjunctive_fixed_outer_cells ^
     " max_depth=" ^
     string_of_int result.disjunctive_fixed_outer_max_depth ^
     " theorem_digest=" ^ theorem_digest);
  {disjunctive_sample_index = index;
   disjunctive_sample_attempts = !attempts;
   disjunctive_sample_result = result};;

let _ =
  let axioms_before = axioms () in
  let prepared = List.nth candle_disjunctive_plan_prepared 1 in
  let function_term =
    candle_disjunctive_fixed_outer_function_term prepared in
  let point_plan = candle_q_dim_taylor_model_point_plan_six prepared in
  if candle_disjunctive_fixed_outer_point_plan_program_count point_plan <> 10
  then
    failwith "disjunctive fixed outer sample: point-plan slot drift";
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-fixed-outer-sample" ^
         " scope=proof phase=" ^ event));
  let results =
    map
      (candle_disjunctive_sample_prove
        prepared function_term point_plan)
      candle_disjunctive_sample_indices in
  let axioms_after = axioms () in
  if length results <> 4 ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "disjunctive fixed outer sample: final validation failed";
  let attempts =
    itlist
      (fun result total -> result.disjunctive_sample_attempts + total)
      results 0 in
  let cells =
    itlist
      (fun result total ->
        result.disjunctive_sample_result.disjunctive_fixed_outer_cells +
        total)
      results 0 in
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_SAMPLE_RESULT" ^
     " leaves=4 indices=0,197,394,787" ^
     " attempts=" ^ string_of_int attempts ^
     " cells=" ^ string_of_int cells ^
     " shared_point_plan=true");
  print_endline
    "CANDLE_CV_DISJUNCTIVE_SAMPLE_OK DEVELOPMENT_NON_RELEASE";;
