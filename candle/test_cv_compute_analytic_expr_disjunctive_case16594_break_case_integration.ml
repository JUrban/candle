(* ========================================================================== *)
(* Genuine case-16594 theorem through the production nonlinear leaf hook.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Only exact role/index/proposition identity is *)
(* reflected; every sibling remains on the authenticated legacy importer.    *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_break_case_integration = struct

open Test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;

let candle_disjunctive_case16594_break_case_label = "prep-8293089898";;
let candle_disjunctive_case16594_break_case_index = 264;;

let candle_disjunctive_case16594_break_case_bool value =
  if value then "true" else "false";;

let _ =
  let axioms_before = axioms () in
  if !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 0 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 0 ||
     !Serialization.nonlinear_legacy_import_attempts <> 0 ||
     !Serialization.nonlinear_legacy_import_successes <> 0 ||
     Serialization.has_deserialization_axiom ()
  then failwith "case16594 break-case integration: dirty import boundary";
  let source_target =
    Break_case_exec.get_ineq candle_disjunctive_case16594_break_case_label in
  let _,_,needs_delta =
    Break_case_exec.get_case candle_disjunctive_case16594_break_case_label in
  let target =
    if needs_delta candle_disjunctive_case16594_break_case_label then
      mk_imp (`delta_ineq_v6:bool`,source_target)
    else source_target in
  let leaf_count =
    Break_case_exec.count_iargs candle_disjunctive_case16594_break_case_label in
  if leaf_count <> 333 then
    failwith "case16594 break-case integration: leaf cardinality drift";
  let reflected_leaf_term = candle_disjunctive_case16594_target in
  let reflected_leaf_theorem =
    candle_disjunctive_case16594_complete_full_source_theorem () in
  if hyp reflected_leaf_theorem <> [] ||
     not (aconv (concl reflected_leaf_theorem) reflected_leaf_term)
  then failwith "case16594 break-case integration: reflected leaf mismatch";
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun role index proposition ->
       if role = candle_disjunctive_case16594_break_case_label &&
          index = candle_disjunctive_case16594_break_case_index then
         if aconv proposition reflected_leaf_term then
           Some reflected_leaf_theorem
         else failwith "case16594 break-case integration: leaf drift"
       else None);
  let serialization_before = !Serialization.use_serialization in
  Serialization.use_serialization := true;
  let parent =
    Break_case_exec.prove_serialized_idv
      candle_disjunctive_case16594_break_case_label in
  Serialization.use_serialization := serialization_before;
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun _ _ _ -> None);
  let axioms_after = axioms () in
  let axiom_growth = length axioms_after - length axioms_before in
  let digest = Digest.to_hex (Digest.string (string_of_thm parent)) in
  print_endline
    ("CANDLE_CV_CASE16594_BREAK_CASE_INTEGRATION_STATE" ^
     " needs_delta=" ^
     candle_disjunctive_case16594_break_case_bool
       (needs_delta candle_disjunctive_case16594_break_case_label) ^
     " hypotheses=" ^ string_of_int (length (hyp parent)) ^
     " target_match=" ^
     candle_disjunctive_case16594_break_case_bool
       (aconv (concl parent) target) ^
     " reflected_attempts=" ^
     string_of_int
       !Break_case_exec.candle_nonlinear_reflected_leaf_attempts ^
     " reflected_successes=" ^
     string_of_int
       !Break_case_exec.candle_nonlinear_reflected_leaf_successes ^
     " legacy_attempts=" ^
     string_of_int !Serialization.nonlinear_legacy_import_attempts ^
     " legacy_successes=" ^
     string_of_int !Serialization.nonlinear_legacy_import_successes ^
     " iarg_leaf_visits=" ^
     string_of_int !Break_case_exec.candle_nonlinear_iarg_leaf_visits ^
     " deserialization_axiom=" ^
     candle_disjunctive_case16594_break_case_bool
       (Serialization.has_deserialization_axiom ()) ^
     " axiom_growth=" ^ string_of_int axiom_growth ^
     " theorem_digest=" ^ digest);
  if hyp parent <> [] ||
     not (aconv (concl parent) target) ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> leaf_count ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 1 ||
     !Serialization.nonlinear_legacy_import_attempts <> leaf_count - 1 ||
     !Serialization.nonlinear_legacy_import_successes <> leaf_count - 1 ||
     not (Serialization.has_deserialization_axiom ()) ||
     axiom_growth <> 1
  then failwith "case16594 break-case integration: parent validation failed";
  print_endline
    ("CANDLE_CV_CASE16594_BREAK_CASE_INTEGRATION_OK" ^
     " DEVELOPMENT_NON_RELEASE parent=prep-8293089898 leaves=" ^
     string_of_int leaf_count ^
     " reflected_leaves=1 legacy_siblings=" ^
     string_of_int (leaf_count - 1) ^
     " iarg_leaf_visits=" ^
     string_of_int !Break_case_exec.candle_nonlinear_iarg_leaf_visits ^
     " assumptions=0 axiom_growth=" ^ string_of_int axiom_growth ^
     " theorem_digest=" ^ digest);;

end;;
