(* ========================================================================== *)
(* Exact action-296 parent reconstruction through the production leaf hook. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The right sibling deliberately remains on the *)
(* authenticated legacy importer so this test exercises the mixed provider  *)
(* path at Break_case_exec's real reconstruction boundary.                   *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_handoff.ml";;

module Test_cv_compute_analytic_expr_case10173_break_case_integration = struct

open Test_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_handoff;;

let candle_case10173_break_case_label = "prep-8657368829";;

let candle_case10173_break_case_expected_reflected_term =
  Candle_cv_analytic_expr_case10173_fixture.candle_case10173_analytic_target;;

let _ =
  let axioms_before = axioms () in
  if !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 0 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 0 ||
     !Serialization.nonlinear_legacy_import_attempts <> 0 ||
     !Serialization.nonlinear_legacy_import_successes <> 0 ||
     Serialization.has_deserialization_axiom ()
  then
    failwith "case10173 break-case integration: dirty import boundary";
  let target =
    Break_case_exec.get_ineq candle_case10173_break_case_label in
  if Break_case_exec.count_iargs candle_case10173_break_case_label <> 2 then
    failwith "case10173 break-case integration: leaf cardinality drift";
  let reflected_leaf_term =
    candle_case10173_break_case_expected_reflected_term in
  let reflected_leaf_theorem =
    candle_case10173_fixed_nonlinear_complete_source_theorem () in
  if hyp reflected_leaf_theorem <> [] ||
     not (aconv (concl reflected_leaf_theorem) reflected_leaf_term)
  then
    failwith "case10173 break-case integration: reflected leaf mismatch";
  let _ =
    Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
      (fun role index proposition ->
         if role = candle_case10173_break_case_label && index = 1 then
           if aconv proposition reflected_leaf_term then
             Some reflected_leaf_theorem
           else
             failwith
               "case10173 break-case integration: processed leaf drift"
         else None) in
  let serialization_before = !Serialization.use_serialization in
  let _ = Serialization.use_serialization := true in
  let parent =
    Break_case_exec.prove_serialized_idv candle_case10173_break_case_label in
  let _ = Serialization.use_serialization := serialization_before in
  let _ =
    Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
      (fun _ _ _ -> None) in
  let axioms_after = axioms () in
  let axiom_growth = length axioms_after - length axioms_before in
  let digest = Digest.to_hex (Digest.string (string_of_thm parent)) in
  if hyp parent <> [] ||
     not (aconv (concl parent) target) ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 2 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 1 ||
     !Serialization.nonlinear_legacy_import_attempts <> 1 ||
     !Serialization.nonlinear_legacy_import_successes <> 1 ||
     !Break_case_exec.candle_nonlinear_iarg_leaf_visits <> 1 ||
     not (Serialization.has_deserialization_axiom ()) ||
     axiom_growth <> 1
  then failwith "case10173 break-case integration: parent validation failed";
  print_endline
    ("CANDLE_CV_CASE10173_BREAK_CASE_INTEGRATION_OK" ^
     " DEVELOPMENT_NON_RELEASE parent=prep-8657368829 leaves=2" ^
     " reflected_leaves=1 legacy_siblings=1 assumptions=0" ^
     " axiom_growth=" ^ string_of_int axiom_growth ^
     " theorem_digest=" ^ digest);;

end;;
