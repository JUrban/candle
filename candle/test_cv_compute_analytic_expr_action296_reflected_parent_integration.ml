(* ========================================================================== *)
(* Exact action-296 parent reconstruction with both leaves reflected.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This exercises Break_case_exec's production  *)
(* boundary with no serialized theorem import and therefore no new axiom.    *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_action296_fixed_nonlinear_complete_handoff.ml";;
needs "candle/test_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_handoff.ml";;

module Test_cv_compute_analytic_expr_action296_reflected_parent_integration = struct

open Test_cv_compute_analytic_expr_action296_fixed_nonlinear_complete_handoff;;
open Test_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_handoff;;
open Candle_cv_analytic_expr_action296_fixture;;
open Candle_cv_analytic_expr_case10173_fixture;;

let candle_action296_reflected_parent_label = "prep-8657368829";;

let _ =
  let axioms_before = axioms () in
  if !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 0 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 0 ||
     !Serialization.nonlinear_legacy_import_attempts <> 0 ||
     !Serialization.nonlinear_legacy_import_successes <> 0 ||
     Serialization.has_deserialization_axiom ()
  then
    failwith "action296 reflected parent: dirty import boundary";
  let target =
    Break_case_exec.get_ineq candle_action296_reflected_parent_label in
  if Break_case_exec.count_iargs candle_action296_reflected_parent_label <> 2
  then failwith "action296 reflected parent: leaf cardinality drift";
  let right_term = candle_action296_analytic_target in
  let right_theorem =
    candle_action296_fixed_nonlinear_complete_source_theorem () in
  let left_term = candle_case10173_analytic_target in
  let left_theorem =
    candle_case10173_fixed_nonlinear_complete_source_theorem () in
  if hyp right_theorem <> [] ||
     not (aconv (concl right_theorem) right_term) ||
     hyp left_theorem <> [] ||
     not (aconv (concl left_theorem) left_term)
  then failwith "action296 reflected parent: reflected leaf mismatch";
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun role index proposition ->
       if role <> candle_action296_reflected_parent_label then None
       else if index = 0 then
         if aconv proposition right_term then Some right_theorem
         else failwith "action296 reflected parent: right leaf drift"
       else if index = 1 then
         if aconv proposition left_term then Some left_theorem
         else failwith "action296 reflected parent: left leaf drift"
       else None);
  let serialization_before = !Serialization.use_serialization in
  Serialization.use_serialization := true;
  let parent =
    Break_case_exec.prove_serialized_idv
      candle_action296_reflected_parent_label in
  Serialization.use_serialization := serialization_before;
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun _ _ _ -> None);
  let axioms_after = axioms () in
  let axiom_growth = length axioms_after - length axioms_before in
  let digest = Digest.to_hex (Digest.string (string_of_thm parent)) in
  if hyp parent <> [] ||
     not (aconv (concl parent) target) ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 2 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 2 ||
     !Serialization.nonlinear_legacy_import_attempts <> 0 ||
     !Serialization.nonlinear_legacy_import_successes <> 0 ||
     !Break_case_exec.candle_nonlinear_iarg_leaf_visits <> 1 ||
     Serialization.has_deserialization_axiom () ||
     axiom_growth <> 0 ||
     digest <> "82ae96fa6840365b4aac7ec8be40539b"
  then failwith "action296 reflected parent: parent validation failed";
  print_endline
    ("CANDLE_CV_ACTION296_REFLECTED_PARENT_INTEGRATION_OK" ^
     " DEVELOPMENT_NON_RELEASE parent=prep-8657368829 leaves=2" ^
     " reflected_leaves=2 legacy_siblings=0 assumptions=0" ^
     " axiom_growth=" ^ string_of_int axiom_growth ^
     " theorem_digest=" ^ digest);;

end;;
