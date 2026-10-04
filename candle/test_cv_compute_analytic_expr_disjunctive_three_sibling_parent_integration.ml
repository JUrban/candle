(* Three same-program reflected siblings through the real production parent. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_case16479_shared_complete.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete.ml";;

module Test_cv_compute_analytic_expr_disjunctive_three_sibling_parent_integration = struct

open Test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff;;
open Test_cv_compute_analytic_expr_disjunctive_case16479_shared_complete;;
open Test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete;;
open Candle_cv_analytic_expr_disjunctive_case16479_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16597_plan;;

let candle_disjunctive_three_parent_label = "prep-8293089898";;

let candle_disjunctive_three_parent_formula tm =
  match snd (strip_comb tm) with
  | [_;_;formula] -> formula
  | _ -> failwith "disjunctive three parent: malformed provider leaf";;

let _ =
  let axioms_before = axioms () in
  if !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 0 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 0 ||
     !Serialization.nonlinear_legacy_import_attempts <> 0 ||
     !Serialization.nonlinear_legacy_import_successes <> 0 ||
     Serialization.has_deserialization_axiom ()
  then failwith "disjunctive three parent: dirty import boundary";
  let source_target =
    Break_case_exec.get_ineq candle_disjunctive_three_parent_label in
  let _,_,needs_delta =
    Break_case_exec.get_case candle_disjunctive_three_parent_label in
  let target =
    if needs_delta candle_disjunctive_three_parent_label then
      mk_imp (`delta_ineq_v6:bool`,source_target)
    else source_target in
  let leaf_count =
    Break_case_exec.count_iargs candle_disjunctive_three_parent_label in
  if leaf_count <> 333 then
    failwith "disjunctive three parent: leaf cardinality drift";
  let case16479_term = candle_disjunctive_case16479_target
  and case16479_theorem = candle_disjunctive_case16479_theorem
  and case16594_term = candle_disjunctive_case16594_target
  and case16594_theorem =
    candle_disjunctive_case16594_complete_full_source_theorem ()
  and case16597_term = candle_disjunctive_case16597_target
  and case16597_theorem = candle_disjunctive_case16597_theorem in
  let reference_formula =
    candle_disjunctive_three_parent_formula case16594_term in
  let shared_source_attempts = ref 0 in
  if hyp case16479_theorem <> [] ||
     not (aconv (concl case16479_theorem) case16479_term) ||
     hyp case16594_theorem <> [] ||
     not (aconv (concl case16594_theorem) case16594_term) ||
     hyp case16597_theorem <> [] ||
     not (aconv (concl case16597_theorem) case16597_term) then
    failwith "disjunctive three parent: reflected theorem mismatch";
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun role index proposition ->
       if role <> candle_disjunctive_three_parent_label then None
       else if not
           (aconv
             (candle_disjunctive_three_parent_formula proposition)
             reference_formula) then
         failwith "disjunctive three parent: source formula drift"
       else let _ = shared_source_attempts := !shared_source_attempts + 1 in
       if index = candle_disjunctive_case16479_index then
         if aconv proposition case16479_term then Some case16479_theorem
         else failwith "disjunctive three parent: index-149 drift"
       else if index = 264 then
         if aconv proposition case16594_term then Some case16594_theorem
         else failwith "disjunctive three parent: index-264 drift"
       else if index = candle_disjunctive_case16597_index then
         if aconv proposition case16597_term then Some case16597_theorem
         else failwith "disjunctive three parent: index-267 drift"
       else None);
  let serialization_before = !Serialization.use_serialization in
  Serialization.use_serialization := true;
  let parent =
    Break_case_exec.prove_serialized_idv
      candle_disjunctive_three_parent_label in
  Serialization.use_serialization := serialization_before;
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun _ _ _ -> None);
  let axioms_after = axioms () in
  let axiom_growth = length axioms_after - length axioms_before in
  let digest = Digest.to_hex (Digest.string (string_of_thm parent)) in
  if hyp parent <> [] ||
     not (aconv (concl parent) target) ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> leaf_count ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 3 ||
     !shared_source_attempts <> leaf_count ||
     !Serialization.nonlinear_legacy_import_attempts <> leaf_count - 3 ||
     !Serialization.nonlinear_legacy_import_successes <> leaf_count - 3 ||
     !Break_case_exec.candle_nonlinear_iarg_leaf_visits <> 111 ||
     not (Serialization.has_deserialization_axiom ()) ||
     axiom_growth <> 1 ||
     digest <> "e543c7135f766094f4c885571b72cb4a" then
    failwith "disjunctive three parent: parent validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_THREE_PARENT_INTEGRATION_OK" ^
     " DEVELOPMENT_NON_RELEASE parent=prep-8293089898 leaves=333" ^
     " reflected_leaves=3 legacy_siblings=330 shared_direct_programs=2" ^
     " shared_source_leaves=" ^ string_of_int !shared_source_attempts ^
     " iarg_leaf_visits=111 assumptions=0 axiom_growth=" ^
     string_of_int axiom_growth ^ " theorem_digest=" ^ digest);;

end;;
