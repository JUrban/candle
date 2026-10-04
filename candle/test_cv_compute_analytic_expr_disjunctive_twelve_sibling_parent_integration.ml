(* Twelve shared-program reflected siblings through the real production parent. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_case16479_shared_complete.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_shared_complete.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_second_sibling_batch_shared_complete.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_shared_complete.ml";;

module Test_cv_compute_analytic_expr_disjunctive_twelve_sibling_parent_integration = struct

open Test_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_handoff;;
open Test_cv_compute_analytic_expr_disjunctive_case16479_shared_complete;;
open Test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_shared_complete;;
open Test_cv_compute_analytic_expr_disjunctive_second_sibling_batch_shared_complete;;
open Test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_shared_complete;;
open Candle_cv_analytic_expr_disjunctive_case16479_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16597_plan;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_second_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_third_sibling_batch;;

let candle_disjunctive_twelve_parent_label = "prep-8293089898";;

let candle_disjunctive_twelve_parent_formula tm =
  match snd (strip_comb tm) with
  | [_;_;formula] -> formula
  | _ -> failwith "disjunctive twelve parent: malformed provider leaf";;

let _ =
  let axioms_before = axioms () in
  if !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> 0 ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 0 ||
     !Serialization.nonlinear_legacy_import_attempts <> 0 ||
     !Serialization.nonlinear_legacy_import_successes <> 0 ||
     Serialization.has_deserialization_axiom ()
  then failwith "disjunctive twelve parent: dirty import boundary";
  let source_target =
    Break_case_exec.get_ineq candle_disjunctive_twelve_parent_label in
  let _,_,needs_delta =
    Break_case_exec.get_case candle_disjunctive_twelve_parent_label in
  let target =
    if needs_delta candle_disjunctive_twelve_parent_label then
      mk_imp (`delta_ineq_v6:bool`,source_target)
    else source_target in
  let leaf_count =
    Break_case_exec.count_iargs candle_disjunctive_twelve_parent_label in
  if leaf_count <> 333 then
    failwith "disjunctive twelve parent: leaf cardinality drift";
  let reflected =
    [(149,candle_disjunctive_case16479_target,
          candle_disjunctive_case16479_theorem);
     (264,candle_disjunctive_case16594_target,
          candle_disjunctive_case16594_complete_full_source_theorem ());
     (267,candle_disjunctive_case16597_target,
          candle_disjunctive_case16597_theorem);
     (287,candle_disjunctive_case16617_target,
          candle_disjunctive_case16617_theorem);
     (263,candle_disjunctive_case16593_target,
          candle_disjunctive_case16593_theorem);
     (252,candle_disjunctive_case16582_target,
          candle_disjunctive_case16582_theorem);
     (152,candle_disjunctive_case16482_target,
          candle_disjunctive_case16482_theorem);
     (326,candle_disjunctive_case16656_target,
          candle_disjunctive_case16656_theorem);
     (317,candle_disjunctive_case16647_target,
          candle_disjunctive_case16647_theorem);
     (150,candle_disjunctive_case16480_target,
          candle_disjunctive_case16480_theorem);
     (9,candle_disjunctive_case16339_target,
          candle_disjunctive_case16339_theorem);
     (265,candle_disjunctive_case16595_target,
          candle_disjunctive_case16595_theorem)] in
  let reference_formula =
    candle_disjunctive_twelve_parent_formula candle_disjunctive_case16594_target in
  if not
       (List.for_all
         (fun (_,proposition,theorem) ->
           aconv (candle_disjunctive_twelve_parent_formula proposition)
             reference_formula &&
           hyp theorem = [] && aconv (concl theorem) proposition)
         reflected) then
    failwith "disjunctive twelve parent: reflected theorem mismatch";
  let shared_source_attempts = ref 0 in
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun role index proposition ->
       if role <> candle_disjunctive_twelve_parent_label then None
       else if not
           (aconv
             (candle_disjunctive_twelve_parent_formula proposition)
             reference_formula) then
         failwith "disjunctive twelve parent: source formula drift"
       else begin
         shared_source_attempts := !shared_source_attempts + 1;
         try
           let _,expected,theorem =
             List.find
               (fun (expected_index,_,_) -> expected_index = index)
               reflected in
           if aconv proposition expected then Some theorem
           else failwith "disjunctive twelve parent: indexed proposition drift"
         with Not_found -> None
       end);
  let serialization_before = !Serialization.use_serialization in
  Serialization.use_serialization := true;
  let parent =
    Break_case_exec.prove_serialized_idv
      candle_disjunctive_twelve_parent_label in
  Serialization.use_serialization := serialization_before;
  Break_case_exec.candle_nonlinear_reflected_leaf_provider :=
    (fun _ _ _ -> None);
  let axioms_after = axioms () in
  let axiom_growth = length axioms_after - length axioms_before in
  let digest = Digest.to_hex (Digest.string (string_of_thm parent)) in
  if hyp parent <> [] ||
     not (aconv (concl parent) target) ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_attempts <> leaf_count ||
     !Break_case_exec.candle_nonlinear_reflected_leaf_successes <> 12 ||
     !shared_source_attempts <> leaf_count ||
     !Serialization.nonlinear_legacy_import_attempts <> leaf_count - 12 ||
     !Serialization.nonlinear_legacy_import_successes <> leaf_count - 12 ||
     !Break_case_exec.candle_nonlinear_iarg_leaf_visits <> 111 ||
     not (Serialization.has_deserialization_axiom ()) ||
     axiom_growth <> 1 ||
     digest <> "e543c7135f766094f4c885571b72cb4a" then
    failwith "disjunctive twelve parent: parent validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_TWELVE_PARENT_INTEGRATION_OK" ^
     " DEVELOPMENT_NON_RELEASE parent=prep-8293089898 leaves=333" ^
     " reflected_leaves=12 legacy_siblings=321 shared_direct_programs=2" ^
     " shared_source_leaves=" ^ string_of_int !shared_source_attempts ^
     " iarg_leaf_visits=111 assumptions=0 axiom_growth=" ^
     string_of_int axiom_growth ^ " theorem_digest=" ^ digest);;

end;;
