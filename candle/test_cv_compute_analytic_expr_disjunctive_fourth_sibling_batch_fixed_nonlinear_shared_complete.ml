(* Exact proof of the fourth three siblings from the fixed-nonlinear forests. *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_forests.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_term_order_compat.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_shared_complete = struct

open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_shared_sibling_prepare;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_forests;;
open Candle_cv_flyspeck_nonlinear_term_order_compat;;

let candle_disjunctive_fourth_fsn_axioms_before = axioms ();;

let candle_disjunctive_fourth_fsn_component_pass component list_theorem =
  let function_term =
    List.nth candle_disjunctive_case16364_functions
      component.next_batch_component_selected in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain
      (concl component.next_batch_component_domain) in
  let functions,actual_domain =
    M_verifier.dest_m_cell_list_pass (concl list_theorem) in
  if functions <> [function_term] ||
     not (aconv actual_domain expected_domain) ||
     hyp list_theorem <> [] then
    failwith
      "fixed nonlinear fourth sibling complete: component handoff drift";
  list_theorem;;

let candle_disjunctive_fourth_fsn_pair_components components sources =
  let rec pair components sources =
    match components,sources with
    | [],[] -> []
    | component::remaining_components,source::remaining_sources ->
        (component.next_batch_component_id,
         candle_disjunctive_fourth_fsn_component_pass component source) ::
        pair remaining_components remaining_sources
    | _ -> failwith
        "fixed nonlinear fourth sibling complete: forest cardinality drift" in
  pair components sources;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-fixed-nonlinear-component-handoff-begin";;
let candle_disjunctive_fourth_fsn_component_passes =
  candle_disjunctive_fourth_fsn_pair_components
    (rev candle_disjunctive_fourth_batch_components0)
    candle_disjunctive_fourth_bounded_sources0 @
  candle_disjunctive_fourth_fsn_pair_components
    (rev candle_disjunctive_fourth_batch_components1)
    candle_disjunctive_fourth_bounded_sources1;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-fixed-nonlinear-component-handoff-end";;

let candle_disjunctive_fourth_fsn_component_table =
  let count = length candle_disjunctive_fourth_batch_components in
  let table = Array.make count TRUTH and seen = Array.make count false in
  let rec fill = function
    | [] -> ()
    | (component,theorem)::remaining ->
        if component < 0 || component >= count || seen.(component) then
          failwith
            "fixed nonlinear fourth sibling complete: component table drift";
        table.(component) <- theorem;
        seen.(component) <- true;
        fill remaining in
  let rec all_seen index =
    index = count || (seen.(index) && all_seen (index + 1)) in
  fill candle_disjunctive_fourth_fsn_component_passes;
  if not (all_seen 0) then
    failwith "fixed nonlinear fourth sibling complete: component missing";
  table;;

let rec candle_disjunctive_fourth_fsn_glue = function
  | Candle_disjunctive_next_batch_component component ->
      candle_disjunctive_fourth_fsn_component_table.(component)
  | Candle_disjunctive_next_batch_mixed (axis,left,right) ->
      let left_theorem = candle_disjunctive_fourth_fsn_glue left in
      let right_theorem = candle_disjunctive_fourth_fsn_glue right in
      let appended =
        M_verifier.m_glue_cells_list 6 axis left_theorem right_theorem in
      candle_nonlinear_merge_m_cell_list_pass 6 appended;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-fixed-nonlinear-mixed-reconstruction-begin";;
let candle_disjunctive_case16364_fixed_nonlinear_root_list_pass =
  candle_disjunctive_fourth_fsn_glue candle_disjunctive_case16364_skeleton;;
let candle_disjunctive_case16625_fixed_nonlinear_root_list_pass =
  candle_disjunctive_fourth_fsn_glue candle_disjunctive_case16625_skeleton;;
let candle_disjunctive_case16587_fixed_nonlinear_root_list_pass =
  candle_disjunctive_fourth_fsn_glue candle_disjunctive_case16587_skeleton;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-fixed-nonlinear-mixed-reconstruction-end";;

let candle_disjunctive_fourth_fsn_finalize
    functions variable_vector standard domain_subset converted expansion
    reconstruction target root_list_pass =
  let expanded_general =
    M_verifier_main.normalize_disj_result true
      functions variable_vector standard domain_subset root_list_pass in
  let expanded =
    let theorem = SPEC_ALL expanded_general in
    let bridge = TAUT (mk_imp (concl theorem,converted)) in
    MP bridge theorem in
  let case_theorem = REWRITE_RULE[GSYM expansion] expanded in
  let theorem =
    (SPEC_ALL o REWRITE_RULE[GSYM reconstruction]) case_theorem in
  if hyp theorem <> [] || not (aconv (concl theorem) target) then
    failwith "fixed nonlinear fourth sibling complete: exact theorem mismatch";
  theorem;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-fixed-nonlinear-exact-finalize-begin";;
let candle_disjunctive_case16364_fixed_nonlinear_theorem =
  candle_disjunctive_fourth_fsn_finalize
    candle_disjunctive_case16364_functions
    candle_disjunctive_case16364_variable_vector
    candle_disjunctive_case16364_standard
    candle_disjunctive_case16364_domain_subset
    candle_disjunctive_case16364_converted
    candle_disjunctive_case16364_expansion
    candle_disjunctive_case16364_reconstruction
    candle_disjunctive_case16364_target
    candle_disjunctive_case16364_fixed_nonlinear_root_list_pass;;
let candle_disjunctive_case16625_fixed_nonlinear_theorem =
  candle_disjunctive_fourth_fsn_finalize
    candle_disjunctive_case16625_functions
    candle_disjunctive_case16625_variable_vector
    candle_disjunctive_case16625_standard
    candle_disjunctive_case16625_domain_subset
    candle_disjunctive_case16625_converted
    candle_disjunctive_case16625_expansion
    candle_disjunctive_case16625_reconstruction
    candle_disjunctive_case16625_target
    candle_disjunctive_case16625_fixed_nonlinear_root_list_pass;;
let candle_disjunctive_case16587_fixed_nonlinear_theorem =
  candle_disjunctive_fourth_fsn_finalize
    candle_disjunctive_case16587_functions
    candle_disjunctive_case16587_variable_vector
    candle_disjunctive_case16587_standard
    candle_disjunctive_case16587_domain_subset
    candle_disjunctive_case16587_converted
    candle_disjunctive_case16587_expansion
    candle_disjunctive_case16587_reconstruction
    candle_disjunctive_case16587_target
    candle_disjunctive_case16587_fixed_nonlinear_root_list_pass;;
let candle_disjunctive_case16364_theorem =
  candle_disjunctive_case16364_fixed_nonlinear_theorem;;
let candle_disjunctive_case16625_theorem =
  candle_disjunctive_case16625_fixed_nonlinear_theorem;;
let candle_disjunctive_case16587_theorem =
  candle_disjunctive_case16587_fixed_nonlinear_theorem;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-fixed-nonlinear-exact-finalize-end";;

let candle_disjunctive_case16364_fixed_nonlinear_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_disjunctive_case16364_fixed_nonlinear_theorem));;
let candle_disjunctive_case16625_fixed_nonlinear_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_disjunctive_case16625_fixed_nonlinear_theorem));;
let candle_disjunctive_case16587_fixed_nonlinear_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_disjunctive_case16587_fixed_nonlinear_theorem));;
let candle_disjunctive_fourth_fsn_axioms_after = axioms ();;

if length candle_disjunctive_fourth_fsn_component_passes <>
     length candle_disjunctive_fourth_batch_components ||
   length candle_disjunctive_fourth_fsn_axioms_after <>
     length candle_disjunctive_fourth_fsn_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_disjunctive_fourth_fsn_axioms_before)
       candle_disjunctive_fourth_fsn_axioms_after) then
  failwith "fixed nonlinear fourth sibling complete: final validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_SHARED_COMPLETE_OK" ^
   " DEVELOPMENT_NON_RELEASE parent=prep-8293089898" ^
   " reflected_siblings=3 source_leaves=13978 numerical_cells=" ^
   string_of_int candle_disjunctive_fourth_batch_total_cells ^
   " complete_verdicts=2 components=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components) ^
   " assumptions=0 axiom_growth=0" ^
   " record16364_digest=" ^ candle_disjunctive_case16364_fixed_nonlinear_digest ^
   " record16625_digest=" ^ candle_disjunctive_case16625_fixed_nonlinear_digest ^
   " record16587_digest=" ^ candle_disjunctive_case16587_fixed_nonlinear_digest);;

end;;
