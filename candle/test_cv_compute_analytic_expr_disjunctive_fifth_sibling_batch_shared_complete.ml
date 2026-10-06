(* Bounded reflected proof of the fifth three authentic production siblings. *)
(* Numerical and topology checking is checkpointed by whole components.       *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_bounded_forests.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_term_order_compat.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_shared_complete = struct

open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_shared_sibling_prepare;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_bounded_forests;;
open Candle_cv_flyspeck_nonlinear_term_order_compat;;

let candle_disjunctive_fifth_batch_axioms_before = axioms ();;

let candle_disjunctive_fifth_batch_component_pass component source =
  let function_term =
    List.nth candle_disjunctive_case16646_functions
      component.next_batch_component_selected in
  let expected_lower,expected_upper =
    candle_disjunctive_fixed_outer_domain_bounds
      component.next_batch_component_domain in
  candle_reflected_nl_source_pass_with function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_shared_aconv_lists
             actual_lower expected_lower &&
           candle_disjunctive_shared_aconv_lists
             actual_upper expected_upper)
      then failwith "fifth sibling batch complete: component handoff drift";
      source)
    component.next_batch_component_domain;;

let candle_disjunctive_fifth_batch_pair_components components sources =
  let rec pair components sources =
    match components,sources with
    | [],[] -> []
    | component::remaining_components,source::remaining_sources ->
        (component.next_batch_component_id,
         candle_disjunctive_fifth_batch_component_pass component source) ::
        pair remaining_components remaining_sources
    | _ -> failwith "fifth sibling batch complete: forest cardinality drift" in
  pair components sources;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-component-handoff-begin";;
let candle_disjunctive_fifth_batch_component_passes =
  candle_disjunctive_fifth_batch_pair_components
    (rev candle_disjunctive_fifth_batch_components0)
    candle_disjunctive_fifth_bounded_sources0 @
  candle_disjunctive_fifth_batch_pair_components
    (rev candle_disjunctive_fifth_batch_components1)
    candle_disjunctive_fifth_bounded_sources1;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-component-handoff-end";;

let candle_disjunctive_fifth_batch_component_table =
  let count = length candle_disjunctive_fifth_batch_components in
  let table = Array.make count TRUTH and seen = Array.make count false in
  let rec fill = function
    | [] -> ()
    | (component,theorem)::remaining ->
        if component < 0 || component >= count || seen.(component) then
          failwith "fifth sibling batch complete: component table drift";
        table.(component) <- theorem;
        seen.(component) <- true;
        fill remaining in
  let rec all_seen index =
    index = count || (seen.(index) && all_seen (index + 1)) in
  fill candle_disjunctive_fifth_batch_component_passes;
  if not (all_seen 0) then
    failwith "fifth sibling batch complete: component missing";
  table;;

let rec candle_disjunctive_fifth_batch_glue = function
  | Candle_disjunctive_next_batch_component component ->
      candle_disjunctive_fifth_batch_component_table.(component)
  | Candle_disjunctive_next_batch_mixed (axis,left,right) ->
      let left_theorem = candle_disjunctive_fifth_batch_glue left in
      let right_theorem = candle_disjunctive_fifth_batch_glue right in
      let appended =
        M_verifier.m_glue_cells_list 6 axis left_theorem right_theorem in
      candle_nonlinear_merge_m_cell_list_pass 6 appended;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-mixed-reconstruction-begin";;
let candle_disjunctive_case16646_root_list_pass =
  candle_disjunctive_fifth_batch_glue
    candle_disjunctive_case16646_skeleton;;
let candle_disjunctive_case16659_root_list_pass =
  candle_disjunctive_fifth_batch_glue
    candle_disjunctive_case16659_skeleton;;
let candle_disjunctive_case16658_root_list_pass =
  candle_disjunctive_fifth_batch_glue
    candle_disjunctive_case16658_skeleton;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-mixed-reconstruction-end";;

let candle_disjunctive_fifth_batch_finalize
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
    failwith "fifth sibling batch complete: exact theorem mismatch";
  theorem;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-exact-finalize-begin";;
let candle_disjunctive_case16646_theorem =
  candle_disjunctive_fifth_batch_finalize
    candle_disjunctive_case16646_functions
    candle_disjunctive_case16646_variable_vector
    candle_disjunctive_case16646_standard
    candle_disjunctive_case16646_domain_subset
    candle_disjunctive_case16646_converted
    candle_disjunctive_case16646_expansion
    candle_disjunctive_case16646_reconstruction
    candle_disjunctive_case16646_target
    candle_disjunctive_case16646_root_list_pass;;
let candle_disjunctive_case16659_theorem =
  candle_disjunctive_fifth_batch_finalize
    candle_disjunctive_case16659_functions
    candle_disjunctive_case16659_variable_vector
    candle_disjunctive_case16659_standard
    candle_disjunctive_case16659_domain_subset
    candle_disjunctive_case16659_converted
    candle_disjunctive_case16659_expansion
    candle_disjunctive_case16659_reconstruction
    candle_disjunctive_case16659_target
    candle_disjunctive_case16659_root_list_pass;;
let candle_disjunctive_case16658_theorem =
  candle_disjunctive_fifth_batch_finalize
    candle_disjunctive_case16658_functions
    candle_disjunctive_case16658_variable_vector
    candle_disjunctive_case16658_standard
    candle_disjunctive_case16658_domain_subset
    candle_disjunctive_case16658_converted
    candle_disjunctive_case16658_expansion
    candle_disjunctive_case16658_reconstruction
    candle_disjunctive_case16658_target
    candle_disjunctive_case16658_root_list_pass;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-exact-finalize-end";;

let candle_disjunctive_case16646_digest =
  Digest.to_hex (Digest.string (string_of_thm candle_disjunctive_case16646_theorem));;
let candle_disjunctive_case16659_digest =
  Digest.to_hex (Digest.string (string_of_thm candle_disjunctive_case16659_theorem));;
let candle_disjunctive_case16658_digest =
  Digest.to_hex (Digest.string (string_of_thm candle_disjunctive_case16658_theorem));;
let candle_disjunctive_fifth_batch_axioms_after = axioms ();;

if length candle_disjunctive_fifth_batch_component_passes <>
     length candle_disjunctive_fifth_batch_components ||
   length candle_disjunctive_fifth_batch_axioms_after <>
     length candle_disjunctive_fifth_batch_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_disjunctive_fifth_batch_axioms_before)
       candle_disjunctive_fifth_batch_axioms_after) then
  failwith "fifth sibling batch complete: final validation failed";;

print_endline
  ("CANDLE_CV_FIFTH_SIBLING_BATCH_SHARED_COMPLETE_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898 reflected_siblings=3 source_leaves=5739" ^
   " numerical_cells=" ^
   string_of_int candle_disjunctive_fifth_batch_total_cells ^
   " complete_verdicts=2 components=" ^
   string_of_int (length candle_disjunctive_fifth_batch_components) ^
   " assumptions=0 axiom_growth=0" ^
   " record16646_digest=" ^ candle_disjunctive_case16646_digest ^
   " record16659_digest=" ^ candle_disjunctive_case16659_digest ^
   " record16658_digest=" ^ candle_disjunctive_case16658_digest);;

end;;
