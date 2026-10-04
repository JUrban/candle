(* Test all six one-step split axes for rejected case-16597 source leaves. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16597_plan_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16597_split_scan = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16597_leaf_grouping;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Test_cv_compute_analytic_expr_disjunctive_case16597_plan_scan;;

let rec candle_disjunctive_case16597_split_scan_axes leaf axis domain =
  if axis > 6 then []
  else
    let left,right = M_verifier.split_domain 6 6 axis domain in
    (leaf,axis,left)::(leaf,axis,right)::
      candle_disjunctive_case16597_split_scan_axes leaf (axis + 1) domain;;

let candle_disjunctive_case16597_split_scan_candidates =
  List.flatten
    (map
      (fun leaf ->
        candle_disjunctive_case16597_split_scan_axes leaf 1
          (List.nth candle_disjunctive_case16597_leaves leaf))
      candle_disjunctive_case16597_scan_failures);;

let candle_disjunctive_case16597_split_scan_cells =
  map
    (fun (_,_,domain) -> candle_disjunctive_case16597_scan_cell domain)
    candle_disjunctive_case16597_split_scan_candidates;;
let candle_disjunctive_case16597_split_scan_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_case16597_split_scan_cells;;
let candle_disjunctive_case16597_split_scan_call =
  list_mk_comb
    (`candle_cv_fso_variable_jobs_scan`,
     [candle_disjunctive_case16597_scan_prepared.program_representation_term;
      candle_disjunctive_case16597_split_scan_encoded_jobs]);;

let candle_disjunctive_case16597_split_scan_axioms_before = axioms ();;
let _ =
  candle_q_dim_analytic_jet_profile_event "case16597-split-scan-begin";;
let candle_disjunctive_case16597_split_scan_theorem =
  candle_q_dim_analytic_jet_compute
    candle_cv_fso_variable_jobs_scan_compute_eqs
    candle_disjunctive_case16597_split_scan_call;;
let _ =
  candle_q_dim_analytic_jet_profile_event "case16597-split-scan-end";;

let candle_disjunctive_case16597_split_scan_count,
    candle_disjunctive_case16597_split_scan_failures =
  candle_cv_fso_variable_jobs_scan_decode "case16597 split scan"
    (rand (concl candle_disjunctive_case16597_split_scan_theorem));;

let rec candle_disjunctive_case16597_split_scan_choose_axis base axis =
  if axis > 6 then None
  else
    let left = base + 2 * (axis - 1) in
    if not
         (List.mem left
           candle_disjunctive_case16597_split_scan_failures) &&
       not
         (List.mem (left + 1)
           candle_disjunctive_case16597_split_scan_failures)
    then Some axis
    else candle_disjunctive_case16597_split_scan_choose_axis base (axis + 1);;

let rec candle_disjunctive_case16597_split_scan_select base = function
  | [] -> [],[]
  | leaf::remaining ->
      let selected,unsolved =
        candle_disjunctive_case16597_split_scan_select
          (base + 12) remaining in
      (match candle_disjunctive_case16597_split_scan_choose_axis base 1 with
       | Some axis -> (leaf,axis)::selected,unsolved
       | None -> selected,leaf::unsolved);;

let candle_disjunctive_case16597_split_scan_selected,
    candle_disjunctive_case16597_split_scan_unsolved =
  candle_disjunctive_case16597_split_scan_select 0
    candle_disjunctive_case16597_scan_failures;;

let rec candle_disjunctive_case16597_split_scan_selection_string = function
  | [] -> ""
  | [(leaf,axis)] -> string_of_int leaf ^ ":" ^ string_of_int axis
  | (leaf,axis)::remaining ->
      string_of_int leaf ^ ":" ^ string_of_int axis ^ "," ^
      candle_disjunctive_case16597_split_scan_selection_string remaining;;

let candle_disjunctive_case16597_split_scan_axioms_after = axioms ();;
let candle_disjunctive_case16597_split_scan_expected_jobs =
  12 * length candle_disjunctive_case16597_scan_failures;;

if length candle_disjunctive_case16597_split_scan_candidates <>
     candle_disjunctive_case16597_split_scan_expected_jobs ||
   candle_disjunctive_case16597_split_scan_count <>
     candle_disjunctive_case16597_split_scan_expected_jobs ||
   hyp candle_disjunctive_case16597_split_scan_theorem <> [] ||
   not
     (aconv (lhand (concl candle_disjunctive_case16597_split_scan_theorem))
       candle_disjunctive_case16597_split_scan_call) ||
   length candle_disjunctive_case16597_split_scan_axioms_after <>
     length candle_disjunctive_case16597_split_scan_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_case16597_split_scan_axioms_before)
       candle_disjunctive_case16597_split_scan_axioms_after) then
  failwith "case16597 split scan: validation failed";;

print_endline
  ("CANDLE_CV_CASE16597_SPLIT_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " rejected_source_leaves=" ^
   string_of_int (length candle_disjunctive_case16597_scan_failures) ^
   " candidate_children=" ^
   string_of_int candle_disjunctive_case16597_split_scan_expected_jobs ^
   " rejected_children=" ^
   string_of_int
     (length candle_disjunctive_case16597_split_scan_failures) ^
   " selected_splits=" ^
   candle_disjunctive_case16597_split_scan_selection_string
     candle_disjunctive_case16597_split_scan_selected ^
   " unsolved=" ^
   candle_cv_fso_variable_jobs_scan_indices_string
     candle_disjunctive_case16597_split_scan_unsolved ^
   " assumptions=0 axiom_growth=0");;

end;;
