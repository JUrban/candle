(* ========================================================================== *)
(* Conditional handoff for the genuine case-16594 cell-0 object verdict.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This discharges all mathematical premises and *)
(* leaves the exact evaluator verdict as an explicit implication premise.     *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_cell0_call.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_cell0_conditional_handoff = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry_success_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_entry_fixture;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_plan;;
open Test_cv_compute_analytic_expr_case16594_packed_object_cell0_call;;

let candle_case16594_object_cell0_outer_correspondence_goal =
  list_mk_comb
    (`candle_q_packed_source_correspondence`,
     [candle_case16594_cell0_outer_boxes;
      candle_case16594_cell0_center_boxes;
      candle_case16594_cell0_outer_boxes;
      candle_case16594_cell0_radii]);;

let candle_case16594_object_cell0_outer_correspondence = prove
  (candle_case16594_object_cell0_outer_correspondence_goal,
   REWRITE_TAC
     [candle_q_packed_source_correspondence_def;
      candle_q_packed_center_contains_source_midpoint_def;
      candle_q_packed_radii_cover_source_def;
      candle_q_packed_outer_covers_source_def;
      candle_case16594_cell0_forall_lt_six;
      candle_case16594_cell0_forall_lt_length_six;
      candle_q_box_valid_list_def; candle_q_radius_list_def;
      candle_q_interval_contains_def; candle_q_le_real;
      LENGTH; ALL] THEN
   CONV_TAC (DEPTH_CONV EL_CONV) THEN
   REWRITE_TAC
     [candle_q_midpoint_real; candle_q_radius_real;
      candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
      FST; SND] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN
   TRY (REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV));;

let candle_case16594_object_cell0_source_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:((((num#num)#num)#((num#num)#num))list)->num`,
       candle_case16594_cell0_source_boxes));;

let candle_case16594_object_cell0_center_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:((((num#num)#num)#((num#num)#num))list)->num`,
       candle_case16594_cell0_center_boxes));;

let candle_case16594_object_cell0_outer_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:((((num#num)#num)#((num#num)#num))list)->num`,
       candle_case16594_cell0_outer_boxes));;

let candle_case16594_object_cell0_radii_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:(((num#num)#num)list)->num`,
       candle_case16594_cell0_radii));;

let candle_case16594_object_cell0_acceptance_hypothesis =
  mk_eq (candle_case16594_object_cell0_call,`Cexp_num 1`);;

let candle_case16594_object_cell0_raw_acceptance =
  ASSUME candle_case16594_object_cell0_acceptance_hypothesis;;

let candle_case16594_object_cell0_acceptance =
  TRANS candle_case16594_object_cell0_representation
    candle_case16594_object_cell0_raw_acceptance;;

let candle_case16594_object_cell0_cell_pass =
  MATCH_MP
    (SPECL
      [candle_case16594_cell0_source_boxes;
       candle_case16594_cell0_center_boxes;
       candle_case16594_cell0_outer_boxes;
       candle_case16594_cell0_radii;
       candle_case16594_cell0_plan_codes;
       candle_case16594_cell0_sources;
       candle_case16594_cell0_certificates]
      candle_cv_q_packed_object_dispatch_entry_accept_cell_pass)
    (end_itlist CONJ
      [candle_case16594_object_cell0_source_length;
       candle_case16594_object_cell0_center_length;
       candle_case16594_object_cell0_outer_length;
       candle_case16594_object_cell0_radii_length;
       candle_case16594_cell0_correspondence;
       candle_case16594_object_cell0_outer_correspondence;
       candle_case16594_cell0_plan;
       candle_case16594_object_cell0_acceptance]);;

let candle_case16594_object_cell0_conditional_cell_pass =
  DISCH candle_case16594_object_cell0_acceptance_hypothesis
    candle_case16594_object_cell0_cell_pass;;

let _ =
  if hyp candle_case16594_object_cell0_outer_correspondence <> [] ||
     hyp candle_case16594_object_cell0_raw_acceptance <>
       [candle_case16594_object_cell0_acceptance_hypothesis] ||
     hyp candle_case16594_object_cell0_acceptance <>
       [candle_case16594_object_cell0_acceptance_hypothesis] ||
     hyp candle_case16594_object_cell0_cell_pass <>
       [candle_case16594_object_cell0_acceptance_hypothesis] ||
     hyp candle_case16594_object_cell0_conditional_cell_pass <> [] then
    failwith "case16594 object cell0 conditional handoff: assumption drift";;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_CELL0_CONDITIONAL_HANDOFF_OK cells=1 cell_pass=1 evaluator_premises=1 theorem_assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
