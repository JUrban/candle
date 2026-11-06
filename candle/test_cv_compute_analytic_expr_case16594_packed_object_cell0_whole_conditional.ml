(* ========================================================================== *)
(* Genuine case-16594 cell 0 through the packed-object whole-call boundary.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is a bounded representation seam test.   *)
(* It assumes only the already isolated exact entry verdict and proves that  *)
(* the one-leaf whole call returns the same source box and yields the root    *)
(* [m_cell_pass] theorem through the generic whole-call soundness result.     *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_cell0_call.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_whole_success_sound.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_cell0_whole_conditional = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry_success_sound;;
open Candle_cv_analytic_expr_packed_source_object_whole_compute;;
open Candle_cv_analytic_expr_packed_source_object_whole_success_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_entry_fixture;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_plan;;
open Test_cv_compute_analytic_expr_case16594_packed_object_cell0_call;;

(* The interval packet encodes an outward-rounded outer box: each endpoint is
   one fixed-scale unit wider than the pre-rounded endpoint used by the
   packer.  Add that same unit to the ceil-halfwidth so the explicit geometry
   contract covers the encoded box, not merely the packer's precursor. *)
let candle_case16594_object_cell0_whole_radii =
  mk_list
    (map candle_case16594_cell0_scaled_q
       ["161518258123"; "161518258123"; "161518258123";
        "323036516243"; "211308954992"; "323036516243"],
     `:((num#num)#num)`);;

let candle_case16594_object_cell0_whole_source_correspondence_goal =
  list_mk_comb
    (`candle_q_packed_source_correspondence`,
     [candle_case16594_cell0_source_boxes;
      candle_case16594_cell0_center_boxes;
      candle_case16594_cell0_outer_boxes;
      candle_case16594_object_cell0_whole_radii]);;

let candle_case16594_object_cell0_whole_source_correspondence = prove
  (candle_case16594_object_cell0_whole_source_correspondence_goal,
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

let candle_case16594_object_cell0_whole_outer_correspondence_goal =
  list_mk_comb
    (`candle_q_packed_source_correspondence`,
     [candle_case16594_cell0_outer_boxes;
      candle_case16594_cell0_center_boxes;
      candle_case16594_cell0_outer_boxes;
      candle_case16594_object_cell0_whole_radii]);;

let candle_case16594_object_cell0_whole_outer_correspondence = prove
  (candle_case16594_object_cell0_whole_outer_correspondence_goal,
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

let _ = print_endline "CANDLE_CASE16594_CELL0_WHOLE_STAGE outer_correspondence";;

let candle_case16594_object_cell0_whole_source_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:((((num#num)#num)#((num#num)#num))list)->num`,
       candle_case16594_cell0_source_boxes));;

let candle_case16594_object_cell0_whole_center_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:((((num#num)#num)#((num#num)#num))list)->num`,
       candle_case16594_cell0_center_boxes));;

let candle_case16594_object_cell0_whole_outer_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:((((num#num)#num)#((num#num)#num))list)->num`,
       candle_case16594_cell0_outer_boxes));;

let candle_case16594_object_cell0_whole_radii_length =
  LENGTH_CONV
    (mk_comb
      (`LENGTH:(((num#num)#num)list)->num`,
       candle_case16594_object_cell0_whole_radii));;

let candle_case16594_object_cell0_packed_cells =
  mk_list
    ([mk_pair
       (candle_case16594_object_cell0_whole_radii,
        candle_case16594_cell0_certificates)],
     `:(((num#num)#num)list #
        ((((num#num)#num)#((num#num)#num))list))`);;

let candle_case16594_object_cell0_jobs =
  mk_list
    ([mk_pair
       (candle_case16594_cell0_outer_boxes,
        mk_pair
          (candle_case16594_cell0_center_boxes,
           candle_case16594_cell0_source_boxes))],
     `:((((num#num)#num)#((num#num)#num))list #
       (((((num#num)#num)#((num#num)#num))list) #
        ((((num#num)#num)#((num#num)#num))list)))`);;

let candle_case16594_object_cell0_tokens =
  `[Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf]`;;

let candle_case16594_object_cell0_whole_call =
  list_mk_comb
    (`candle_cv_q_packed_object_whole_check`,
     [list_mk_comb
        (`Cexp_pair`,
         [mk_comb
            (`candle_cv_q_packed_object_plan_code_list`,
             candle_case16594_cell0_plan_codes);
          list_mk_comb
            (`Cexp_pair`,
             [mk_comb
                (`candle_cv_analytic_instruction_list`,
                 candle_case16594_cell0_sources);
              mk_comb
                (`candle_cv_q_packed_object_cells`,
                 candle_case16594_object_cell0_packed_cells)])]);
      `Cexp_num (dimindex (:6))`;
      mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens`,
         candle_case16594_object_cell0_tokens);
      mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         candle_case16594_object_cell0_jobs)]);;

let candle_case16594_object_cell0_whole_logical_call =
  list_mk_comb
    (`candle_cv_q_packed_object_dispatch_entry`,
     [mk_comb
        (`candle_cv_q_interval_list`,
         candle_case16594_cell0_center_boxes);
      mk_comb
        (`candle_cv_q_interval_list`,
         candle_case16594_cell0_outer_boxes);
      mk_comb
        (`candle_cv_q_list`,
         candle_case16594_object_cell0_whole_radii);
      mk_comb
        (`candle_cv_q_packed_object_plan_code_list`,
         candle_case16594_cell0_plan_codes);
      mk_comb
        (`candle_cv_analytic_instruction_list`,
         candle_case16594_cell0_sources);
      mk_comb
        (`candle_cv_q_interval_list`,
         candle_case16594_cell0_certificates)]);;

let candle_case16594_object_cell0_encoded_root =
  mk_comb
    (`candle_cv_q_interval_list`,candle_case16594_cell0_source_boxes);;

let candle_case16594_object_cell0_whole_result =
  list_mk_comb
    (`Cexp_pair`,
     [`Cexp_num 1`;
      list_mk_comb
        (`Cexp_pair`,
         [`Cexp_num 1`;
          list_mk_comb
            (`Cexp_pair`,
             [`Cexp_num 0`;
              list_mk_comb
                (`Cexp_pair`,
                 [candle_case16594_object_cell0_encoded_root;
                  `Cexp_num 0`])])])]);;

let candle_cv_q_packed_object_whole_singleton_from_entry = prove
 (`!plan_codes source_instructions packed_cell outer_boxes center_boxes
      source_boxes.
     candle_cv_q_packed_object_whole_job_check plan_codes
       source_instructions packed_cell
       (Cexp_pair outer_boxes (Cexp_pair center_boxes source_boxes)) =
       Cexp_num 1 /\
     candle_cv_list_length source_boxes = Cexp_num 6
     ==>
     candle_cv_q_packed_object_whole_check
       (Cexp_pair plan_codes
         (Cexp_pair source_instructions
           (Cexp_pair packed_cell (Cexp_num 0))))
       (Cexp_num 6)
       (Cexp_pair (Cexp_num 0) (Cexp_num 0))
       (Cexp_pair
         (Cexp_pair outer_boxes (Cexp_pair center_boxes source_boxes))
         (Cexp_num 0)) =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair source_boxes (Cexp_num 0))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    ((CONJUNCTS
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def) @
    [candle_cv_q_packed_object_whole_check_def;
     candle_cv_q_packed_object_whole_jobs_check_def;
     candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
     candle_cv_bool_and_def; candle_cv_bool_def;
     cexp_eq_def; cexp_if_def; cexp_ispair_def;
     cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF]) THEN
  ASM_REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_case16594_object_cell0_whole_from_entry = prove
 (mk_imp
   (mk_eq (candle_case16594_object_cell0_whole_logical_call,`Cexp_num 1`),
    mk_eq
      (candle_case16594_object_cell0_whole_call,
       candle_case16594_object_cell0_whole_result)),
  DISCH_THEN (LABEL_TAC "entry_accept") THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_cells_def;
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
     candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
     candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
     DIMINDEX_CONV `dimindex (:6)`] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_whole_singleton_from_entry THEN
  CONJ_TAC THENL
   [REWRITE_TAC
      [candle_cv_q_packed_object_whole_job_check_def;
       cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF] THEN
    USE_THEN "entry_accept" ACCEPT_TAC;
    REWRITE_TAC
      [candle_cv_interval_list_length_correct;
       candle_case16594_object_cell0_whole_source_length]]);;

let _ = print_endline "CANDLE_CASE16594_CELL0_WHOLE_STAGE whole_from_entry";;

let candle_case16594_object_cell0_input_contract = prove
 (list_mk_icomb
    "candle_q_packed_object_whole_input_contract"
    [candle_case16594_object_cell0_packed_cells;
     candle_case16594_object_cell0_jobs],
  REWRITE_TAC
    [candle_q_packed_object_whole_input_contract_def; LENGTH; FST; SND;
     candle_case16594_object_cell0_whole_source_length;
     candle_case16594_object_cell0_whole_center_length;
     candle_case16594_object_cell0_whole_outer_length;
     candle_case16594_object_cell0_whole_radii_length;
     candle_case16594_object_cell0_whole_source_correspondence;
     candle_case16594_object_cell0_whole_outer_correspondence]);;

let _ = print_endline "CANDLE_CASE16594_CELL0_WHOLE_STAGE input_contract";;

let candle_case16594_object_cell0_whole_conditional_goal =
  let reference_item =
    mk_var ("reference_item",`:candle_q_packed_object_item`) in
  let reference_run =
    list_mk_comb
      (`candle_q_packed_object_source_planned_program_run`,
       [candle_case16594_cell0_center_boxes;
        candle_case16594_cell0_outer_boxes;
        candle_case16594_object_cell0_whole_radii;
        candle_case16594_cell0_plan_codes;
        candle_case16594_cell0_sources;
        candle_case16594_cell0_certificates;
        mk_list ([],`:candle_q_packed_object_item`);
        mk_list ([reference_item],`:candle_q_packed_object_item`);
        mk_list ([],candle_q_interval_type)]) in
  let reference_box_expr =
    mk_comb
      (`candle_q_packed_object_item_box_expr`,reference_item) in
  let erased_reference_box_expr =
    mk_comb
      (`candle_analytic_erase_sqrt_certificates`,reference_box_expr) in
  let reference_function =
    mk_comb
      (`candle_analytic_denote_dim:candle_analytic_expr->real^6->real`,
       erased_reference_box_expr) in
  let source_domain =
    mk_pair
      (mk_comb
        (`candle_q_box_lower_vector:
            ((((num#num)#num)#((num#num)#num))list)->real^6`,
         candle_case16594_cell0_source_boxes),
       mk_comb
        (`candle_q_box_upper_vector:
            ((((num#num)#num)#((num#num)#num))list)->real^6`,
         candle_case16594_cell0_source_boxes)) in
  let root_pass =
    list_mk_comb
      (`m_cell_pass:(real^6->real)->(real^6#real^6)->bool`,
       [reference_function;source_domain]) in
  mk_imp
    (mk_eq
      (candle_case16594_object_cell0_whole_logical_call,`Cexp_num 1`),
     mk_exists (reference_item,mk_conj (reference_run,root_pass)));;

let candle_case16594_object_cell0_whole_conditional = prove
 (candle_case16594_object_cell0_whole_conditional_goal,
  DISCH_THEN (LABEL_TAC "entry_accept") THEN
  MP_TAC
    (MATCH_MP
      (SPECL
        [candle_case16594_cell0_source_boxes;
         candle_case16594_cell0_center_boxes;
         candle_case16594_cell0_outer_boxes;
         candle_case16594_object_cell0_whole_radii;
         candle_case16594_cell0_plan_codes;
         candle_case16594_cell0_sources;
         candle_case16594_cell0_certificates]
        candle_cv_q_packed_object_dispatch_entry_accept_cell_pass)
      (end_itlist CONJ
        [candle_case16594_object_cell0_whole_source_length;
         candle_case16594_object_cell0_whole_center_length;
         candle_case16594_object_cell0_whole_outer_length;
         candle_case16594_object_cell0_whole_radii_length;
         candle_case16594_object_cell0_whole_source_correspondence;
         candle_case16594_object_cell0_whole_outer_correspondence;
         candle_case16594_cell0_plan;
         ASSUME
           (mk_eq
             (candle_case16594_object_cell0_whole_logical_call,
              `Cexp_num 1`))])) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "reference_run")
        (LABEL_TAC "single_pass"))) THEN
  EXISTS_TAC
    `Candle_q_packed_object_item
      (Candle_q_packed_object_state domain center_value center_gradient
        value_bound gradient_bounds packed_hessian) center_e box_e` THEN
  CONJ_TAC THENL
   [USE_THEN "reference_run" ACCEPT_TAC;
    MATCH_MP_TAC
      (REWRITE_RULE
        [candle_cv_q_interval_list_roundtrip]
        (ISPECL
        [candle_case16594_object_cell0_packed_cells;
         candle_case16594_object_cell0_jobs;
         candle_case16594_cell0_plan_codes;
         candle_case16594_cell0_sources;
         candle_case16594_cell0_center_boxes;
         candle_case16594_cell0_outer_boxes;
         candle_case16594_object_cell0_whole_radii;
         candle_case16594_cell0_certificates;
         `Candle_q_packed_object_item
            (Candle_q_packed_object_state domain center_value center_gradient
              value_bound gradient_bounds packed_hessian) center_e box_e`;
         `[]:(((num#num)#num)#((num#num)#num))list`;
         `ARB:real^6`;
         candle_case16594_object_cell0_tokens;
         candle_case16594_object_cell0_encoded_root]
        candle_cv_q_packed_object_whole_success)) THEN
    REWRITE_TAC[candle_case16594_object_cell0_input_contract;
      candle_case16594_cell0_plan] THEN
    CONJ_TAC THENL
     [USE_THEN "reference_run" ACCEPT_TAC;
      MATCH_MP_TAC candle_case16594_object_cell0_whole_from_entry THEN
      USE_THEN "entry_accept" ACCEPT_TAC]]);;

if hyp candle_case16594_object_cell0_whole_from_entry <> [] ||
   hyp candle_case16594_object_cell0_input_contract <> [] ||
   hyp candle_case16594_object_cell0_whole_conditional <> [] then
  failwith "case16594 object cell0 whole conditional: assumptions";;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_CELL0_WHOLE_CONDITIONAL_OK cells=1 tokens=1 assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
