(* ========================================================================== *)
(* One-root split-tree proof of the first genuine action-296 nonlinear leaf. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Two exact child boxes are checked by one      *)
(* reflected batch computation.  A proved split tree turns that verdict into *)
(* one source theorem over the parent box, followed by one live-domain       *)
(* handoff.  No child source theorem or external cell glue is constructed.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_tree_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet_prove;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_prove;;

let candle_action296_tree_verdict_axioms_before = axioms ();;

let candle_action296_tree_verdict_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_tree_verdict_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 tree verdict: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 tree verdict: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_tree_verdict_find left_domain left
  | P_result_mono _ ->
      failwith "action296 tree verdict: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 tree verdict: unexpected reference node";;

let candle_action296_tree_verdict_parent_domain =
  candle_action296_tree_verdict_find
    candle_action296_tree_verdict_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_tree_verdict_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_tree_verdict_parent_lower,
    candle_action296_tree_verdict_parent_upper =
  candle_action296_tree_verdict_domain_bounds
    candle_action296_tree_verdict_parent_domain;;

let candle_action296_tree_verdict_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_tree_verdict_parent_lower
    candle_action296_tree_verdict_parent_upper;;

let candle_action296_tree_verdict_point_plan =
  candle_q_dim_taylor_model_point_plan_six
    candle_action296_tree_verdict_box_prepared;;

let candle_action296_tree_verdict_left_domain,
    candle_action296_tree_verdict_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_tree_verdict_parent_domain;;

let candle_action296_tree_verdict_cell domain_th =
  let lower,upper = candle_action296_tree_verdict_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      candle_action296_tree_verdict_box_prepared
      candle_action296_tree_verdict_point_plan lower upper in
  {
    batch_center_variant = center_variant;
    batch_lower = lower;
    batch_upper = upper;
  };;

let candle_action296_tree_verdict_left_cell =
  candle_action296_tree_verdict_cell
    candle_action296_tree_verdict_left_domain;;
let candle_action296_tree_verdict_right_cell =
  candle_action296_tree_verdict_cell
    candle_action296_tree_verdict_right_domain;;

let candle_action296_tree_verdict_profile_events : string list ref = ref [];;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      candle_action296_tree_verdict_profile_events :=
        event :: !candle_action296_tree_verdict_profile_events;
      print_endline
        ("CANDLE_CV_ACTION296_TREE_VERDICT_STAGE event=" ^ event));;

let candle_action296_tree_verdict_root_boxes =
  candle_poly_fixture_q_boxes
    candle_action296_tree_verdict_parent_lower
    candle_action296_tree_verdict_parent_upper;;
let candle_action296_tree_verdict_left_boxes =
  candle_poly_fixture_q_boxes
    candle_action296_tree_verdict_left_cell.batch_lower
    candle_action296_tree_verdict_left_cell.batch_upper;;
let candle_action296_tree_verdict_right_boxes =
  candle_poly_fixture_q_boxes
    candle_action296_tree_verdict_right_cell.batch_lower
    candle_action296_tree_verdict_right_cell.batch_upper;;

let candle_action296_tree_verdict_left_tree =
  candle_q_dim_taylor_model_tree_leaf_term
    candle_action296_tree_verdict_left_cell.batch_center_variant.
      variant_expression_term
    candle_action296_tree_verdict_left_boxes;;
let candle_action296_tree_verdict_right_tree =
  candle_q_dim_taylor_model_tree_leaf_term
    candle_action296_tree_verdict_right_cell.batch_center_variant.
      variant_expression_term
    candle_action296_tree_verdict_right_boxes;;
let candle_action296_tree_verdict_tree =
  candle_q_dim_taylor_model_tree_node_term `4`
    candle_action296_tree_verdict_root_boxes
    candle_action296_tree_verdict_left_tree
    candle_action296_tree_verdict_right_tree;;

let candle_action296_tree_verdict_vector_equality
    left_selector left_boxes left_components
    right_selector right_boxes right_components =
  let left =
    candle_reflected_nl_selector_vector_identity
      left_selector left_boxes left_components and
      right =
        candle_reflected_nl_selector_vector_identity
          right_selector right_boxes right_components in
  if not (aconv (rand (concl left)) (rand (concl right))) then
    failwith "action296 tree verdict: unequal endpoint component lists";
  TRANS left (SYM right);;

let candle_action296_tree_verdict_component_equality
    left_selector left_boxes right_selector right_boxes index =
  let component selector boxes =
    let theorem =
      match fst (dest_const selector) with
      | "candle_q_box_lower_vector" ->
          candle_q_box_lower_vector_component
      | "candle_q_box_upper_vector" ->
          candle_q_box_upper_vector_component
      | _ -> failwith "action296 tree verdict: unknown component selector" in
    let implication =
      SPECL [boxes;mk_small_numeral index]
        (INST_TYPE [`:6`,`:N`] theorem) in
    let premise,_ = dest_imp (concl implication) in
    let premise_theorem =
      prove
        (premise,
         REWRITE_TAC[IN_NUMSEG;candle_q_dim_poly_jet_dim_six] THEN
         ARITH_TAC) in
    let component = MATCH_MP implication premise_theorem in
    let q_function,projected = dest_comb (rand (concl component)) in
    let projection,selected = dest_comb projected in
    let select_with_index,boxes_term = dest_comb selected in
    let select_function,index_term = dest_comb select_with_index in
    let index_equality = NUM_REDUCE_CONV index_term in
    let selected_index_equality =
      MK_COMB
        (AP_TERM select_function index_equality,REFL boxes_term) in
    let selected_equality =
      TRANS selected_index_equality
        (EL_CONV (rand (concl selected_index_equality))) in
    let projected_equality0 = AP_TERM projection selected_equality in
    let projected_equality =
      TRANS projected_equality0
        (REWRITE_CONV[FST;SND] (rand (concl projected_equality0))) in
    TRANS component (AP_TERM q_function projected_equality) in
  let left = component left_selector left_boxes and
      right = component right_selector right_boxes in
  if not (aconv (rand (concl left)) (rand (concl right))) then
    failwith
      ("action296 tree verdict: unequal component values: " ^
       string_of_term (rand (concl left)) ^ " <> " ^
       string_of_term (rand (concl right)));
  TRANS left (SYM right);;

let candle_action296_tree_verdict_lower_selector =
  `candle_q_box_lower_vector:
     (((num#num)#num)#((num#num)#num))list->real^6`;;
let candle_action296_tree_verdict_upper_selector =
  `candle_q_box_upper_vector:
     (((num#num)#num)#((num#num)#num))list->real^6`;;

let candle_action296_tree_verdict_root_left_lower =
  candle_action296_tree_verdict_vector_equality
    candle_action296_tree_verdict_lower_selector
    candle_action296_tree_verdict_root_boxes
    candle_action296_tree_verdict_parent_lower
    candle_action296_tree_verdict_lower_selector
    candle_action296_tree_verdict_left_boxes
    candle_action296_tree_verdict_left_cell.batch_lower;;

let candle_action296_tree_verdict_root_right_upper =
  candle_action296_tree_verdict_vector_equality
    candle_action296_tree_verdict_upper_selector
    candle_action296_tree_verdict_root_boxes
    candle_action296_tree_verdict_parent_upper
    candle_action296_tree_verdict_upper_selector
    candle_action296_tree_verdict_right_boxes
    candle_action296_tree_verdict_right_cell.batch_upper;;

let candle_action296_tree_verdict_non_split_components =
  map
    (fun index ->
      let lower =
        candle_action296_tree_verdict_component_equality
          candle_action296_tree_verdict_lower_selector
          candle_action296_tree_verdict_right_boxes
          candle_action296_tree_verdict_lower_selector
          candle_action296_tree_verdict_root_boxes index and
          upper =
            candle_action296_tree_verdict_component_equality
              candle_action296_tree_verdict_upper_selector
              candle_action296_tree_verdict_left_boxes
              candle_action296_tree_verdict_upper_selector
              candle_action296_tree_verdict_root_boxes index in
      CONJ lower upper)
    [1;2;3;5;6];;

let candle_action296_tree_verdict_non_split_goal =
  let right_boxes =
    `right_boxes:(((num#num)#num)#((num#num)#num))list` and
      left_boxes =
        `left_boxes:(((num#num)#num)#((num#num)#num))list` and
      root_boxes =
        `root_boxes:(((num#num)#num)#((num#num)#num))list` in
  subst
    [candle_action296_tree_verdict_right_boxes,right_boxes;
     candle_action296_tree_verdict_left_boxes,left_boxes;
     candle_action296_tree_verdict_root_boxes,root_boxes]
    `!i. 1 <= i /\ i <= dimindex (:6) /\ ~(i = 4)
         ==> (candle_q_box_lower_vector right_boxes:real^6)$i =
               (candle_q_box_lower_vector root_boxes:real^6)$i /\
             (candle_q_box_upper_vector left_boxes:real^6)$i =
               (candle_q_box_upper_vector root_boxes:real^6)$i`;;

let candle_action296_tree_verdict_non_split = prove
 (candle_action296_tree_verdict_non_split_goal,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_dim_six] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `i = 1` THENL
   [ASM_REWRITE_TAC[el 0 candle_action296_tree_verdict_non_split_components];
    ASM_CASES_TAC `i = 2` THENL
     [ASM_REWRITE_TAC[el 1 candle_action296_tree_verdict_non_split_components];
      ASM_CASES_TAC `i = 3` THENL
       [ASM_REWRITE_TAC[el 2 candle_action296_tree_verdict_non_split_components];
        ASM_CASES_TAC `i = 5` THENL
         [ASM_REWRITE_TAC
            [el 3 candle_action296_tree_verdict_non_split_components];
          ASM_CASES_TAC `i = 6` THENL
           [ASM_REWRITE_TAC
              [el 4 candle_action296_tree_verdict_non_split_components];
            ASM_ARITH_TAC]]]]]);;

let candle_action296_tree_verdict_split_face =
  candle_action296_tree_verdict_component_equality
    candle_action296_tree_verdict_upper_selector
    candle_action296_tree_verdict_left_boxes
    candle_action296_tree_verdict_lower_selector
    candle_action296_tree_verdict_right_boxes 4;;

let candle_action296_tree_verdict_leaf_well_formed tree =
  let goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_tree_well_formed:
          real^6->candle_q_dim_taylor_model_tree->bool`,
       [`ARB:real^6`;tree]) in
  let expansion =
    REWRITE_CONV
      [candle_q_dim_taylor_model_tree_well_formed_def]
      goal in
  let length_call,dimension = dest_eq (rand (concl expansion)) in
  let length_evaluation =
    CONV_RULE (RAND_CONV NUM_REDUCE_CONV)
      (REWRITE_CONV[LENGTH] length_call) in
  if not
      (aconv dimension (lhand (concl candle_q_dim_poly_jet_dim_six)) &&
       aconv (rand (concl length_evaluation))
         (rand (concl candle_q_dim_poly_jet_dim_six))) then
    failwith
      ("action296 tree verdict: leaf dimension mismatch: " ^
       string_of_term dimension ^ " / length=" ^
       string_of_term (rand (concl length_evaluation)) ^
       " / expected-dimension=" ^
       string_of_term (lhand (concl candle_q_dim_poly_jet_dim_six)) ^
       " / expected-length=" ^
       string_of_term (rand (concl candle_q_dim_poly_jet_dim_six)));
  let length_theorem =
    TRANS length_evaluation (SYM candle_q_dim_poly_jet_dim_six) in
  EQ_MP (SYM expansion) length_theorem;;

let candle_action296_tree_verdict_left_well_formed =
  candle_action296_tree_verdict_leaf_well_formed
    candle_action296_tree_verdict_left_tree;;
let candle_action296_tree_verdict_right_well_formed =
  candle_action296_tree_verdict_leaf_well_formed
    candle_action296_tree_verdict_right_tree;;

let candle_action296_tree_verdict_length =
  let length_evaluation =
    CONV_RULE (RAND_CONV NUM_REDUCE_CONV)
      (REWRITE_CONV[LENGTH]
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
           candle_action296_tree_verdict_root_boxes))) in
  TRANS length_evaluation (SYM candle_q_dim_poly_jet_dim_six);;

let candle_action296_tree_verdict_split_lower =
  ARITH_RULE `1 <= 4`;;
let candle_action296_tree_verdict_split_upper = prove
 (`4 <= dimindex (:6)`,
  REWRITE_TAC[candle_q_dim_poly_jet_dim_six] THEN ARITH_TAC);;

let candle_action296_tree_verdict_well_formed =
  let goal =
    list_mk_comb
      (`candle_q_dim_taylor_model_tree_well_formed:
          real^6->candle_q_dim_taylor_model_tree->bool`,
       [`ARB:real^6`;candle_action296_tree_verdict_tree]) in
  let outer_expansion =
    ONCE_REWRITE_CONV
      [candle_q_dim_taylor_model_tree_well_formed_def]
      goal in
  let expansion =
    TRANS outer_expansion
      (REWRITE_CONV
        [candle_q_dim_taylor_model_tree_root_boxes_def]
        (rand (concl outer_expansion))) in
  let facts =
    end_itlist CONJ
      [candle_action296_tree_verdict_length;
       candle_action296_tree_verdict_split_lower;
       candle_action296_tree_verdict_split_upper;
       candle_action296_tree_verdict_root_left_lower;
       candle_action296_tree_verdict_root_right_upper;
       candle_action296_tree_verdict_non_split;
       candle_action296_tree_verdict_split_face;
       candle_action296_tree_verdict_left_well_formed;
       candle_action296_tree_verdict_right_well_formed] in
  if not (aconv (rand (concl expansion)) (concl facts)) then
    failwith "action296 tree verdict: topology expansion mismatch";
  EQ_MP (SYM expansion) facts;;

print_endline "CANDLE_CV_ACTION296_TREE_VERDICT event=batch-begin";;
let candle_action296_tree_verdict_result =
  candle_q_dim_taylor_model_batch_prove_six
    candle_action296_tree_verdict_box_prepared
    [candle_action296_tree_verdict_left_cell;
     candle_action296_tree_verdict_right_cell];;
print_endline "CANDLE_CV_ACTION296_TREE_VERDICT event=batch-end";;

print_endline "CANDLE_CV_ACTION296_TREE_VERDICT event=root-source-begin";;
let candle_action296_tree_verdict_source =
  candle_q_dim_taylor_model_tree_source_six
    candle_action296_tree_verdict_result
    candle_action296_tree_verdict_tree
    candle_action296_tree_verdict_well_formed;;
print_endline "CANDLE_CV_ACTION296_TREE_VERDICT event=root-source-end";;

let rec candle_action296_tree_verdict_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_action296_tree_verdict_aconv_lists left_tail right_tail
  | _ -> false;;

print_endline "CANDLE_CV_ACTION296_TREE_VERDICT event=handoff-begin";;
let candle_action296_tree_verdict_theorem =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_tree_verdict_aconv_lists lower
             candle_action296_tree_verdict_parent_lower &&
           candle_action296_tree_verdict_aconv_lists upper
             candle_action296_tree_verdict_parent_upper) then
        failwith "action296 tree verdict: non-root handoff request";
      candle_action296_tree_verdict_source)
    candle_action296_tree_verdict_parent_domain;;
print_endline "CANDLE_CV_ACTION296_TREE_VERDICT event=handoff-end";;

let candle_action296_tree_verdict_functions,
    candle_action296_tree_verdict_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_tree_verdict_theorem);;

let candle_action296_tree_verdict_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_tree_verdict_parent_domain);;

let candle_action296_tree_verdict_theorem_md5 =
  Digest.to_hex
    (Digest.string (string_of_thm candle_action296_tree_verdict_theorem));;

if candle_action296_tree_verdict_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_tree_verdict_proved_domain
       candle_action296_tree_verdict_expected_domain) ||
   hyp candle_action296_tree_verdict_theorem <> [] ||
   candle_action296_tree_verdict_theorem_md5 <>
     "926f44ab8d5f2303064fe5788cead588" then
  failwith "action296 tree verdict: final theorem mismatch";;

let candle_action296_tree_verdict_axioms_after = axioms ();;

if length candle_action296_tree_verdict_axioms_after <>
     length candle_action296_tree_verdict_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_tree_verdict_axioms_before)
       candle_action296_tree_verdict_axioms_after) then
  failwith "action296 tree verdict: changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_TREE_VERDICT_RESULT cells=2 computes=1" ^
   " root_handoffs=1 child_source_extractions=0 external_glues=0" ^
   " theorem_md5=" ^ candle_action296_tree_verdict_theorem_md5 ^
   " profile_events=" ^
   string_of_int (length !candle_action296_tree_verdict_profile_events));;
print_endline
  "CANDLE_CV_ACTION296_TREE_VERDICT_OK DEVELOPMENT_NON_RELEASE";;
