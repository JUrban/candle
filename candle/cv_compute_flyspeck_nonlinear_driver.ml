(* ========================================================================== *)
(* A reflected-leaf callback for the Flyspeck nonlinear certificate driver.  *)
(*                                                                            *)
(* The adaptive certificate and its split/glue proof remain the authoritative *)
(* driver.  Only an ordinary non-raw pass leaf is replaced: its live logical  *)
(* domain is normalized to exact rationals, checked by the shared-jet program, *)
(* and transported back to the verifier's original domain presentation.       *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_prove.ml";;

module Candle_cv_flyspeck_nonlinear_driver = struct

open Certificate;;
open Report;;
open Verifier_options;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_polynomial_expr_dim_jet_prove;;

let candle_reflected_nl_index_cases =
  ARITH_RULE
   `1 <= i /\ i <= 6
    ==> i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6`;;

let candle_reflected_nl_vector_component = prove
 (`!l i.
     1 <= i /\ i <= dimindex (:N)
     ==> ((vector l:A^N)$i = EL (i - 1) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_REWRITE_TAC[]);;

let candle_reflected_nl_discharge_component conditional =
  let premise,_ = dest_imp (concl conditional) in
  MATCH_MP conditional
    (prove
      (premise,
       REWRITE_TAC[IN_NUMSEG;candle_q_dim_poly_jet_dim_six] THEN
       ARITH_TAC));;

let candle_reflected_nl_explicit_component vector_tm index =
  let vector_head,vector_args = strip_comb vector_tm in
  if fst (dest_const vector_head) <> "vector" || length vector_args <> 1 then
    failwith "reflected nonlinear driver: expected explicit vector";
  let component_th =
    INST_TYPE [`:6`,`:N`;`:real`,`:A`]
      candle_reflected_nl_vector_component in
  candle_reflected_nl_discharge_component
    (ISPECL [hd vector_args;mk_small_numeral index] component_th);;

let candle_reflected_nl_selector_component selector_component boxes index =
  let component_th = INST_TYPE [`:6`,`:N`] selector_component in
  candle_reflected_nl_discharge_component
    (ISPECL [boxes;mk_small_numeral index] component_th);;

let candle_reflected_nl_selector_vector_identity selector boxes components =
  let encoded = mk_comb (selector,boxes) in
  let explicit =
    mk_comb
      (`vector:real list->real^6`,mk_list (components,`:real`)) in
  let selector_component =
    match fst (dest_const selector) with
    | "candle_q_box_lower_vector" -> candle_q_box_lower_vector_component
    | "candle_q_box_upper_vector" -> candle_q_box_upper_vector_component
    | _ -> failwith "reflected nonlinear driver: unknown box selector" in
  let selector_components =
    map
      (candle_reflected_nl_selector_component selector_component boxes)
      (1--6) in
  let explicit_components =
    map (candle_reflected_nl_explicit_component explicit) (1--6) in
  let goal = mk_eq (encoded,explicit) in
  prove
    (goal,
     REWRITE_TAC[CART_EQ] THEN
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_poly_jet_dim_six]) THEN
     SUBGOAL_THEN
       `i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6`
       (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
     [MATCH_MP_TAC candle_reflected_nl_index_cases THEN
      ASM_REWRITE_TAC[candle_q_dim_poly_jet_dim_six];
      ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC
       (selector_components @ explicit_components @
        [EL;HD;TL;candle_q_real_def;candle_q_den_def;
         candle_lc_zreal_def;candle_q_dim_poly_jet_dim_six;ARITH]) THEN
     CONV_TAC (DEPTH_CONV EL_CONV) THEN
     SIMP_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_reflected_nl_exact_component tm =
  try
    let _ = rat_of_term tm in
    REFL tm
  with Failure _ ->
    let th = Arith_float.FLOAT_TO_NUM_CONV tm in
    let _ = rat_of_term (rand (concl th)) in
    th;;

let candle_reflected_nl_normalize_vector vector_tm =
  let vector_head,vector_args = strip_comb vector_tm in
  if fst (dest_const vector_head) <> "vector" || length vector_args <> 1 then
    failwith "reflected nonlinear driver: expected live explicit vector";
  let list_tm = hd vector_args in
  let components = dest_list list_tm in
  if length components <> 6 then
    failwith "reflected nonlinear driver: expected six live coordinates";
  let component_theorems = map candle_reflected_nl_exact_component components in
  let list_theorem = PURE_REWRITE_CONV component_theorems list_tm in
  let vector_theorem = AP_TERM vector_head list_theorem in
  let normalized_components = dest_list (rand (concl list_theorem)) in
  if hyp vector_theorem <> [] ||
     not (aconv (lhand (concl vector_theorem)) vector_tm) then
    failwith "reflected nonlinear driver: endpoint normalization mismatch";
  normalized_components,vector_theorem;;

let candle_reflected_nl_source_pass prepared domain_th =
  let domain,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain in
  let lower,actual_lower_theorem =
    candle_reflected_nl_normalize_vector actual_lower in
  let upper,actual_upper_theorem =
    candle_reflected_nl_normalize_vector actual_upper in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let source_theorem =
    candle_q_dim_poly_jet_prove_box_six prepared lower upper in
  let lower_selector =
    `candle_q_box_lower_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let upper_selector =
    `candle_q_box_upper_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let lower_selector_theorem =
    candle_reflected_nl_selector_vector_identity lower_selector boxes lower in
  let upper_selector_theorem =
    candle_reflected_nl_selector_vector_identity upper_selector boxes upper in
  let lower_transport =
    TRANS lower_selector_theorem (SYM actual_lower_theorem) in
  let upper_transport =
    TRANS upper_selector_theorem (SYM actual_upper_theorem) in
  let live_source_theorem =
    REWRITE_RULE [lower_transport;upper_transport] source_theorem in
  let point,body = dest_forall (concl live_source_theorem) in
  let membership,claim = dest_imp body in
  let relation_args = snd (strip_comb claim) in
  let source_at_point = hd relation_args in
  let function_tm = mk_abs (point,source_at_point) in
  if not (aconv function_tm prepared.function_term) ||
     hyp domain_th <> [] || hyp live_source_theorem <> [] then
    failwith "reflected nonlinear driver: live source mismatch";
  let cell_goal =
    list_mk_comb (`m_cell_pass:(real^6->real)->(real^6#real^6)->bool`,
                  [prepared.function_term;domain]) in
  let cell_expansion = REWRITE_CONV [M_verifier.m_cell_pass] cell_goal in
  if not (aconv (rand (concl cell_expansion))
                 (concl live_source_theorem)) then
    failwith "reflected nonlinear driver: cell theorem mismatch";
  let cell_theorem = EQ_MP (SYM cell_expansion) live_source_theorem in
  let list_theorem =
    MATCH_MP M_verifier.M_CELL_PASS_IMP_LIST_PASS1 cell_theorem in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass (concl list_theorem) in
  if functions <> [prepared.function_term] ||
     not (aconv proved_domain domain) || hyp list_theorem <> [] then
    failwith "reflected nonlinear driver: leaf result mismatch";
  list_theorem;;

let candle_reflected_nl_verify_disj_raw
    _ n p_split fs_list leaf_check certificate domain_th0 th_list =
  let rec rec_verify domain_th certificate =
    match certificate with
    | P_result_mono _ ->
        failwith "reflected nonlinear driver: monotonicity not implemented"
    | P_result_pass (p_status,function_index,raw_flag) ->
        let verifier = List.nth fs_list function_index in
        leaf_check p_status function_index raw_flag verifier domain_th
    | P_result_glue (_,split_index,convex_flag,left,right) ->
        if convex_flag then
          failwith "reflected nonlinear driver: convexity not implemented";
        let left_domain,right_domain =
          M_verifier.split_domain n p_split (split_index + 1) domain_th in
        let left_theorem = rec_verify left_domain left in
        let right_theorem = rec_verify right_domain right in
        let append_theorem =
          M_verifier.m_glue_cells_list
            n (split_index + 1) left_theorem right_theorem in
        M_verifier.merge_m_cell_list_pass n append_theorem
    | P_result_ref index ->
        if index > 0 then List.nth th_list (index - 1)
        else
          let domain,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
          let pass_theorem = List.nth th_list (-index - 1) in
          M_verifier.m_cell_list_pass_subdomain domain pass_theorem in
  rec_verify domain_th0 certificate;;

let candle_reflected_nl_verify_disj_raw0
    n p_split fs_list leaf_check certificate lower upper =
  candle_reflected_nl_verify_disj_raw
    (0,0) n p_split fs_list leaf_check certificate
    (M_taylor.mk_m_center_domain n p_split lower upper) [];;

end;;
