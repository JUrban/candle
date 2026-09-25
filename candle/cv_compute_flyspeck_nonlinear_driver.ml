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

let candle_reflected_nl_profile = ref (fun (_:string) -> ());;

let candle_reflected_nl_profile_event event =
  (!candle_reflected_nl_profile) event;;

let candle_reflected_nl_vector_component = prove
 (`!l i.
     1 <= i /\ i <= dimindex (:N)
     ==> ((vector l:A^N)$i = EL (i - 1) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_REWRITE_TAC[]);;

let candle_reflected_nl_lower_vector_list = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     (candle_q_box_lower_vector boxes : real^N) =
       vector (MAP (\box. candle_q_real (FST box)) boxes)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[IN_NUMSEG]) THEN
  SUBGOAL_THEN
    `i - 1 <
     LENGTH (boxes:(((num#num)#num)#((num#num)#num))list)`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
    [ASM_SIMP_TAC[SUB_ADD];
      ASM_REWRITE_TAC[GSYM LE_SUC_LT;ADD1]];
    ASM_SIMP_TAC[candle_q_box_lower_vector_def;
                 candle_reflected_nl_vector_component;EL_MAP] THEN
    MATCH_MP_TAC LAMBDA_BETA THEN ASM_REWRITE_TAC[IN_NUMSEG]]);;

let candle_reflected_nl_upper_vector_list = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N)
     ==>
     (candle_q_box_upper_vector boxes : real^N) =
       vector (MAP (\box. candle_q_real (SND box)) boxes)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[IN_NUMSEG]) THEN
  SUBGOAL_THEN
    `i - 1 <
     LENGTH (boxes:(((num#num)#num)#((num#num)#num))list)`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SUB_ADD];
      ASM_REWRITE_TAC[GSYM LE_SUC_LT;ADD1]];
    ASM_SIMP_TAC[candle_q_box_upper_vector_def;
                 candle_reflected_nl_vector_component;EL_MAP] THEN
    MATCH_MP_TAC LAMBDA_BETA THEN ASM_REWRITE_TAC[IN_NUMSEG]]);;

let candle_reflected_nl_q_real_identity encoded component =
  prove
    (mk_eq (mk_comb (`candle_q_real`,encoded),component),
     REWRITE_TAC[candle_q_real_def;candle_q_den_def;candle_lc_zreal_def] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_reflected_nl_selector_vector_identity selector boxes components =
  let encoded = mk_comb (selector,boxes) in
  let explicit =
    mk_comb
      (`vector:real list->real^6`,mk_list (components,`:real`)) in
  let selector_list_theorem =
    match fst (dest_const selector) with
    | "candle_q_box_lower_vector" ->
        candle_reflected_nl_lower_vector_list
    | "candle_q_box_upper_vector" ->
        candle_reflected_nl_upper_vector_list
    | _ -> failwith "reflected nonlinear driver: unknown box selector" in
  let choose_component =
    match fst (dest_const selector) with
    | "candle_q_box_lower_vector" -> fst o dest_pair
    | "candle_q_box_upper_vector" -> snd o dest_pair
    | _ -> failwith "reflected nonlinear driver: unknown box selector" in
  let encoded_components = map choose_component (dest_list boxes) in
  let component_identities =
    map2 candle_reflected_nl_q_real_identity encoded_components components in
  let _ = candle_reflected_nl_profile_event "selector-length-begin" in
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let _ = candle_reflected_nl_profile_event "selector-length-complete" in
  let abstract_identity =
    MATCH_MP
      (SPEC boxes
        (REWRITE_RULE[candle_q_dim_poly_jet_dim_six]
          (INST_TYPE [`:6`,`:N`] selector_list_theorem)))
      length_six in
  let _ = candle_reflected_nl_profile_event "selector-abstract-complete" in
  let expanded_identity =
    PURE_REWRITE_RULE [FST;SND]
      (BETA_RULE (PURE_REWRITE_RULE [MAP] abstract_identity)) in
  let identity =
    PURE_REWRITE_RULE component_identities expanded_identity in
  let _ = candle_reflected_nl_profile_event "selector-normalize-complete" in
  if hyp identity <> [] ||
     not (aconv (lhand (concl identity)) encoded) ||
     not (aconv (rand (concl identity)) explicit) then
    failwith "reflected nonlinear driver: selector identity mismatch";
  identity;;

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

let candle_reflected_nl_source_pass_with
    function_term prove_box domain_th =
  let domain,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain in
  let lower,actual_lower_theorem =
    candle_reflected_nl_normalize_vector actual_lower in
  let _ = candle_reflected_nl_profile_event "normalize-lower-complete" in
  let upper,actual_upper_theorem =
    candle_reflected_nl_normalize_vector actual_upper in
  let _ = candle_reflected_nl_profile_event "normalize-upper-complete" in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let source_theorem = prove_box lower upper in
  let _ = candle_reflected_nl_profile_event "source-proof-complete" in
  let lower_selector =
    `candle_q_box_lower_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let upper_selector =
    `candle_q_box_upper_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let lower_selector_theorem =
    candle_reflected_nl_selector_vector_identity lower_selector boxes lower in
  let _ = candle_reflected_nl_profile_event "lower-transport-complete" in
  let upper_selector_theorem =
    candle_reflected_nl_selector_vector_identity upper_selector boxes upper in
  let _ = candle_reflected_nl_profile_event "upper-transport-complete" in
  let lower_transport =
    TRANS lower_selector_theorem (SYM actual_lower_theorem) in
  let upper_transport =
    TRANS upper_selector_theorem (SYM actual_upper_theorem) in
  let live_source_theorem =
    REWRITE_RULE [lower_transport;upper_transport] source_theorem in
  let _ = candle_reflected_nl_profile_event "source-rewrite-complete" in
  let point,body = dest_forall (concl live_source_theorem) in
  let membership,claim = dest_imp body in
  let relation_args = snd (strip_comb claim) in
  let source_at_point = hd relation_args in
  let function_tm = mk_abs (point,source_at_point) in
  if not (aconv function_tm function_term) ||
     hyp domain_th <> [] || hyp live_source_theorem <> [] then
    failwith "reflected nonlinear driver: live source mismatch";
  let cell_goal =
    list_mk_comb (`m_cell_pass:(real^6->real)->(real^6#real^6)->bool`,
                  [function_term;domain]) in
  let cell_expansion = REWRITE_CONV [M_verifier.m_cell_pass] cell_goal in
  if not (aconv (rand (concl cell_expansion))
                 (concl live_source_theorem)) then
    failwith "reflected nonlinear driver: cell theorem mismatch";
  let cell_theorem = EQ_MP (SYM cell_expansion) live_source_theorem in
  let list_theorem =
    MATCH_MP M_verifier.M_CELL_PASS_IMP_LIST_PASS1 cell_theorem in
  let _ = candle_reflected_nl_profile_event "cell-handoff-complete" in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass (concl list_theorem) in
  if functions <> [function_term] ||
     not (aconv proved_domain domain) || hyp list_theorem <> [] then
    failwith "reflected nonlinear driver: leaf result mismatch";
  list_theorem;;

let candle_reflected_nl_source_pass prepared domain_th =
  candle_reflected_nl_source_pass_with
    prepared.function_term
    (candle_q_dim_poly_jet_prove_box_six prepared)
    domain_th;;

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
        let merged = M_verifier.merge_m_cell_list_pass n append_theorem in
        let _ = candle_reflected_nl_profile_event "glue-complete" in
        merged
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
