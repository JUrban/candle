(* ========================================================================== *)
(* Assemble one complete genuine Flyspeck inequality from reflected leaves.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The numerical leaf theorems come from the      *)
(* shared-jet batch.  This adapter changes only their domain presentation and  *)
(* applies the legacy verifier's interval split law to the authenticated       *)
(* 16-pass / 15-glue certificate tree.                                        *)
(* ========================================================================== *)

needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_batch.ml";;

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_real_flyspeck_leaf_jet_batch_test;;

module Candle_cv_real_flyspeck_leaf_jet_certificate_test = struct

let candle_real_jet_certificate_index_cases =
  ARITH_RULE
   `1 <= i /\ i <= 6
    ==> i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6`;;

let candle_real_jet_certificate_index_cases_without =
 [GEN `i:num` (ARITH_RULE
   `1 <= i /\ i <= 6 /\ ~(i = 1)
    ==> i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6`);
  GEN `i:num` (ARITH_RULE
   `1 <= i /\ i <= 6 /\ ~(i = 2)
    ==> i = 1 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6`);
  GEN `i:num` (ARITH_RULE
   `1 <= i /\ i <= 6 /\ ~(i = 3)
    ==> i = 1 \/ i = 2 \/ i = 4 \/ i = 5 \/ i = 6`);
  GEN `i:num` (ARITH_RULE
   `1 <= i /\ i <= 6 /\ ~(i = 4)
    ==> i = 1 \/ i = 2 \/ i = 3 \/ i = 5 \/ i = 6`);
  GEN `i:num` (ARITH_RULE
   `1 <= i /\ i <= 6 /\ ~(i = 5)
    ==> i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 6`);
  GEN `i:num` (ARITH_RULE
   `1 <= i /\ i <= 6 /\ ~(i = 6)
    ==> i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5`)];;

let candle_real_jet_certificate_vector_component = prove
 (`!l i.
     1 <= i /\ i <= dimindex (:N)
     ==> ((vector l:A^N)$i = EL (i - 1) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector] THEN
  MATCH_MP_TAC LAMBDA_BETA THEN ASM_REWRITE_TAC[]);;

let candle_real_jet_certificate_discharge_component conditional =
  let premise,_ = dest_imp (concl conditional) in
  MATCH_MP conditional
    (prove
      (premise,
       REWRITE_TAC[IN_NUMSEG;candle_real_jet_batch_dim_six] THEN
       ARITH_TAC));;

let candle_real_jet_certificate_explicit_component vector_tm index =
  let vector_head,vector_args = strip_comb vector_tm in
  if fst (dest_const vector_head) <> "vector" || length vector_args <> 1 then
    failwith "shared-jet certificate expected explicit vector";
  let component_th =
    INST_TYPE [`:6`,`:N`;`:real`,`:A`]
      candle_real_jet_certificate_vector_component in
  candle_real_jet_certificate_discharge_component
    (ISPECL [hd vector_args;mk_small_numeral index] component_th);;

let candle_real_jet_certificate_selector_component
    selector_component boxes index =
  let component_th = INST_TYPE [`:6`,`:N`] selector_component in
  candle_real_jet_certificate_discharge_component
    (ISPECL [boxes;mk_small_numeral index] component_th);;

module Candle_cv_real_flyspeck_leaf_jet_certificate_glue = struct

open Ssreflect
open Ssrfun
open Ssrbool
open Ssrnat

let base = prove
 (`!j x z v u P Q.
     (!i. 1 <= i /\ i <= dimindex (:N) ==> ~(i = j) ==>
       u$i = x$i /\ v$i = z$i) ==>
     v$j = u$j ==>
     (!p. p IN interval [x,v] ==> P p) ==>
     (!p. p IN interval [u,z] ==> Q p) ==>
     (!p. p IN interval [x,z:real^N] ==> P p \/ Q p)`,
  REWRITE_TAC[IN_INTERVAL] THEN REPEAT GEN_TAC THEN
  move ["eq1"; "eq_vu"; "cell1"; "cell2"; "y"; "ineq"] THEN
  ASM_CASES_TAC `(y:real^N)$j <= (v:real^N)$j` THENL
  [
    DISJ1_TAC THEN REMOVE_THEN "cell1" MATCH_MP_TAC THEN
    GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "ineq" (new_rewrite [] []) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i = j:num` THENL
    [
      REPLICATE_TAC 3 (POP_ASSUM MP_TAC) THEN SIMP_TAC[];
      ALL_TAC
    ] THEN
    USE_THEN "eq1" (new_rewrite [] []) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ineq" (new_rewrite [] []) THEN ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN
  POP_ASSUM
    (ASSUME_TAC o MATCH_MP (REAL_ARITH `~(a <= b) ==> b <= a:real`)) THEN
  DISJ2_TAC THEN REMOVE_THEN "cell2" MATCH_MP_TAC THEN
  GEN_TAC THEN DISCH_TAC THEN
  USE_THEN "ineq" (new_rewrite [] []) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = j:num` THENL
  [
    ASM_REWRITE_TAC[] THEN
    USE_THEN "eq_vu" (fun th -> REWRITE_TAC[SYM th]) THEN
    REPLICATE_TAC 3 (POP_ASSUM MP_TAC) THEN SIMP_TAC[];
    ALL_TAC
  ] THEN
  USE_THEN "eq1" (new_rewrite [] []) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ineq" (new_rewrite [] []) THEN ASM_REWRITE_TAC[]);;

end;;

let candle_real_jet_certificate_glue_base =
  Candle_cv_real_flyspeck_leaf_jet_certificate_glue.base;;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE glue-law-ready";;

let candle_real_jet_certificate_vector_identity selector boxes components =
  let encoded = mk_comb (selector,boxes) in
  let explicit =
    mk_comb
      (`vector:real list->real^6`,mk_list (components,`:real`)) in
  let selector_component =
    match fst (dest_const selector) with
    | "candle_q_box_lower_vector" -> candle_q_box_lower_vector_component
    | "candle_q_box_upper_vector" -> candle_q_box_upper_vector_component
    | _ -> failwith "shared-jet certificate unknown box selector" in
  let selector_components =
    map
      (candle_real_jet_certificate_selector_component
        selector_component boxes)
      (1--6) in
  let explicit_components =
    map (candle_real_jet_certificate_explicit_component explicit) (1--6) in
  let goal = mk_eq (encoded,explicit) in
  let tactic =
    REWRITE_TAC[CART_EQ] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_real_jet_batch_dim_six]) THEN
    SUBGOAL_THEN
      `i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6`
      (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
    [MATCH_MP_TAC candle_real_jet_certificate_index_cases THEN
     ASM_REWRITE_TAC[candle_real_jet_batch_dim_six];
     ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC
      (selector_components @ explicit_components @
       [EL;HD;TL;candle_q_real_def;candle_q_den_def;
        candle_lc_zreal_def;candle_real_jet_batch_dim_six;ARITH]) THEN
    CONV_TAC (DEPTH_CONV EL_CONV) THEN
    SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV in
  try prove (goal,tactic) with Failure _ ->
    let _,subgoals,_ = tactic ([],goal) in
    List.iter
      (fun (_,tm) ->
        print_endline
          ("CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE residual=" ^
           string_of_term tm))
      subgoals;
    failwith "shared-jet certificate vector identity failed";;

let candle_real_jet_certificate_leaf_pass source_th (lower,upper) =
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let lower_selector =
    `candle_q_box_lower_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let upper_selector =
    `candle_q_box_upper_vector:
       (((num#num)#num)#((num#num)#num))list->real^6` in
  let lower_eq =
    candle_real_jet_certificate_vector_identity
      lower_selector boxes lower in
  let upper_eq =
    candle_real_jet_certificate_vector_identity
      upper_selector boxes upper in
  let explicit_source_th =
    REWRITE_RULE [lower_eq;upper_eq] source_th in
  explicit_source_th;;

let candle_real_jet_certificate_leaf_passes =
  map2 candle_real_jet_certificate_leaf_pass
    candle_real_jet_batch_theorems
    candle_real_jet_batch_box_sources;;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE leaf-adapters-ready";;

type candle_real_jet_certificate_tree =
  | Candle_real_jet_leaf of int
  | Candle_real_jet_glue of int * candle_real_jet_certificate_tree *
      candle_real_jet_certificate_tree;;

(* Split indices are one-based here, as consumed by the interval glue law. *)
let candle_real_jet_certificate_tree =
  Candle_real_jet_glue (2,
    Candle_real_jet_glue (3,
      Candle_real_jet_glue (6,
        Candle_real_jet_glue (1,
          Candle_real_jet_leaf 0,
          Candle_real_jet_glue (2,
            Candle_real_jet_glue (3,
              Candle_real_jet_glue (6,
                Candle_real_jet_glue (4,
                  Candle_real_jet_leaf 1,
                  Candle_real_jet_leaf 2),
                Candle_real_jet_glue (4,
                  Candle_real_jet_leaf 3,
                  Candle_real_jet_leaf 4)),
              Candle_real_jet_leaf 5),
            Candle_real_jet_leaf 6)),
        Candle_real_jet_glue (1,
          Candle_real_jet_leaf 7,
          Candle_real_jet_glue (2,
            Candle_real_jet_glue (3,
              Candle_real_jet_glue (6,
                Candle_real_jet_glue (4,
                  Candle_real_jet_leaf 8,
                  Candle_real_jet_leaf 9),
                Candle_real_jet_glue (4,
                  Candle_real_jet_leaf 10,
                  Candle_real_jet_leaf 11)),
              Candle_real_jet_leaf 12),
            Candle_real_jet_leaf 13))),
      Candle_real_jet_leaf 14),
    Candle_real_jet_leaf 15);;

let candle_real_jet_certificate_dest_pass th =
  let point,body = dest_forall (concl th) in
  let membership,claim = dest_imp body in
  let in_head,in_args = strip_comb membership in
  if fst (dest_const in_head) <> "IN" || length in_args <> 2 ||
     not (aconv (hd in_args) point) then
    failwith "shared-jet certificate expected interval membership";
  let interval_head,interval_args = strip_comb (List.nth in_args 1) in
  if fst (dest_const interval_head) <> "closed_interval" ||
     length interval_args <> 1 then
    failwith "shared-jet certificate expected interval";
  let interval_items = dest_list (hd interval_args) in
  if length interval_items <> 1 then
    failwith "shared-jet certificate expected one interval pair";
  let lower,upper = dest_pair (hd interval_items) in
  mk_abs (point,claim),lower,upper;;

let candle_real_jet_certificate_debug_prove label goal tactic =
  try prove (goal,tactic) with Failure _ ->
    let _,subgoals,_ = tactic ([],goal) in
    List.iter
      (fun (_,tm) ->
        print_endline
          ("CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE " ^ label ^
           " residual=" ^ string_of_term tm))
      subgoals;
    failwith ("shared-jet certificate " ^ label ^ " failed");;

let candle_real_jet_certificate_coordinate_equalities index x z v u =
  let index_tm = mk_small_numeral index in
  let goal =
    vsubst
      [index_tm,`j:num`;x,`x:real^6`;z,`z:real^6`;
       v,`v:real^6`;u,`u:real^6`]
      `!i. 1 <= i /\ i <= dimindex (:6) ==> ~(i = j) ==>
           (u:real^6)$i = (x:real^6)$i /\
           (v:real^6)$i = (z:real^6)$i` in
  let component_body =
    vsubst
      [x,`x:real^6`;z,`z:real^6`;v,`v:real^6`;u,`u:real^6`]
      `(u:real^6)$i = (x:real^6)$i /\
       (v:real^6)$i = (z:real^6)$i` in
  let component_theorems =
    itlist (@)
      (map
        (fun vector_tm ->
          map (candle_real_jet_certificate_explicit_component vector_tm)
            (1--6))
        [x;z;v;u]) [] in
  let allowed_indices = filter (fun i -> i <> index) (1--6) in
  let exact_component_theorems =
    map
      (fun i ->
        let exact_goal =
          vsubst [mk_small_numeral i,`i:num`] component_body in
        candle_real_jet_certificate_debug_prove
          "coordinate-component" exact_goal
          (SIMP_TAC
            (component_theorems @
             [EL;HD;TL;candle_real_jet_batch_dim_six;ARITH]) THEN
           CONV_TAC (DEPTH_CONV EL_CONV) THEN
           SIMP_TAC[] THEN
           CONV_TAC NUM_REDUCE_CONV THEN
           CONV_TAC REAL_RAT_REDUCE_CONV))
      allowed_indices in
  let point,after_point = dest_forall goal in
  let range_tm,after_range = dest_imp after_point in
  let unequal_tm,_ = dest_imp after_range in
  let range_th = ASSUME range_tm in
  let normalized_range_th =
    REWRITE_RULE[candle_real_jet_batch_dim_six] range_th in
  let unequal_th = ASSUME unequal_tm in
  let left_associated_premise = CONJ normalized_range_th unequal_th in
  let right_associated_premise =
    CONJ (CONJUNCT1 normalized_range_th)
      (CONJ (CONJUNCT2 normalized_range_th) unequal_th) in
  let case_rule =
    SPEC point
      (List.nth candle_real_jet_certificate_index_cases_without
        (index - 1)) in
  let case_premise,_ = dest_imp (concl case_rule) in
  let premise_th =
    try
      find (fun th -> aconv (concl th) case_premise)
        [left_associated_premise;right_associated_premise]
    with Failure _ ->
      failwith "shared-jet certificate index premise shape drift" in
  let cases_th = MP case_rule premise_th in
  let component_predicate = mk_abs (point,component_body) in
  let transport equality_th exact_th =
    let predicate_equality =
      BETA_RULE (AP_TERM component_predicate equality_th) in
    EQ_MP (SYM predicate_equality) exact_th in
  let rec eliminate cases exacts =
    match exacts with
    | [exact_th] -> transport cases exact_th
    | exact_th::rest ->
        let left_tm,right_tm = dest_disj (concl cases) in
        DISJ_CASES cases
          (transport (ASSUME left_tm) exact_th)
          (eliminate (ASSUME right_tm) rest)
    | [] -> failwith "shared-jet certificate empty coordinate cases" in
  let body_th = eliminate cases_th exact_component_theorems in
  let result_th = GEN point (DISCH range_tm (DISCH unequal_tm body_th)) in
  if aconv (concl result_th) goal then result_th
  else failwith "shared-jet certificate coordinate conclusion drift";;

let candle_real_jet_certificate_glue index left_th right_th =
  let left_function,x,v =
    candle_real_jet_certificate_dest_pass left_th in
  let right_function,u,z =
    candle_real_jet_certificate_dest_pass right_th in
  if not (aconv left_function right_function) then
    failwith "shared-jet certificate function drift at glue";
  let coordinate_th =
    candle_real_jet_certificate_coordinate_equalities index x z v u in
  let index_tm = mk_small_numeral index in
  let boundary_goal =
    vsubst
      [index_tm,`j:num`;v,`v:real^6`;u,`u:real^6`]
      `(v:real^6)$j = (u:real^6)$j` in
  let boundary_th =
    let v_component =
      candle_real_jet_certificate_explicit_component v index in
    let u_component =
      candle_real_jet_certificate_explicit_component u index in
    candle_real_jet_certificate_debug_prove "boundary" boundary_goal
     (
      SIMP_TAC[v_component;u_component;EL;HD;TL;ARITH] THEN
      CONV_TAC (DEPTH_CONV EL_CONV) THEN
      SIMP_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV) in
  let glue_th =
    BETA_RULE
      (ISPECL
        [index_tm;x;z;v;u;left_function;left_function]
        candle_real_jet_certificate_glue_base) in
  REWRITE_RULE [TAUT `p \/ p <=> p`]
    (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP glue_th coordinate_th)
      boundary_th) left_th) right_th);;

let rec candle_real_jet_certificate_assemble tree =
  match tree with
  | Candle_real_jet_leaf index ->
      List.nth candle_real_jet_certificate_leaf_passes index
  | Candle_real_jet_glue (index,left,right) ->
      let left_th = candle_real_jet_certificate_assemble left in
      let right_th = candle_real_jet_certificate_assemble right in
      candle_real_jet_certificate_glue index left_th right_th;;

let candle_real_jet_certificate_root_pass =
  candle_real_jet_certificate_assemble candle_real_jet_certificate_tree;;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE root-glue-ready";;

let candle_real_jet_certificate_root_theorem =
  candle_real_jet_certificate_root_pass;;

let rec candle_real_jet_certificate_tree_leaves tree =
  match tree with
  | Candle_real_jet_leaf index -> [index]
  | Candle_real_jet_glue (_,left,right) ->
      candle_real_jet_certificate_tree_leaves left @
      candle_real_jet_certificate_tree_leaves right;;

let rec candle_real_jet_certificate_tree_glues tree =
  match tree with
  | Candle_real_jet_leaf _ -> 0
  | Candle_real_jet_glue (_,left,right) ->
      candle_real_jet_certificate_tree_glues left +
      candle_real_jet_certificate_tree_glues right + 1;;

let candle_real_jet_certificate_leaf_indices =
  candle_real_jet_certificate_tree_leaves
    candle_real_jet_certificate_tree;;

let candle_real_jet_certificate_glue_count =
  candle_real_jet_certificate_tree_glues
    candle_real_jet_certificate_tree;;

let candle_real_jet_certificate_root_function,
    candle_real_jet_certificate_root_lower,
    candle_real_jet_certificate_root_upper =
  candle_real_jet_certificate_dest_pass
    candle_real_jet_certificate_root_theorem;;

let candle_real_jet_certificate_first_function,
    candle_real_jet_certificate_first_lower,_ =
  candle_real_jet_certificate_dest_pass
    (hd candle_real_jet_certificate_leaf_passes);;

let _,_,candle_real_jet_certificate_last_upper =
  candle_real_jet_certificate_dest_pass
    (List.nth candle_real_jet_certificate_leaf_passes 15);;

if length candle_real_jet_certificate_leaf_passes <> 16 ||
   candle_real_jet_certificate_leaf_indices <> (0--15) ||
   candle_real_jet_certificate_glue_count <> 15 ||
   hyp candle_real_jet_certificate_root_pass <> [] ||
   hyp candle_real_jet_certificate_root_theorem <> [] ||
   not (aconv candle_real_jet_certificate_root_function
          candle_real_jet_certificate_first_function) ||
   not (aconv candle_real_jet_certificate_root_lower
          candle_real_jet_certificate_first_lower) ||
   not (aconv candle_real_jet_certificate_root_upper
          candle_real_jet_certificate_last_upper) then
  failwith "shared-jet certificate root theorem drift";;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE_RESULT leaves=16 glues=15 " ^
     "theorem_md5=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm candle_real_jet_certificate_root_theorem)));;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_JET_CERTIFICATE_OK";;

end;;
