(* ========================================================================== *)
(* Direct analytic soundness of exact object-q multiplication.               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fixed-word checker refines a rational     *)
(* object operation which fuses the sums of interval products used by the    *)
(* product rule.  This file mirrors that exact association order; it does not *)
(* replace it with the older normalized decimal jet operation.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_add_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_mul_sound = struct

open Candle_cv_exact_interval_mul_core;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_add_sound;;

(* The two- and four-product operations are the only arities used by the
   object checker.  Their nesting is exactly the left-to-right accumulator
   nesting in [bounded_object_q_interval_products_sum_acc_cv]. *)

let candle_q_packed_object_products_sum2_def = new_definition
 `candle_q_packed_object_products_sum2
      first_left first_right second_left second_right =
    candle_q_interval_add
      (candle_q_interval_add candle_q_zero_interval
        (candle_q_interval_mul first_left first_right))
      (candle_q_interval_mul second_left second_right)`;;

let candle_q_packed_object_products_sum2_sound = prove
 (`!first_left first_right second_left second_right
       first_left_value first_right_value
       second_left_value second_right_value.
     candle_q_interval_contains first_left first_left_value /\
     candle_q_interval_contains first_right first_right_value /\
     candle_q_interval_contains second_left second_left_value /\
     candle_q_interval_contains second_right second_right_value
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_products_sum2
         first_left first_right second_left second_right)
       (first_left_value * first_right_value +
        second_left_value * second_right_value)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_products_sum2_def] THEN
  let first_product = MATCH_MP
    (SPECL
      [`first_left:((num#num)#num)#((num#num)#num)`;
       `first_right:((num#num)#num)#((num#num)#num)`;
       `first_left_value:real`; `first_right_value:real`]
      candle_q_interval_mul_sound)
    (CONJ
      (ASSUME `candle_q_interval_contains first_left first_left_value`)
      (ASSUME `candle_q_interval_contains first_right first_right_value`)) in
  let second_product = MATCH_MP
    (SPECL
      [`second_left:((num#num)#num)#((num#num)#num)`;
       `second_right:((num#num)#num)#((num#num)#num)`;
       `second_left_value:real`; `second_right_value:real`]
      candle_q_interval_mul_sound)
    (CONJ
      (ASSUME `candle_q_interval_contains second_left second_left_value`)
      (ASSUME `candle_q_interval_contains second_right second_right_value`)) in
  let first_sum = REWRITE_RULE[REAL_ADD_LID]
    (MATCH_MP
      (SPECL
        [`candle_q_zero_interval`;
         `candle_q_interval_mul first_left first_right`;
         `&0`; `first_left_value * first_right_value`]
        candle_q_interval_add_sound)
      (CONJ candle_q_zero_interval_contains first_product)) in
  ACCEPT_TAC
    (MATCH_MP
      (SPECL
        [`candle_q_interval_add candle_q_zero_interval
            (candle_q_interval_mul first_left first_right)`;
         `candle_q_interval_mul second_left second_right`;
         `first_left_value * first_right_value`;
         `second_left_value * second_right_value`]
        candle_q_interval_add_sound)
      (CONJ first_sum second_product)));;

let candle_q_packed_object_products_sum4_def = new_definition
 `candle_q_packed_object_products_sum4
      first_left first_right second_left second_right
      third_left third_right fourth_left fourth_right =
    candle_q_interval_add
      (candle_q_interval_add
        (candle_q_interval_add
          (candle_q_interval_add candle_q_zero_interval
            (candle_q_interval_mul first_left first_right))
          (candle_q_interval_mul second_left second_right))
        (candle_q_interval_mul third_left third_right))
      (candle_q_interval_mul fourth_left fourth_right)`;;

let candle_q_packed_object_products_sum4_sound = prove
 (`!first_left first_right second_left second_right
       third_left third_right fourth_left fourth_right
       first_left_value first_right_value
       second_left_value second_right_value
       third_left_value third_right_value
       fourth_left_value fourth_right_value.
     candle_q_interval_contains first_left first_left_value /\
     candle_q_interval_contains first_right first_right_value /\
     candle_q_interval_contains second_left second_left_value /\
     candle_q_interval_contains second_right second_right_value /\
     candle_q_interval_contains third_left third_left_value /\
     candle_q_interval_contains third_right third_right_value /\
     candle_q_interval_contains fourth_left fourth_left_value /\
     candle_q_interval_contains fourth_right fourth_right_value
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_products_sum4
         first_left first_right second_left second_right
         third_left third_right fourth_left fourth_right)
       (((first_left_value * first_right_value +
          second_left_value * second_right_value) +
         third_left_value * third_right_value) +
        fourth_left_value * fourth_right_value)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_products_sum4_def] THEN
  let product_sound left right left_value right_value =
    MATCH_MP
      (SPECL [left; right; left_value; right_value]
        candle_q_interval_mul_sound)
      (CONJ
        (ASSUME (mk_comb
          (mk_comb (`candle_q_interval_contains`,left),left_value)))
        (ASSUME (mk_comb
          (mk_comb (`candle_q_interval_contains`,right),right_value)))) in
  let first_product = product_sound
    `first_left:((num#num)#num)#((num#num)#num)`
    `first_right:((num#num)#num)#((num#num)#num)`
    `first_left_value:real` `first_right_value:real` in
  let second_product = product_sound
    `second_left:((num#num)#num)#((num#num)#num)`
    `second_right:((num#num)#num)#((num#num)#num)`
    `second_left_value:real` `second_right_value:real` in
  let third_product = product_sound
    `third_left:((num#num)#num)#((num#num)#num)`
    `third_right:((num#num)#num)#((num#num)#num)`
    `third_left_value:real` `third_right_value:real` in
  let fourth_product = product_sound
    `fourth_left:((num#num)#num)#((num#num)#num)`
    `fourth_right:((num#num)#num)#((num#num)#num)`
    `fourth_left_value:real` `fourth_right_value:real` in
  let first_sum = REWRITE_RULE[REAL_ADD_LID]
    (MATCH_MP
      (SPECL
        [`candle_q_zero_interval`;
         `candle_q_interval_mul first_left first_right`;
         `&0`; `first_left_value * first_right_value`]
        candle_q_interval_add_sound)
      (CONJ candle_q_zero_interval_contains first_product)) in
  let second_sum = MATCH_MP
    (SPECL
      [`candle_q_interval_add candle_q_zero_interval
          (candle_q_interval_mul first_left first_right)`;
       `candle_q_interval_mul second_left second_right`;
       `first_left_value * first_right_value`;
       `second_left_value * second_right_value`]
      candle_q_interval_add_sound)
    (CONJ first_sum second_product) in
  let third_sum = MATCH_MP
    (SPECL
      [`candle_q_interval_add
          (candle_q_interval_add candle_q_zero_interval
            (candle_q_interval_mul first_left first_right))
          (candle_q_interval_mul second_left second_right)`;
       `candle_q_interval_mul third_left third_right`;
       `first_left_value * first_right_value +
          second_left_value * second_right_value`;
       `third_left_value * third_right_value`]
      candle_q_interval_add_sound)
    (CONJ second_sum third_product) in
  ACCEPT_TAC
    (MATCH_MP
      (SPECL
        [`candle_q_interval_add
            (candle_q_interval_add
              (candle_q_interval_add candle_q_zero_interval
                (candle_q_interval_mul first_left first_right))
              (candle_q_interval_mul second_left second_right))
            (candle_q_interval_mul third_left third_right)`;
         `candle_q_interval_mul fourth_left fourth_right`;
         `(first_left_value * first_right_value +
            second_left_value * second_right_value) +
           third_left_value * third_right_value`;
         `fourth_left_value * fourth_right_value`]
        candle_q_interval_add_sound)
      (CONJ third_sum fourth_product)));;

(* Exact counterpart of [bounded_object_q_interval_fused_scale_add_cv]. *)

let candle_q_packed_object_fused_scale_add_def = new_definition
 `candle_q_packed_object_fused_scale_add
      left_scale left right_scale right =
    MAP2
      (\left_entry right_entry.
         candle_q_packed_object_products_sum2
           left_scale left_entry right_scale right_entry)
      left right`;;

let candle_real_packed_object_fused_scale_add_def = new_definition
 `candle_real_packed_object_fused_scale_add
      left_scale left right_scale right =
    MAP2
      (\left_entry right_entry.
         left_scale * left_entry + right_scale * right_entry)
      left right`;;

let candle_q_packed_object_fused_scale_add_lookup = prove
 (`!left_scale left right_scale right i.
     LENGTH left = LENGTH right /\ i < LENGTH left
     ==>
     candle_q_interval_lookup i
       (candle_q_packed_object_fused_scale_add
         left_scale left right_scale right) =
     candle_q_packed_object_products_sum2
       left_scale (candle_q_interval_lookup i left)
       right_scale (candle_q_interval_lookup i right)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH
      (right:(((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_packed_object_fused_scale_add_def;
               LENGTH_MAP2; EL_MAP2;
               candle_q_interval_lookup_in_range]);;

let candle_q_packed_object_fused_scale_add_component_sound = prove
 (`!left_scale left right_scale right i
       left_scale_value right_scale_value left_value right_value.
     LENGTH left = LENGTH right /\ i < LENGTH left /\
     candle_q_interval_contains left_scale left_scale_value /\
     candle_q_interval_contains right_scale right_scale_value /\
     candle_q_interval_contains
       (candle_q_interval_lookup i left) left_value /\
     candle_q_interval_contains
       (candle_q_interval_lookup i right) right_value
     ==>
     candle_q_interval_contains
       (candle_q_interval_lookup i
         (candle_q_packed_object_fused_scale_add
           left_scale left right_scale right))
       (left_scale_value * left_value +
        right_scale_value * right_value)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_fused_scale_add_lookup] THEN
  MATCH_MP_TAC candle_q_packed_object_products_sum2_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_fused_scale_add_length = prove
 (`!left_scale left right_scale right.
     LENGTH left = LENGTH right
     ==>
     LENGTH (candle_q_packed_object_fused_scale_add
       left_scale left right_scale right) = LENGTH left`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_fused_scale_add_def; LENGTH_MAP2]);;

(* One packed Hessian entry.  [outer] stores the two symmetric gradient
   products in the same order as the HOL4 fused-product operation. *)

let candle_q_packed_object_symmetric_product_pair_def = new_definition
 `candle_q_packed_object_symmetric_product_pair left right i j =
    ((candle_q_interval_lookup i left,
      candle_q_interval_lookup j right),
     (candle_q_interval_lookup i right,
      candle_q_interval_lookup j left))`;;

let candle_q_packed_object_fused_hessian_entry_def = new_definition
 `candle_q_packed_object_fused_hessian_entry
      left_value right_value left_hessian right_hessian outer =
    candle_q_packed_object_products_sum4
      right_value left_hessian
      (FST (FST outer)) (SND (FST outer))
      (FST (SND outer)) (SND (SND outer))
      left_value right_hessian`;;

let candle_q_packed_object_fused_hessian_entry_sound = prove
 (`!left_value right_value left_hessian right_hessian
       left_gradient_i right_gradient_j right_gradient_i left_gradient_j
       left_value_real right_value_real
       left_hessian_real right_hessian_real
       left_gradient_i_real right_gradient_j_real
       right_gradient_i_real left_gradient_j_real.
     candle_q_interval_contains left_value left_value_real /\
     candle_q_interval_contains right_value right_value_real /\
     candle_q_interval_contains left_hessian left_hessian_real /\
     candle_q_interval_contains right_hessian right_hessian_real /\
     candle_q_interval_contains left_gradient_i left_gradient_i_real /\
     candle_q_interval_contains right_gradient_j right_gradient_j_real /\
     candle_q_interval_contains right_gradient_i right_gradient_i_real /\
     candle_q_interval_contains left_gradient_j left_gradient_j_real
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_fused_hessian_entry
         left_value right_value left_hessian right_hessian
         ((left_gradient_i,right_gradient_j),
          (right_gradient_i,left_gradient_j)))
       (((right_value_real * left_hessian_real +
          left_gradient_i_real * right_gradient_j_real) +
         right_gradient_i_real * left_gradient_j_real) +
        left_value_real * right_hessian_real)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_fused_hessian_entry_def; FST; SND] THEN
  MATCH_MP_TAC candle_q_packed_object_products_sum4_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_symmetric_product_pair_sound = prove
 (`!left right i j left_i right_j right_i left_j
       left_i_real right_j_real right_i_real left_j_real.
     candle_q_interval_contains left_i left_i_real /\
     candle_q_interval_contains right_j right_j_real /\
     candle_q_interval_contains right_i right_i_real /\
     candle_q_interval_contains left_j left_j_real /\
     left_i = candle_q_interval_lookup i left /\
     right_j = candle_q_interval_lookup j right /\
     right_i = candle_q_interval_lookup i right /\
     left_j = candle_q_interval_lookup j left
     ==>
     candle_q_packed_object_symmetric_product_pair left right i j =
       ((left_i,right_j),(right_i,left_j))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_q_packed_object_symmetric_product_pair_def]);;

let candle_q_packed_object_hessian6_row_def = new_definition
 `candle_q_packed_object_hessian6_row i =
    if i < 6 then 0
    else if i < 11 then 1
    else if i < 15 then 2
    else if i < 18 then 3
    else if i < 20 then 4
    else 5`;;

let candle_q_packed_object_hessian6_col_def = new_definition
 `candle_q_packed_object_hessian6_col i =
    if i < 6 then i
    else if i < 11 then i - 5
    else if i < 15 then i - 9
    else if i < 18 then i - 12
    else if i < 20 then i - 14
    else 5`;;

let candle_q_packed_object_hessian6_coordinate_bounds = prove
  (`!i. i < 21
       ==> candle_q_packed_object_hessian6_row i < 6 /\
           candle_q_packed_object_hessian6_col i < 6`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
              candle_q_packed_object_hessian6_col_def] THEN
  ASM_CASES_TAC `i < 6` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 11` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 15` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 18` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < 20` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let candle_q_packed_object_hessian6_index_row_def = new_definition
 `candle_q_packed_object_hessian6_index_row (rowindex:num) =
    if rowindex = 0 then ([0;1;2;3;4;5]:num list)
    else if rowindex = 1 then [1;6;7;8;9;10]
    else if rowindex = 2 then [2;7;11;12;13;14]
    else if rowindex = 3 then [3;8;12;15;16;17]
    else if rowindex = 4 then [4;9;13;16;18;19]
    else [5;10;14;17;19;20]`;;

let candle_q_packed_object_hessian6_index_row_0 = prove
 (`candle_q_packed_object_hessian6_index_row 0 = [0;1;2;3;4;5]`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def]);;

let candle_q_packed_object_hessian6_index_row_1 = prove
 (`candle_q_packed_object_hessian6_index_row 1 = [1;6;7;8;9;10]`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def;
              ARITH_RULE `~(1 = 0)`]);;

let candle_q_packed_object_hessian6_index_row_2 = prove
 (`candle_q_packed_object_hessian6_index_row 2 = [2;7;11;12;13;14]`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def;
              ARITH_RULE `~(2 = 0)`; ARITH_RULE `~(2 = 1)`]);;

let candle_q_packed_object_hessian6_index_row_3 = prove
 (`candle_q_packed_object_hessian6_index_row 3 = [3;8;12;15;16;17]`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def;
              ARITH_RULE `~(3 = 0)`; ARITH_RULE `~(3 = 1)`;
              ARITH_RULE `~(3 = 2)`]);;

let candle_q_packed_object_hessian6_index_row_4 = prove
 (`candle_q_packed_object_hessian6_index_row 4 = [4;9;13;16;18;19]`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def;
              ARITH_RULE `~(4 = 0)`; ARITH_RULE `~(4 = 1)`;
              ARITH_RULE `~(4 = 2)`; ARITH_RULE `~(4 = 3)`]);;

let candle_q_packed_object_hessian6_index_row_5 = prove
 (`candle_q_packed_object_hessian6_index_row 5 = [5;10;14;17;19;20]`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def;
              ARITH_RULE `~(5 = 0)`; ARITH_RULE `~(5 = 1)`;
              ARITH_RULE `~(5 = 2)`; ARITH_RULE `~(5 = 3)`;
              ARITH_RULE `~(5 = 4)`]);;

let candle_q_packed_object_hessian6_index_row_length = prove
 (`!rowindex.
     LENGTH (candle_q_packed_object_hessian6_index_row rowindex) = 6`,
  GEN_TAC THEN REWRITE_TAC[candle_q_packed_object_hessian6_index_row_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_hessian6_index_row_0_tail = prove
 (`!columnindex. columnindex < 6
       ==> EL columnindex
             (candle_q_packed_object_hessian6_index_row 0) = columnindex`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ARITH_RULE
      `columnindex < 6
       ==> columnindex = 0 \/ columnindex = 1 \/ columnindex = 2 \/
           columnindex = 3 \/ columnindex = 4 \/ columnindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_0] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let candle_q_packed_object_hessian6_index_row_1_tail = prove
 (`!columnindex. 1 <= columnindex /\ columnindex < 6
       ==> EL columnindex
             (candle_q_packed_object_hessian6_index_row 1) =
           columnindex + 5`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ARITH_RULE
      `1 <= columnindex /\ columnindex < 6
       ==> columnindex = 1 \/ columnindex = 2 \/ columnindex = 3 \/
           columnindex = 4 \/ columnindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_1] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN ARITH_TAC);;

let candle_q_packed_object_hessian6_index_row_2_tail = prove
 (`!columnindex. 2 <= columnindex /\ columnindex < 6
       ==> EL columnindex
             (candle_q_packed_object_hessian6_index_row 2) =
           columnindex + 9`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ARITH_RULE
      `2 <= columnindex /\ columnindex < 6
       ==> columnindex = 2 \/ columnindex = 3 \/
           columnindex = 4 \/ columnindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_2] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN ARITH_TAC);;

let candle_q_packed_object_hessian6_index_row_3_tail = prove
 (`!columnindex. 3 <= columnindex /\ columnindex < 6
       ==> EL columnindex
             (candle_q_packed_object_hessian6_index_row 3) =
           columnindex + 12`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ARITH_RULE
      `3 <= columnindex /\ columnindex < 6
       ==> columnindex = 3 \/ columnindex = 4 \/ columnindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_3] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN ARITH_TAC);;

let candle_q_packed_object_hessian6_index_row_4_tail = prove
 (`!columnindex. 4 <= columnindex /\ columnindex < 6
       ==> EL columnindex
             (candle_q_packed_object_hessian6_index_row 4) =
           columnindex + 14`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ARITH_RULE
      `4 <= columnindex /\ columnindex < 6
       ==> columnindex = 4 \/ columnindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_4] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN ARITH_TAC);;

let candle_q_packed_object_hessian6_index_row_5_tail = prove
 (`EL 5 (candle_q_packed_object_hessian6_index_row 5) = 20`,
  REWRITE_TAC[candle_q_packed_object_hessian6_index_row_5] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let candle_q_packed_object_hessian6_coordinate_index = prove
 (`!i. i < 21
       ==> EL (candle_q_packed_object_hessian6_col i)
              (candle_q_packed_object_hessian6_index_row
                (candle_q_packed_object_hessian6_row i)) = i`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i < 6` THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
                    candle_q_packed_object_hessian6_col_def] THEN
    MATCH_MP_TAC candle_q_packed_object_hessian6_index_row_0_tail THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 11` THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
                    candle_q_packed_object_hessian6_col_def] THEN
    MP_TAC (SPEC `i - 5`
      candle_q_packed_object_hessian6_index_row_1_tail) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 15` THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
                    candle_q_packed_object_hessian6_col_def] THEN
    MP_TAC (SPEC `i - 9`
      candle_q_packed_object_hessian6_index_row_2_tail) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 18` THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
                    candle_q_packed_object_hessian6_col_def] THEN
    MP_TAC (SPEC `i - 12`
      candle_q_packed_object_hessian6_index_row_3_tail) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 20` THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
                    candle_q_packed_object_hessian6_col_def] THEN
    MP_TAC (SPEC `i - 14`
      candle_q_packed_object_hessian6_index_row_4_tail) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `i = 20` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[candle_q_packed_object_hessian6_row_def;
                  candle_q_packed_object_hessian6_col_def;
                  candle_q_packed_object_hessian6_index_row_5_tail] THEN
      CONV_TAC NUM_REDUCE_CONV]] THEN
  MATCH_ACCEPT_TAC candle_q_packed_object_hessian6_index_row_5_tail);;

let candle_q_packed_object_hessian6_expand_row_lookup = prove
  (`!packed rowindex.
     LENGTH packed = 21 /\ rowindex < 6
     ==>
     candle_q_dim_interval_row_lookup rowindex
       (candle_q_packed_hessian6_expand packed) =
     MAP (\i. candle_q_interval_lookup i packed)
       (candle_q_packed_object_hessian6_index_row rowindex)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_interval_row_lookup rowindex
      (candle_q_packed_hessian6_expand packed) =
    EL rowindex (candle_q_packed_hessian6_expand packed)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_dim_interval_row_lookup_in_range THEN
    REWRITE_TAC[candle_q_packed_hessian6_expand_def; LENGTH] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < 21
        ==> candle_q_interval_lookup i packed = EL i packed`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
    (ARITH_RULE
      `rowindex < 6
       ==> rowindex = 0 \/ rowindex = 1 \/ rowindex = 2 \/
           rowindex = 3 \/ rowindex = 4 \/ rowindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[candle_q_packed_object_hessian6_index_row_0;
                  candle_q_packed_object_hessian6_index_row_1;
                  candle_q_packed_object_hessian6_index_row_2;
                  candle_q_packed_object_hessian6_index_row_3;
                  candle_q_packed_object_hessian6_index_row_4;
                  candle_q_packed_object_hessian6_index_row_5;
                  candle_q_packed_hessian6_expand_def; MAP] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  let lookup =
    ASSUME
      `!i. i < 21
           ==> candle_q_interval_lookup i packed = EL i packed` in
  let lookup_at n =
    let numeral = mk_small_numeral n in
    let bound =
      EQT_ELIM
        (NUM_REDUCE_CONV
          (mk_comb
            (mk_comb (`(<):num->num->bool`,numeral),`21`))) in
    MATCH_MP (SPEC numeral lookup) bound in
  MAP_EVERY ASSUME_TAC (map lookup_at (0--20)) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_hessian6_coordinate_index_lookup = prove
 (`!packed i.
     LENGTH packed = 21 /\ i < 21
     ==>
     candle_q_interval_lookup
       (candle_q_packed_object_hessian6_col i)
       (MAP (\k. candle_q_interval_lookup k packed)
         (candle_q_packed_object_hessian6_index_row
           (candle_q_packed_object_hessian6_row i))) =
     candle_q_interval_lookup i packed`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_packed_object_hessian6_col i <
    LENGTH (MAP (\k. candle_q_interval_lookup k packed)
      (candle_q_packed_object_hessian6_index_row
        (candle_q_packed_object_hessian6_row i)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_MAP;
                candle_q_packed_object_hessian6_index_row_length] THEN
    MP_TAC (SPEC `i:num`
      candle_q_packed_object_hessian6_coordinate_bounds) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_lookup
      (candle_q_packed_object_hessian6_col i)
      (MAP (\k. candle_q_interval_lookup k packed)
        (candle_q_packed_object_hessian6_index_row
          (candle_q_packed_object_hessian6_row i))) =
    EL (candle_q_packed_object_hessian6_col i)
      (MAP (\k. candle_q_interval_lookup k packed)
        (candle_q_packed_object_hessian6_index_row
          (candle_q_packed_object_hessian6_row i)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EL (candle_q_packed_object_hessian6_col i)
      (MAP (\k. candle_q_interval_lookup k packed)
        (candle_q_packed_object_hessian6_index_row
          (candle_q_packed_object_hessian6_row i))) =
    candle_q_interval_lookup
      (EL (candle_q_packed_object_hessian6_col i)
        (candle_q_packed_object_hessian6_index_row
          (candle_q_packed_object_hessian6_row i))) packed`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EL_MAP THEN
    REWRITE_TAC[candle_q_packed_object_hessian6_index_row_length] THEN
    MP_TAC (SPEC `i:num`
      candle_q_packed_object_hessian6_coordinate_bounds) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (SPEC `i:num`
    candle_q_packed_object_hessian6_coordinate_index) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let candle_q_packed_object_hessian6_coordinate_lookup = prove
 (`!packed i.
     LENGTH packed = 21 /\ i < 21
     ==>
     candle_q_interval_lookup i packed =
     candle_q_interval_lookup
       (candle_q_packed_object_hessian6_col i)
       (candle_q_dim_interval_row_lookup
         (candle_q_packed_object_hessian6_row i)
         (candle_q_packed_hessian6_expand packed))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_interval_row_lookup
      (candle_q_packed_object_hessian6_row i)
      (candle_q_packed_hessian6_expand packed) =
    MAP (\k. candle_q_interval_lookup k packed)
      (candle_q_packed_object_hessian6_index_row
        (candle_q_packed_object_hessian6_row i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_hessian6_expand_row_lookup THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC (SPEC `i:num`
      candle_q_packed_object_hessian6_coordinate_bounds) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  MATCH_MP_TAC candle_q_packed_object_hessian6_coordinate_index_lookup THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_analytic_hessian_lookup_contains = prove
 (`!value_bound gradient_bounds packed_hessian environment e i.
     LENGTH packed_hessian = 21 /\ i < 21 /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         value_bound gradient_bounds packed_hessian)
       environment e
     ==>
     candle_q_interval_contains
       (candle_q_interval_lookup i packed_hessian)
       (candle_analytic_dd
         (candle_q_packed_object_hessian6_row i)
         (candle_q_packed_object_hessian6_col i)
         environment e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_lookup i packed_hessian =
    candle_q_interval_lookup
      (candle_q_packed_object_hessian6_col i)
      (candle_q_dim_interval_row_lookup
        (candle_q_packed_object_hessian6_row i)
        (candle_q_packed_hessian6_expand packed_hessian))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_hessian6_coordinate_lookup THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`candle_q_packed_object_hessian6_row i`;
       `candle_q_packed_object_hessian6_col i`]
      (CONJUNCT2 (CONJUNCT2
        (REWRITE_RULE
          [candle_q_dim_analytic_contains_def;
           candle_q_dim_jet_contains_components_def]
          (ASSUME
            `candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                value_bound gradient_bounds packed_hessian)
              environment e`))))) THEN
  REWRITE_TAC[candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  ANTS_TAC THENL
   [MP_TAC (SPEC `i:num`
      candle_q_packed_object_hessian6_coordinate_bounds) THEN
    ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

let candle_q_packed_object_center_first_mul_contains = prove
 (`!left_value left_gradient left_e
       right_value right_gradient right_e environment.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     candle_q_packed_object_center_first_contains
       left_value left_gradient environment left_e /\
     candle_q_packed_object_center_first_contains
       right_value right_gradient environment right_e
     ==>
     candle_q_packed_object_center_first_contains
       (candle_q_interval_mul left_value right_value)
       (candle_q_packed_object_fused_scale_add
         right_value left_gradient left_value right_gradient)
       environment (Candle_analytic_mul left_e right_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_object_center_first_contains_def]) THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `candle_analytic_d i environment left_e *
        candle_analytic_value environment right_e +
      candle_analytic_value environment left_e *
        candle_analytic_d i environment right_e =
      candle_analytic_value environment right_e *
        candle_analytic_d i environment left_e +
      candle_analytic_value environment left_e *
        candle_analytic_d i environment right_e`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC
      candle_q_packed_object_fused_scale_add_component_sound THEN
    ASM_SIMP_TAC[]]);;

let candle_q_packed_object_symmetric_product_pairs6_def = new_definition
 `candle_q_packed_object_symmetric_product_pairs6 left right =
    list_of_seq
      (\i. candle_q_packed_object_symmetric_product_pair left right
        (candle_q_packed_object_hessian6_row i)
        (candle_q_packed_object_hessian6_col i)) 21`;;

let candle_q_packed_object_fused_hessian_def = new_definition
 `candle_q_packed_object_fused_hessian
      left_value right_value left_hessian right_hessian outer =
    MAP2
      (\left_entry right_outer.
         candle_q_packed_object_fused_hessian_entry
           left_value right_value left_entry
           (FST right_outer) (SND right_outer))
      left_hessian
      (MAP2 (\right_entry outer_entry. (right_entry,outer_entry))
        right_hessian outer)`;;

let candle_q_packed_object_mul_hessian6_def = new_definition
 `candle_q_packed_object_mul_hessian6
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian =
    candle_q_packed_object_fused_hessian
      left_value right_value left_hessian right_hessian
      (candle_q_packed_object_symmetric_product_pairs6
        left_gradient right_gradient)`;;

let candle_q_packed_object_symmetric_product_pairs6_length = prove
 (`!left right.
     LENGTH (candle_q_packed_object_symmetric_product_pairs6 left right) = 21`,
  REWRITE_TAC[candle_q_packed_object_symmetric_product_pairs6_def;
              LENGTH_LIST_OF_SEQ]);;

let candle_q_packed_hessian6_values_coordinates = prove
 (`!h:num->num->real.
     candle_q_packed_hessian6_values h =
     list_of_seq
       (\i. h (candle_q_packed_object_hessian6_row i)
              (candle_q_packed_object_hessian6_col i)) 21`,
  GEN_TAC THEN
  let numeral_conversions =
    map (fun n -> num_CONV (mk_small_numeral n)) (1--21) in
  REWRITE_TAC
    ([candle_q_packed_hessian6_values_def;
      candle_q_packed_object_hessian6_row_def;
      candle_q_packed_object_hessian6_col_def;
      list_of_seq; APPEND] @ numeral_conversions) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_mul_hessian6_length = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian.
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21
     ==>
     LENGTH (candle_q_packed_object_mul_hessian6
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian) = 21`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_mul_hessian6_def;
               candle_q_packed_object_fused_hessian_def;
               candle_q_packed_object_symmetric_product_pairs6_length;
               LENGTH_MAP2]);;

let candle_q_interval_list_eq_list_of_seq_lookup = prove
 (`!n items.
     LENGTH items = n
     ==>
     items = list_of_seq
       (\i. candle_q_interval_lookup i items) n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; candle_q_interval_lookup_in_range]);;

let candle_packed_object_list_eq_list_of_seq_el = prove
 (`!n (items:A list).
     LENGTH items = n
     ==> items = list_of_seq (\i. EL i items) n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let candle_q_packed_object_fused_hessian_lookup = prove
 (`!left_value right_value left_hessian right_hessian outer i.
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
     LENGTH outer = 21 /\ i < 21
     ==>
     candle_q_interval_lookup i
       (candle_q_packed_object_fused_hessian
         left_value right_value left_hessian right_hessian outer) =
     candle_q_packed_object_fused_hessian_entry
       left_value right_value
       (candle_q_interval_lookup i left_hessian)
       (candle_q_interval_lookup i right_hessian)
       (EL i outer)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_fused_hessian_def;
               LENGTH_MAP2; EL_MAP2;
               candle_q_interval_lookup_in_range]);;

let candle_q_packed_object_mul_hessian6_lookup = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian i.
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\ i < 21
     ==>
     candle_q_interval_lookup i
       (candle_q_packed_object_mul_hessian6
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian) =
     candle_q_packed_object_fused_hessian_entry
       left_value right_value
       (candle_q_interval_lookup i left_hessian)
       (candle_q_interval_lookup i right_hessian)
       (EL i (candle_q_packed_object_symmetric_product_pairs6
         left_gradient right_gradient))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_mul_hessian6_def] THEN
  MATCH_MP_TAC candle_q_packed_object_fused_hessian_lookup THEN
  ASM_REWRITE_TAC[candle_q_packed_object_symmetric_product_pairs6_length]);;

let candle_q_packed_object_hessian_lookup_contains = prove
 (`!packed (h:num->num->real) i.
     LENGTH packed = 21 /\
     candle_q_stack_contains packed
       (candle_q_packed_hessian6_values h) /\
     i < 21
     ==>
     candle_q_interval_contains
       (candle_q_interval_lookup i packed)
       (EL i (candle_q_packed_hessian6_values h))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_interval_lookup_in_range] THEN
  MATCH_MP_TAC candle_q_stack_contains_el_lt THEN
  ASM_REWRITE_TAC[]);;

let candle_real_packed_object_mul_hessian_def = new_definition
 `candle_real_packed_object_mul_hessian
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian i j =
    (((right_value * left_hessian i j +
       left_gradient i * right_gradient j) +
      right_gradient i * left_gradient j) +
     left_value * right_hessian i j)`;;

let candle_real_packed_object_mul_hessian_analytic = prove
 (`!left_e right_e environment i j.
     candle_real_packed_object_mul_hessian
       (candle_analytic_value environment left_e)
       (candle_analytic_value environment right_e)
       (\k. candle_analytic_d k environment left_e)
       (\k. candle_analytic_d k environment right_e)
       (\k l. candle_analytic_dd k l environment left_e)
       (\k l. candle_analytic_dd k l environment right_e) i j =
     candle_analytic_dd i j environment
       (Candle_analytic_mul left_e right_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_packed_object_mul_hessian_def;
              candle_analytic_dd_def] THEN
  CONV_TAC REAL_RING);;

let candle_q_packed_object_analytic_hessian_contains = prove
 (`!packed_hessian environment e i j.
     candle_q_stack_contains packed_hessian
       (candle_q_packed_hessian6_values
         (\k l. candle_analytic_dd k l environment e)) /\
     i < 6 /\ j < 6
     ==>
     candle_q_interval_contains
       (candle_q_interval_lookup j
         (candle_q_dim_interval_row_lookup i
           (candle_q_packed_hessian6_expand packed_hessian)))
       (candle_analytic_dd i j environment e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let expanded =
    MATCH_MP
      (SPECL
        [`packed_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `(\k l. candle_analytic_dd k l environment e):num->num->real`]
        candle_q_packed_hessian6_expand_contains_symmetric_values)
      (ASSUME
        `candle_q_stack_contains packed_hessian
          (candle_q_packed_hessian6_values
            (\k l. candle_analytic_dd k l environment e))`) in
  ASSUME_TAC
    (REWRITE_RULE[candle_q_symmetric_hessian6_analytic_values] expanded) THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (candle_q_dim_interval_row_lookup i
        (candle_q_packed_hessian6_expand packed_hessian))
      (list_of_seq (\l. candle_analytic_dd i l environment e) 6)`
  (LABEL_TAC "row_contains") THENL
   [SUBGOAL_THEN
     `candle_q_dim_interval_row_lookup i
        (candle_q_packed_hessian6_expand packed_hessian) =
      EL i (candle_q_packed_hessian6_expand packed_hessian)`
     SUBST1_TAC THENL
     [MATCH_MP_TAC candle_q_dim_interval_row_lookup_in_range THEN
      REWRITE_TAC[candle_q_packed_hessian6_expand_shape] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `list_of_seq (\l. candle_analytic_dd i l environment e) 6 =
      EL i
        (list_of_seq
          (\k. list_of_seq
            (\l. candle_analytic_dd k l environment e) 6) 6)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_LIST_OF_SEQ];
      ALL_TAC] THEN
    MATCH_MP_TAC candle_all2_el_lt THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC
      (CONJUNCT1
        (ISPEC
          `packed_hessian:
            (((num#num)#num)#((num#num)#num))list`
          candle_q_packed_hessian6_expand_shape)) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_dim_interval_row_lookup i
        (candle_q_packed_hessian6_expand packed_hessian)) = 6`
  ASSUME_TAC THENL
   [MP_TAC
      (MATCH_MP candle_all2_length
        (REWRITE_RULE[candle_q_stack_contains_all2]
          (ASSUME
            `candle_q_stack_contains
              (candle_q_dim_interval_row_lookup i
                (candle_q_packed_hessian6_expand packed_hessian))
              (list_of_seq
                (\l. candle_analytic_dd i l environment e) 6)`))) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_lookup j
      (candle_q_dim_interval_row_lookup i
        (candle_q_packed_hessian6_expand packed_hessian)) =
    EL j
      (candle_q_dim_interval_row_lookup i
        (candle_q_packed_hessian6_expand packed_hessian))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  let el_seq =
    MATCH_MP
      (ISPECL
        [`(\l. candle_analytic_dd i l environment e):num->real`;
         `j:num`; `6`]
        EL_LIST_OF_SEQ)
      (ASSUME `j < 6`) in
  let beta =
    BETA_CONV `(\l. candle_analytic_dd i l environment e) j` in
  let el_value = TRANS el_seq beta in
  GEN_REWRITE_TAC RAND_CONV [GSYM el_value] THEN
  MATCH_MP_TAC candle_q_stack_contains_el_lt THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_mul_hessian6_sound = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian
       left_value_real right_value_real
       (left_gradient_real:num->real) (right_gradient_real:num->real)
       (left_hessian_real:num->num->real)
       (right_hessian_real:num->num->real).
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
     candle_q_interval_contains left_value left_value_real /\
     candle_q_interval_contains right_value right_value_real /\
     (!i. i < 6
          ==> candle_q_interval_contains
                (candle_q_interval_lookup i left_gradient)
                (left_gradient_real i)) /\
     (!i. i < 6
          ==> candle_q_interval_contains
                (candle_q_interval_lookup i right_gradient)
                (right_gradient_real i)) /\
     (!i. i < 21
          ==> candle_q_interval_contains
                (candle_q_interval_lookup i left_hessian)
                (left_hessian_real
                  (candle_q_packed_object_hessian6_row i)
                  (candle_q_packed_object_hessian6_col i))) /\
     (!i. i < 21
          ==> candle_q_interval_contains
                (candle_q_interval_lookup i right_hessian)
                (right_hessian_real
                  (candle_q_packed_object_hessian6_row i)
                  (candle_q_packed_object_hessian6_col i)))
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_mul_hessian6
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian)
       (candle_q_packed_hessian6_values
         (candle_real_packed_object_mul_hessian
           left_value_real right_value_real
           left_gradient_real right_gradient_real
           left_hessian_real right_hessian_real))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_packed_object_mul_hessian6
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian =
    list_of_seq
      (\i. candle_q_interval_lookup i
        (candle_q_packed_object_mul_hessian6
          left_value right_value left_gradient right_gradient
          left_hessian right_hessian)) 21`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_interval_list_eq_list_of_seq_lookup THEN
    MATCH_MP_TAC candle_q_packed_object_mul_hessian6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  ONCE_REWRITE_TAC[candle_q_packed_hessian6_values_coordinates] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_mul_hessian6_lookup;
               candle_q_packed_object_symmetric_product_pairs6_def;
               EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[
              candle_q_packed_object_symmetric_product_pair_def;
              candle_real_packed_object_mul_hessian_def] THEN
  MATCH_MP_TAC candle_q_packed_object_fused_hessian_entry_sound THEN
  ASM_SIMP_TAC[candle_q_packed_object_hessian6_coordinate_bounds]);;

let candle_q_packed_object_box_mul_contains = prove
 (`!left_value left_gradient left_hessian left_e
       right_value right_gradient right_hessian right_e environment.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         left_value left_gradient left_hessian) environment left_e /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         right_value right_gradient right_hessian) environment right_e
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         (candle_q_interval_mul left_value right_value)
         (candle_q_packed_object_fused_scale_add
           right_value left_gradient left_value right_gradient)
         (candle_q_packed_object_mul_hessian6
           left_value right_value left_gradient right_gradient
           left_hessian right_hessian))
       environment (Candle_analytic_mul left_e right_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let left_components =
    REWRITE_RULE
      [candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_at_def;
       candle_q_dim_jet_hessian_at_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_hessian_def;
       candle_q_dim_jet_make_def; FST; SND]
      (ASSUME
        `candle_q_dim_analytic_contains 6
          (candle_q_packed_object_box_jet
            left_value left_gradient left_hessian) environment left_e`) in
  let right_components =
    REWRITE_RULE
      [candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_at_def;
       candle_q_dim_jet_hessian_at_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_hessian_def;
       candle_q_dim_jet_make_def; FST; SND]
      (ASSUME
        `candle_q_dim_analytic_contains 6
          (candle_q_packed_object_box_jet
            right_value right_gradient right_hessian) environment right_e`) in
  let left_value_contains,left_derivatives = CONJ_PAIR left_components in
  let left_gradient_contains,left_hessian_contains =
    CONJ_PAIR left_derivatives in
  let right_value_contains,right_derivatives = CONJ_PAIR right_components in
  let right_gradient_contains,right_hessian_contains =
    CONJ_PAIR right_derivatives in
  MAP_EVERY ASSUME_TAC
    [left_value_contains; left_gradient_contains; left_hessian_contains;
     right_value_contains; right_gradient_contains;
     right_hessian_contains] THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (candle_q_packed_object_mul_hessian6
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian)
      (candle_q_packed_hessian6_values
        (\i j. candle_analytic_dd i j environment
          (Candle_analytic_mul left_e right_e)))`
  (LABEL_TAC "output_hessian_contains") THENL
   [MP_TAC
      (SPECL
        [`left_value:((num#num)#num)#((num#num)#num)`;
         `right_value:((num#num)#num)#((num#num)#num)`;
         `left_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `right_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `left_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `right_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `candle_analytic_value environment left_e`;
         `candle_analytic_value environment right_e`;
         `(\i. candle_analytic_d i environment left_e):num->real`;
         `(\i. candle_analytic_d i environment right_e):num->real`;
         `(\i j. candle_analytic_dd i j environment left_e):
            num->num->real`;
         `(\i j. candle_analytic_dd i j environment right_e):
            num->num->real`]
        candle_q_packed_object_mul_hessian6_sound) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        BETA_TAC THEN
        MATCH_MP_TAC
          (SPECL
            [`left_value:((num#num)#num)#((num#num)#num)`;
             `left_gradient:
                (((num#num)#num)#((num#num)#num))list`;
             `left_hessian:
                (((num#num)#num)#((num#num)#num))list`;
             `environment:real list`; `left_e:candle_analytic_expr`; `k:num`]
            candle_q_packed_object_analytic_hessian_lookup_contains) THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        BETA_TAC THEN
        MATCH_MP_TAC
          (SPECL
            [`right_value:((num#num)#num)#((num#num)#num)`;
             `right_gradient:
                (((num#num)#num)#((num#num)#num))list`;
             `right_hessian:
                (((num#num)#num)#((num#num)#num))list`;
             `environment:real list`; `right_e:candle_analytic_expr`; `k:num`]
            candle_q_packed_object_analytic_hessian_lookup_contains) THEN
        ASM_REWRITE_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN
       `(\i j. candle_analytic_dd i j environment
          (Candle_analytic_mul left_e right_e)) =
        (candle_real_packed_object_mul_hessian
          (candle_analytic_value environment left_e)
          (candle_analytic_value environment right_e)
          (\i. candle_analytic_d i environment left_e)
          (\i. candle_analytic_d i environment right_e)
          (\i j. candle_analytic_dd i j environment left_e)
          (\i j. candle_analytic_dd i j environment right_e))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_real_packed_object_mul_hessian_analytic];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def; FST; SND] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `candle_analytic_d i environment left_e *
        candle_analytic_value environment right_e +
      candle_analytic_value environment left_e *
        candle_analytic_d i environment right_e =
      candle_analytic_value environment right_e *
        candle_analytic_d i environment left_e +
      candle_analytic_value environment left_e *
        candle_analytic_d i environment right_e`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC
      candle_q_packed_object_fused_scale_add_component_sound THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_object_analytic_hessian_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_center_all_mul_contains = prove
 (`!center_boxes
       left_value left_gradient left_e
       right_value right_gradient right_e.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment left_e /\
            candle_q_packed_object_center_first_contains
              left_value left_gradient environment left_e) /\
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment right_e /\
            candle_q_packed_object_center_first_contains
              right_value right_gradient environment right_e)
     ==>
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment
              (Candle_analytic_mul left_e right_e) /\
            candle_q_packed_object_center_first_contains
              (candle_q_interval_mul left_value right_value)
              (candle_q_packed_object_fused_scale_add
                right_value left_gradient left_value right_gradient)
              environment (Candle_analytic_mul left_e right_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
  let left_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains center_boxes environment
             ==> candle_analytic_regular_at environment left_e /\
                 candle_q_packed_object_center_first_contains
                   left_value left_gradient environment left_e`))
      (ASSUME `candle_q_stack_contains center_boxes environment`) in
  let right_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains center_boxes environment
             ==> candle_analytic_regular_at environment right_e /\
                 candle_q_packed_object_center_first_contains
                   right_value right_gradient environment right_e`))
      (ASSUME `candle_q_stack_contains center_boxes environment`) in
  let left_regular,left_contains = CONJ_PAIR left_at in
  let right_regular,right_contains = CONJ_PAIR right_at in
  MAP_EVERY ASSUME_TAC
    [left_regular; left_contains; right_regular; right_contains] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
    MATCH_MP_TAC candle_q_packed_object_center_first_mul_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_all_mul_contains = prove
 (`!outer_boxes
       left_value left_gradient left_hessian left_e
       right_value right_gradient right_hessian right_e.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment left_e /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                left_value left_gradient left_hessian)
              environment left_e) /\
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment right_e /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                right_value right_gradient right_hessian)
              environment right_e)
     ==>
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment
              (Candle_analytic_mul left_e right_e) /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                (candle_q_interval_mul left_value right_value)
                (candle_q_packed_object_fused_scale_add
                  right_value left_gradient left_value right_gradient)
                (candle_q_packed_object_mul_hessian6
                  left_value right_value left_gradient right_gradient
                  left_hessian right_hessian))
              environment (Candle_analytic_mul left_e right_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
  let left_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains outer_boxes environment
             ==> candle_analytic_regular_at environment left_e /\
                 candle_q_dim_analytic_contains 6
                   (candle_q_packed_object_box_jet
                     left_value left_gradient left_hessian)
                   environment left_e`))
      (ASSUME `candle_q_stack_contains outer_boxes environment`) in
  let right_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains outer_boxes environment
             ==> candle_analytic_regular_at environment right_e /\
                 candle_q_dim_analytic_contains 6
                   (candle_q_packed_object_box_jet
                     right_value right_gradient right_hessian)
                   environment right_e`))
      (ASSUME `candle_q_stack_contains outer_boxes environment`) in
  let left_regular,left_contains = CONJ_PAIR left_at in
  let right_regular,right_contains = CONJ_PAIR right_at in
  MAP_EVERY ASSUME_TAC
    [left_regular; left_contains; right_regular; right_contains] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
    MATCH_MP_TAC candle_q_packed_object_box_mul_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_mul_shape = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_box_jet
         (candle_q_interval_mul left_value right_value)
         (candle_q_packed_object_fused_scale_add
           right_value left_gradient left_value right_gradient)
         (candle_q_packed_object_mul_hessian6
           left_value right_value left_gradient right_gradient
           left_hessian right_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  CONJ_TAC THENL
   [MP_TAC
      (SPECL
        [`right_value:((num#num)#num)#((num#num)#num)`;
         `left_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `left_value:((num#num)#num)#((num#num)#num)`;
         `right_gradient:
            (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_fused_scale_add_length) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_packed_hessian6_expand_shape]]);;

let candle_q_packed_object_item_mul_raw_analytic_invariant = prove
 (`!center_boxes outer_boxes
       left_domain left_center_value left_center_gradient
       left_value_bound left_gradient_bounds left_hessian
       left_center_e left_box_e
       right_domain right_center_value right_center_gradient
       right_value_bound right_gradient_bounds right_hessian
       right_center_e right_box_e.
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes left_domain
       left_center_value left_center_gradient
       left_value_bound left_gradient_bounds left_hessian
       left_center_e left_box_e /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes right_domain
       right_center_value right_center_gradient
       right_value_bound right_gradient_bounds right_hessian
       right_center_e right_box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes (left_domain /\ right_domain)
       (candle_q_interval_mul left_center_value right_center_value)
       (candle_q_packed_object_fused_scale_add
         right_center_value left_center_gradient
         left_center_value right_center_gradient)
       (candle_q_interval_mul left_value_bound right_value_bound)
       (candle_q_packed_object_fused_scale_add
         right_value_bound left_gradient_bounds
         left_value_bound right_gradient_bounds)
       (candle_q_packed_object_mul_hessian6
         left_value_bound right_value_bound
         left_gradient_bounds right_gradient_bounds
         left_hessian right_hessian)
       (Candle_analytic_mul left_center_e right_center_e)
       (Candle_analytic_mul left_box_e right_box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_hessian_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "right_hessian_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "left_invariant")
          (LABEL_TAC "right_invariant")))) THEN
  USE_THEN "left_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "left_erasure")
        (LABEL_TAC "left_domain_all"))) THEN
  USE_THEN "right_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "right_valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "right_erasure")
        (LABEL_TAC "right_domain_all"))) THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def;
              candle_analytic_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  let domains = ASSUME `left_domain /\ right_domain` in
  let left_true,right_true = CONJ_PAIR domains in
  MP_TAC (MATCH_MP
    (ASSUME
      `left_domain
       ==> LENGTH left_center_gradient = 6 /\
           candle_q_dim_jet_shape 6
             (candle_q_packed_object_box_jet
               left_value_bound left_gradient_bounds left_hessian) /\
           (!environment.
              candle_q_stack_contains center_boxes environment
              ==> candle_analytic_regular_at environment left_center_e /\
                  candle_q_packed_object_center_first_contains
                    left_center_value left_center_gradient
                    environment left_center_e) /\
           (!environment.
              candle_q_stack_contains outer_boxes environment
              ==> candle_analytic_regular_at environment left_box_e /\
                  candle_q_dim_analytic_contains 6
                    (candle_q_packed_object_box_jet
                      left_value_bound left_gradient_bounds left_hessian)
                    environment left_box_e)`)
    left_true) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "left_box_shape")
        (CONJUNCTS_THEN2 (LABEL_TAC "left_center_all")
          (LABEL_TAC "left_box_all")))) THEN
  MP_TAC (MATCH_MP
    (ASSUME
      `right_domain
       ==> LENGTH right_center_gradient = 6 /\
           candle_q_dim_jet_shape 6
             (candle_q_packed_object_box_jet
               right_value_bound right_gradient_bounds right_hessian) /\
           (!environment.
              candle_q_stack_contains center_boxes environment
              ==> candle_analytic_regular_at environment right_center_e /\
                  candle_q_packed_object_center_first_contains
                    right_center_value right_center_gradient
                    environment right_center_e) /\
           (!environment.
              candle_q_stack_contains outer_boxes environment
              ==> candle_analytic_regular_at environment right_box_e /\
                  candle_q_dim_analytic_contains 6
                    (candle_q_packed_object_box_jet
                      right_value_bound right_gradient_bounds right_hessian)
                    environment right_box_e)`)
    right_true) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "right_center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "right_box_shape")
        (CONJUNCTS_THEN2 (LABEL_TAC "right_center_all")
          (LABEL_TAC "right_box_all")))) THEN
  SUBGOAL_THEN `LENGTH
      (left_gradient_bounds:
        (((num#num)#num)#((num#num)#num))list) = 6`
   (LABEL_TAC "left_box_gradient_length") THENL
   [USE_THEN "left_box_shape" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH
      (right_gradient_bounds:
        (((num#num)#num)#((num#num)#num))list) = 6`
   (LABEL_TAC "right_box_gradient_length") THENL
   [USE_THEN "right_box_shape" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
      (SPECL
        [`right_center_value:((num#num)#num)#((num#num)#num)`;
         `left_center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `left_center_value:((num#num)#num)#((num#num)#num)`;
         `right_center_gradient:
            (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_fused_scale_add_length) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_box_mul_shape THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_center_all_mul_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_box_all_mul_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_mul_analytic_invariant = prove
 (`!center_boxes outer_boxes radii
       left_domain left_center_value left_center_gradient
       left_value_bound left_gradient_bounds left_hessian
       left_center_e left_box_e
       right_domain right_center_value right_center_gradient
       right_value_bound right_gradient_bounds right_hessian
       right_center_e right_box_e.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21 /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes left_domain
       left_center_value left_center_gradient
       left_value_bound left_gradient_bounds left_hessian
       left_center_e left_box_e /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes right_domain
       right_center_value right_center_gradient
       right_value_bound right_gradient_bounds right_hessian
       right_center_e right_box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes (left_domain /\ right_domain)
       (candle_q_interval_mul left_center_value right_center_value)
       (candle_q_packed_object_fused_scale_add
         right_center_value left_center_gradient
         left_center_value right_center_gradient)
       (candle_q_packed_object_value_bound6 radii
         (candle_q_interval_mul left_center_value right_center_value)
         (candle_q_packed_object_fused_scale_add
           right_center_value left_center_gradient
           left_center_value right_center_gradient)
         (candle_q_packed_object_mul_hessian6
           left_value_bound right_value_bound
           left_gradient_bounds right_gradient_bounds
           left_hessian right_hessian))
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_packed_object_fused_scale_add
           right_center_value left_center_gradient
           left_center_value right_center_gradient)
         (candle_q_packed_object_mul_hessian6
           left_value_bound right_value_bound
           left_gradient_bounds right_gradient_bounds
           left_hessian right_hessian))
       (candle_q_packed_object_mul_hessian6
         left_value_bound right_value_bound
         left_gradient_bounds right_gradient_bounds
         left_hessian right_hessian)
       (Candle_analytic_mul left_center_e right_center_e)
       (Candle_analytic_mul left_box_e right_box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       `left_domain /\ right_domain`;
       `candle_q_interval_mul left_center_value right_center_value`;
       `candle_q_packed_object_fused_scale_add
          right_center_value left_center_gradient
          left_center_value right_center_gradient`;
       `candle_q_interval_mul left_value_bound right_value_bound`;
       `candle_q_packed_object_fused_scale_add
          right_value_bound left_gradient_bounds
          left_value_bound right_gradient_bounds`;
       `candle_q_packed_object_mul_hessian6
          left_value_bound right_value_bound
          left_gradient_bounds right_gradient_bounds
          left_hessian right_hessian`;
       `Candle_analytic_mul left_center_e right_center_e`;
       `Candle_analytic_mul left_box_e right_box_e`]
      candle_q_packed_object_item_recomplete_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_packed_object_item_mul_raw_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_products_sum2_sound;
     candle_q_packed_object_products_sum4_sound;
     candle_q_packed_object_fused_scale_add_lookup;
     candle_q_packed_object_fused_scale_add_component_sound;
     candle_q_packed_object_fused_scale_add_length;
     candle_q_packed_object_fused_hessian_entry_sound;
     candle_q_packed_object_symmetric_product_pair_sound;
     candle_q_packed_object_hessian6_coordinate_bounds;
     candle_q_packed_object_hessian6_index_row_0;
     candle_q_packed_object_hessian6_index_row_1;
     candle_q_packed_object_hessian6_index_row_2;
     candle_q_packed_object_hessian6_index_row_3;
     candle_q_packed_object_hessian6_index_row_4;
     candle_q_packed_object_hessian6_index_row_5;
     candle_q_packed_object_hessian6_index_row_length;
     candle_q_packed_object_hessian6_index_row_0_tail;
     candle_q_packed_object_hessian6_index_row_1_tail;
     candle_q_packed_object_hessian6_index_row_2_tail;
     candle_q_packed_object_hessian6_index_row_3_tail;
     candle_q_packed_object_hessian6_index_row_4_tail;
     candle_q_packed_object_hessian6_index_row_5_tail;
     candle_q_packed_object_hessian6_coordinate_index;
     candle_q_packed_object_hessian6_expand_row_lookup;
     candle_q_packed_object_hessian6_coordinate_index_lookup;
     candle_q_packed_object_hessian6_coordinate_lookup;
     candle_q_packed_object_symmetric_product_pairs6_length;
     candle_q_packed_hessian6_values_coordinates;
     candle_q_packed_object_mul_hessian6_length;
     candle_q_interval_list_eq_list_of_seq_lookup;
     candle_packed_object_list_eq_list_of_seq_el;
     candle_q_packed_object_fused_hessian_lookup;
     candle_q_packed_object_mul_hessian6_lookup;
     candle_q_packed_object_hessian_lookup_contains;
     candle_q_packed_object_analytic_hessian_lookup_contains;
     candle_q_packed_object_center_first_mul_contains;
     candle_real_packed_object_mul_hessian_analytic;
     candle_q_packed_object_analytic_hessian_contains;
     candle_q_packed_object_mul_hessian6_sound;
     candle_q_packed_object_box_mul_contains;
     candle_q_packed_object_center_all_mul_contains;
     candle_q_packed_object_box_all_mul_contains;
     candle_q_packed_object_box_mul_shape;
     candle_q_packed_object_item_mul_raw_analytic_invariant;
     candle_q_packed_object_item_mul_analytic_invariant] then
  failwith "packed source object mul sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_MUL_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
