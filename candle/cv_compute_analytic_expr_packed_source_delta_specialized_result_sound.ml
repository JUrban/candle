(* ========================================================================== *)
(* Ordinary-HOL analytic results for the six authenticated delta shortcuts.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the semantic side of the prepared     *)
(* instruction bridge.  It packages the already-proved optimized jets into   *)
(* the ordinary centered Taylor-model result invariant used by program        *)
(* induction.  Source recognition remains exact: the following dispatcher    *)
(* layer may select these results only for the corresponding compiled         *)
(* polynomial instruction.                                                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_product_jet_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_compile_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_jet_sound;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_jet_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;

let candle_q_six_list_lookup = prove
 (`!items:A list.
     LENGTH items = 6
     ==>
     items =
       [EL 0 items; EL 1 items; EL 2 items;
        EL 3 items; EL 4 items; EL 5 items]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `items = list_of_seq (\lookup_index. EL lookup_index (items:A list)) 6`
   MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM LENGTH_EQ_LIST_OF_SEQ];
    REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`;
                num_CONV `3`; num_CONV `2`; num_CONV `1`;
                list_of_seq; APPEND]]);;

let candle_q_six_real_lookup_list = prove
  (`!items:real list.
     LENGTH items = 6
     ==>
     items =
       [candle_q_real_lookup 0 items; candle_q_real_lookup 1 items;
        candle_q_real_lookup 2 items; candle_q_real_lookup 3 items;
        candle_q_real_lookup 4 items; candle_q_real_lookup 5 items]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_real_lookup 0 items = EL 0 items /\
    candle_q_real_lookup 1 items = EL 1 items /\
    candle_q_real_lookup 2 items = EL 2 items /\
    candle_q_real_lookup 3 items = EL 3 items /\
    candle_q_real_lookup 4 items = EL 4 items /\
    candle_q_real_lookup 5 items = EL 5 items`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    MATCH_MP_TAC candle_q_real_lookup_in_range THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_six_list_lookup THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_delta_neg_derivative_jet_environment_def = new_definition
 `candle_q_packed_delta_neg_derivative_jet_environment coordinate environment =
    candle_q_packed_delta_neg_derivative_jet_six coordinate
      (candle_q_interval_lookup 0 environment)
      (candle_q_interval_lookup 1 environment)
      (candle_q_interval_lookup 2 environment)
      (candle_q_interval_lookup 3 environment)
      (candle_q_interval_lookup 4 environment)
      (candle_q_interval_lookup 5 environment)`;;

let candle_q_packed_delta_product_jet_environment_def = new_definition
 `candle_q_packed_delta_product_jet_environment coordinate environment =
    candle_q_packed_delta_product_jet_six coordinate
      (candle_q_interval_lookup 0 environment)
      (candle_q_interval_lookup 1 environment)
      (candle_q_interval_lookup 2 environment)
      (candle_q_interval_lookup 3 environment)
      (candle_q_interval_lookup 4 environment)
      (candle_q_interval_lookup 5 environment)`;;

let candle_q_packed_delta_neg_derivative_jet_environment_shape = prove
 (`!coordinate environment.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_delta_neg_derivative_jet_environment
         coordinate environment)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_jet_environment_def] THEN
  MATCH_MP_TAC candle_q_packed_delta_neg_derivative_jet_six_shape THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_delta_product_jet_environment_shape = prove
 (`!coordinate environment.
     candle_q_dim_jet_shape 6
       (candle_q_packed_delta_product_jet_environment
         coordinate environment)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_product_jet_environment_def] THEN
  MATCH_ACCEPT_TAC candle_q_packed_delta_product_jet_six_shape);;

let candle_q_packed_delta_neg_derivative_jet_environment_contains = prove
 (`!interval_environment real_environment coordinate.
     LENGTH real_environment = 6 /\
     candle_q_stack_contains interval_environment real_environment /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_delta_neg_derivative_jet_environment
         coordinate interval_environment)
       real_environment
       (candle_packed_delta_neg_derivative_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let contains index =
    MATCH_MP
      (SPECL
        [mk_small_numeral index;
         `interval_environment:
            ((((num#num)#num)#((num#num)#num))list)`;
         `real_environment:real list`]
        candle_q_stack_lookup_contains)
      (ASSUME
        `candle_q_stack_contains
          (interval_environment:
            ((((num#num)#num)#((num#num)#num))list))
          (real_environment:real list)`) in
  let real_environment_six =
    MATCH_MP
      (ISPEC `real_environment:real list`
        candle_q_six_real_lookup_list)
      (ASSUME `LENGTH (real_environment:real list) = 6`) in
  ONCE_REWRITE_TAC[real_environment_six] THEN
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_jet_environment_def] THEN
  MATCH_MP_TAC
    candle_q_packed_delta_neg_derivative_jet_six_analytic_contains THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC (contains 0); ACCEPT_TAC (contains 1);
    ACCEPT_TAC (contains 2); ACCEPT_TAC (contains 3);
    ACCEPT_TAC (contains 4); ACCEPT_TAC (contains 5);
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_delta_product_jet_environment_contains = prove
 (`!interval_environment real_environment coordinate.
     LENGTH real_environment = 6 /\
     candle_q_stack_contains interval_environment real_environment /\
     coordinate < 6
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_delta_product_jet_environment
         coordinate interval_environment)
       real_environment
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let contains index =
    MATCH_MP
      (SPECL
        [mk_small_numeral index;
         `interval_environment:
            ((((num#num)#num)#((num#num)#num))list)`;
         `real_environment:real list`]
        candle_q_stack_lookup_contains)
      (ASSUME
        `candle_q_stack_contains
          (interval_environment:
            ((((num#num)#num)#((num#num)#num))list))
          (real_environment:real list)`) in
  let real_environment_six =
    MATCH_MP
      (ISPEC `real_environment:real list`
        candle_q_six_real_lookup_list)
      (ASSUME `LENGTH (real_environment:real list) = 6`) in
  ONCE_REWRITE_TAC[real_environment_six] THEN
  REWRITE_TAC[candle_q_packed_delta_product_jet_environment_def] THEN
  MATCH_MP_TAC candle_q_packed_delta_product_jet_six_analytic_contains THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC (contains 0); ACCEPT_TAC (contains 1);
    ACCEPT_TAC (contains 2); ACCEPT_TAC (contains 3);
    ACCEPT_TAC (contains 4); ACCEPT_TAC (contains 5);
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_delta_neg_derivative_result_def = new_definition
 `candle_q_packed_delta_neg_derivative_result boxes coordinate =
    let center_jet =
      candle_q_packed_delta_neg_derivative_jet_environment coordinate
        (candle_q_center_environment_list boxes) in
    let box_jet =
      candle_q_packed_delta_neg_derivative_jet_environment coordinate boxes in
    candle_q_dim_taylor_model_result_complete
      (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
      T center_jet (candle_q_dim_jet_hessian box_jet)`;;

let candle_q_packed_delta_product_result_def = new_definition
 `candle_q_packed_delta_product_result boxes coordinate =
    let center_jet =
      candle_q_packed_delta_product_jet_environment coordinate
        (candle_q_center_environment_list boxes) in
    let box_jet =
      candle_q_packed_delta_product_jet_environment coordinate boxes in
    candle_q_dim_taylor_model_result_complete
      (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
      T center_jet (candle_q_dim_jet_hessian box_jet)`;;

let candle_q_packed_delta_neg_derivative_result_analytic_invariant = prove
 (`!boxes coordinate.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       (ARB:real^6) boxes
       (candle_q_packed_delta_neg_derivative_result boxes coordinate)
       (candle_packed_delta_neg_derivative_expr coordinate)
       (candle_packed_delta_neg_derivative_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let coordinate_cases =
    ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` in
  let coordinate_lt =
    MATCH_MP
      (ARITH_RULE
        `(coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
         ==> coordinate < 6`)
      coordinate_cases in
  let boxes_length =
    ASSUME
      `LENGTH
        (boxes:((((num#num)#num)#((num#num)#num))list)) = 6` in
  let boxes_valid =
    ASSUME
      `candle_q_box_valid_list
        (boxes:((((num#num)#num)#((num#num)#num))list))` in
  let analytic_valid =
    let polynomial_valid =
      MATCH_MP
        (SPEC `coordinate:num`
          candle_packed_delta_neg_derivative_poly_valid)
        coordinate_lt in
    let valid_equivalence =
      prove
       (`candle_analytic_valid_dim 6
           (candle_packed_delta_neg_derivative_expr coordinate) <=>
         candle_poly_valid_dim 6
           (Candle_poly_neg
             (candle_poly_diff coordinate candle_packed_delta_poly))`,
        REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                    candle_analytic_valid_dim_def]) in
    EQ_MP (SYM valid_equivalence) polynomial_valid in
  let erasure_equal =
    REFL
      `candle_analytic_erase_sqrt_certificates
        (candle_packed_delta_neg_derivative_expr coordinate)` in
  let center_regular =
    prove
     (`candle_analytic_regular_at
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)
         (candle_packed_delta_neg_derivative_expr coordinate)`,
      REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                  candle_analytic_regular_at_def]) in
  let box_regular =
    prove
     (`!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. p$(k + 1)) 6)
              (candle_packed_delta_neg_derivative_expr coordinate)`,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                  candle_analytic_regular_at_def]) in
  let center_shape =
    MATCH_MP
      (SPECL
        [`coordinate:num`;
         `candle_q_center_environment_list boxes`]
        candle_q_packed_delta_neg_derivative_jet_environment_shape)
      coordinate_cases in
  let center_environment_contains =
    let rule =
      CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
        (ISPEC
          `boxes:((((num#num)#num)#((num#num)#num))list)`
          (INST_TYPE [`:6`,`:N`]
            candle_q_center_environment_vector_contains)) in
    MATCH_MP rule boxes_length in
  let center_values_length =
    ISPECL
      [`(\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))`;
       `6`]
      LENGTH_LIST_OF_SEQ in
  let center_contains =
    MATCH_MP
      (SPECL
        [`candle_q_center_environment_list boxes`;
         `list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6`;
         `coordinate:num`]
        candle_q_packed_delta_neg_derivative_jet_environment_contains)
      (CONJ center_values_length
        (CONJ center_environment_contains coordinate_cases)) in
  let box_shape =
    MATCH_MP
      (SPECL
        [`coordinate:num`;
         `boxes:((((num#num)#num)#((num#num)#num))list)`]
        candle_q_packed_delta_neg_derivative_jet_environment_shape)
      coordinate_cases in
  let box_contains =
    let p = `p:real^6` in
    let p_in_box =
      `(p:real^6) IN interval
        [candle_q_box_lower_vector boxes,
         candle_q_box_upper_vector boxes]` in
    let values_length =
      ISPECL [`(\k. (p:real^6)$(k + 1))`; `6`]
        LENGTH_LIST_OF_SEQ in
    let environment_contains =
      let rule =
        CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
          (ISPECL
            [`boxes:((((num#num)#num)#((num#num)#num))list)`;
             `p:real^6`]
            (INST_TYPE [`:6`,`:N`]
              candle_q_box_stack_contains_vector)) in
      MATCH_MP rule (CONJ boxes_length (ASSUME p_in_box)) in
    let contains_at_p =
      MATCH_MP
        (SPECL
          [`boxes:((((num#num)#num)#((num#num)#num))list)`;
           `list_of_seq (\k. (p:real^6)$(k + 1)) 6`;
           `coordinate:num`]
          candle_q_packed_delta_neg_derivative_jet_environment_contains)
        (CONJ values_length
          (CONJ environment_contains coordinate_cases)) in
    GEN p (DISCH p_in_box contains_at_p) in
  let domain_components =
    end_itlist CONJ
      [center_regular; box_regular; center_shape; center_contains;
       box_shape; box_contains] in
  let complete_rule =
    CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
      (ISPECL
        [`candle_packed_delta_neg_derivative_expr coordinate`;
         `candle_packed_delta_neg_derivative_expr coordinate`;
         `boxes:((((num#num)#num)#((num#num)#num))list)`;
         `T`;
         `candle_q_packed_delta_neg_derivative_jet_environment coordinate
            (candle_q_center_environment_list boxes)`;
         `candle_q_packed_delta_neg_derivative_jet_environment coordinate
            boxes`;
         `ARB:real^6`]
        (INST_TYPE [`:6`,`:N`]
          candle_q_dim_taylor_model_complete_analytic_invariant)) in
  let complete_premises =
    end_itlist CONJ
      [analytic_valid; erasure_equal; boxes_length; boxes_valid;
       DISCH `T` domain_components] in
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_result_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC (MATCH_MP complete_rule complete_premises));;

let candle_q_packed_delta_product_result_analytic_invariant = prove
 (`!boxes coordinate.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     coordinate < 3
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       (ARB:real^6) boxes
       (candle_q_packed_delta_product_result boxes coordinate)
       (candle_packed_delta_product_expr coordinate)
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let coordinate_lt =
    ASSUME `(coordinate:num) < 3` in
  let coordinate_lt_six =
    MATCH_MP
      (ARITH_RULE `(coordinate:num) < 3 ==> coordinate < 6`)
      coordinate_lt in
  let boxes_length =
    ASSUME
      `LENGTH
        (boxes:((((num#num)#num)#((num#num)#num))list)) = 6` in
  let boxes_valid =
    ASSUME
      `candle_q_box_valid_list
        (boxes:((((num#num)#num)#((num#num)#num))list))` in
  let analytic_valid_rule =
    prove
     (`!coordinate.
        coordinate < 6
        ==>
        candle_analytic_valid_dim 6
          (candle_packed_delta_product_expr coordinate)`,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[candle_packed_delta_product_expr_def;
                  candle_packed_four_expr_def;
                  candle_packed_coordinate_expr_def;
                  candle_packed_delta_expr_def;
                  candle_analytic_valid_dim_def;
                  candle_poly_valid_dim_def;
                  candle_packed_delta_poly_valid] THEN
      ASM_REWRITE_TAC[]) in
  let analytic_valid =
    MATCH_MP (SPEC `coordinate:num` analytic_valid_rule)
      coordinate_lt_six in
  let erasure_equal =
    REFL
      `candle_analytic_erase_sqrt_certificates
        (candle_packed_delta_product_expr coordinate)` in
  let center_regular =
    prove
     (`candle_analytic_regular_at
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)
         (candle_packed_delta_product_expr coordinate)`,
      REWRITE_TAC[candle_packed_delta_product_expr_def;
                  candle_packed_four_expr_def;
                  candle_packed_coordinate_expr_def;
                  candle_packed_delta_expr_def;
                  candle_analytic_regular_at_def]) in
  let box_regular =
    prove
     (`!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. p$(k + 1)) 6)
              (candle_packed_delta_product_expr coordinate)`,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[candle_packed_delta_product_expr_def;
                  candle_packed_four_expr_def;
                  candle_packed_coordinate_expr_def;
                  candle_packed_delta_expr_def;
                  candle_analytic_regular_at_def]) in
  let center_shape =
    SPECL
      [`coordinate:num`; `candle_q_center_environment_list boxes`]
      candle_q_packed_delta_product_jet_environment_shape in
  let center_environment_contains =
    let rule =
      CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
        (ISPEC
          `boxes:((((num#num)#num)#((num#num)#num))list)`
          (INST_TYPE [`:6`,`:N`]
            candle_q_center_environment_vector_contains)) in
    MATCH_MP rule boxes_length in
  let center_values_length =
    ISPECL
      [`(\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))`;
       `6`]
      LENGTH_LIST_OF_SEQ in
  let center_contains =
    MATCH_MP
      (SPECL
        [`candle_q_center_environment_list boxes`;
         `list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6`;
         `coordinate:num`]
        candle_q_packed_delta_product_jet_environment_contains)
      (CONJ center_values_length
        (CONJ center_environment_contains coordinate_lt_six)) in
  let box_shape =
    SPECL
      [`coordinate:num`;
       `boxes:((((num#num)#num)#((num#num)#num))list)`]
      candle_q_packed_delta_product_jet_environment_shape in
  let box_contains =
    let p = `p:real^6` in
    let p_in_box =
      `(p:real^6) IN interval
        [candle_q_box_lower_vector boxes,
         candle_q_box_upper_vector boxes]` in
    let values_length =
      ISPECL [`(\k. (p:real^6)$(k + 1))`; `6`]
        LENGTH_LIST_OF_SEQ in
    let environment_contains =
      let rule =
        CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
          (ISPECL
            [`boxes:((((num#num)#num)#((num#num)#num))list)`;
             `p:real^6`]
            (INST_TYPE [`:6`,`:N`]
              candle_q_box_stack_contains_vector)) in
      MATCH_MP rule (CONJ boxes_length (ASSUME p_in_box)) in
    let contains_at_p =
      MATCH_MP
        (SPECL
          [`boxes:((((num#num)#num)#((num#num)#num))list)`;
           `list_of_seq (\k. (p:real^6)$(k + 1)) 6`;
           `coordinate:num`]
          candle_q_packed_delta_product_jet_environment_contains)
        (CONJ values_length
          (CONJ environment_contains coordinate_lt_six)) in
    GEN p (DISCH p_in_box contains_at_p) in
  let domain_components =
    end_itlist CONJ
      [center_regular; box_regular; center_shape; center_contains;
       box_shape; box_contains] in
  let complete_rule =
    CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
      (ISPECL
        [`candle_packed_delta_product_expr coordinate`;
         `candle_packed_delta_product_expr coordinate`;
         `boxes:((((num#num)#num)#((num#num)#num))list)`;
         `T`;
         `candle_q_packed_delta_product_jet_environment coordinate
            (candle_q_center_environment_list boxes)`;
         `candle_q_packed_delta_product_jet_environment coordinate boxes`;
         `ARB:real^6`]
        (INST_TYPE [`:6`,`:N`]
          candle_q_dim_taylor_model_complete_analytic_invariant)) in
  let complete_premises =
    end_itlist CONJ
      [analytic_valid; erasure_equal; boxes_length; boxes_valid;
       DISCH `T` domain_components] in
  REWRITE_TAC[candle_q_packed_delta_product_result_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC (MATCH_MP complete_rule complete_premises));;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_six_list_lookup;
     candle_q_six_real_lookup_list;
     candle_q_packed_delta_neg_derivative_jet_environment_shape;
     candle_q_packed_delta_product_jet_environment_shape;
     candle_q_packed_delta_neg_derivative_jet_environment_contains;
     candle_q_packed_delta_product_jet_environment_contains;
     candle_q_packed_delta_neg_derivative_result_analytic_invariant;
     candle_q_packed_delta_product_result_analytic_invariant] then
  failwith "packed source specialized result sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_SPECIALIZED_RESULT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
