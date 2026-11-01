(* ========================================================================== *)
(* Direct analytic soundness of object-q negation.                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_recomplete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_neg_sound = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;

let candle_q_packed_object_hessian_neg_def = new_definition
 `candle_q_packed_object_hessian_neg packed =
    MAP candle_q_interval_neg packed`;;

let candle_q_packed_object_hessian_neg_length = prove
 (`!packed.
     LENGTH (candle_q_packed_object_hessian_neg packed) = LENGTH packed`,
  REWRITE_TAC[candle_q_packed_object_hessian_neg_def; LENGTH_MAP]);;

let candle_q_packed_object_hessian_neg_expand = prove
 (`!packed.
     LENGTH packed = 21
     ==>
     candle_q_packed_hessian6_expand
       (candle_q_packed_object_hessian_neg packed) =
     candle_q_dim_interval_matrix_neg
       (candle_q_packed_hessian6_expand packed)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < 21
        ==> EL i (MAP candle_q_interval_neg packed) =
            candle_q_interval_neg (EL i packed)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EL_MAP THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_packed_object_hessian_neg_def;
              candle_q_packed_hessian6_expand_def;
              candle_q_dim_interval_matrix_neg_map;
              candle_q_dim_interval_list_neg_map; MAP] THEN
  let lookup =
    ASSUME
      `!i. i < 21
           ==> EL i (MAP candle_q_interval_neg packed) =
               candle_q_interval_neg (EL i packed)` in
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

let candle_q_packed_object_box_jet_neg = prove
 (`!value_bound gradient_bounds packed_hessian.
     LENGTH packed_hessian = 21
     ==>
     candle_q_packed_object_box_jet
       (candle_q_interval_neg value_bound)
       (candle_q_dim_interval_list_neg gradient_bounds)
       (candle_q_packed_object_hessian_neg packed_hessian) =
     candle_q_dim_jet_normalized_neg
       (candle_q_packed_object_box_jet
         value_bound gradient_bounds packed_hessian)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  ASM_SIMP_TAC[candle_q_packed_object_hessian_neg_expand]);;

let candle_q_packed_object_center_first_neg_contains = prove
 (`!center_value center_gradient environment e.
     LENGTH center_gradient = 6 /\
     candle_q_packed_object_center_first_contains
       center_value center_gradient environment e
     ==>
     candle_q_packed_object_center_first_contains
       (candle_q_interval_neg center_value)
       (candle_q_dim_interval_list_neg center_gradient)
       environment (Candle_analytic_neg e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "gradient_length")
      (LABEL_TAC "input_contains")) THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  USE_THEN "input_contains" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "value_contains")
      (LABEL_TAC "gradient_contains")) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_neg_sound THEN
    USE_THEN "value_contains" ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_interval_list_neg_lookup] THEN
    MATCH_MP_TAC candle_q_interval_neg_sound THEN
    USE_THEN "gradient_contains"
      (fun th -> MATCH_MP_TAC (SPEC `i:num` th)) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_neg_contains = prove
 (`!value_bound gradient_bounds packed_hessian environment e.
     LENGTH packed_hessian = 21 /\
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_box_jet
         value_bound gradient_bounds packed_hessian) /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         value_bound gradient_bounds packed_hessian) environment e
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         (candle_q_interval_neg value_bound)
         (candle_q_dim_interval_list_neg gradient_bounds)
         (candle_q_packed_object_hessian_neg packed_hessian))
       environment (Candle_analytic_neg e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "hessian_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "input_shape")
        (LABEL_TAC "input_contains"))) THEN
  SUBGOAL_THEN
   `candle_q_packed_object_box_jet
      (candle_q_interval_neg value_bound)
      (candle_q_dim_interval_list_neg gradient_bounds)
      (candle_q_packed_object_hessian_neg packed_hessian) =
    candle_q_dim_jet_normalized_neg
      (candle_q_packed_object_box_jet
        value_bound gradient_bounds packed_hessian)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_box_jet_neg THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "input_contains" MP_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
  DISCH_THEN (LABEL_TAC "input_components") THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_center_all_neg_contains = prove
 (`!center_boxes center_value center_gradient e.
     LENGTH center_gradient = 6 /\
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment e /\
            candle_q_packed_object_center_first_contains
              center_value center_gradient environment e)
     ==>
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment (Candle_analytic_neg e) /\
            candle_q_packed_object_center_first_contains
              (candle_q_interval_neg center_value)
              (candle_q_dim_interval_list_neg center_gradient)
              environment (Candle_analytic_neg e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
  let input_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains center_boxes environment
             ==> candle_analytic_regular_at environment e /\
                 candle_q_packed_object_center_first_contains
                   center_value center_gradient environment e`))
      (ASSUME `candle_q_stack_contains center_boxes environment`) in
  MP_TAC input_at THEN STRIP_TAC THEN
  (CONJ_TAC THENL
    [(ASM_REWRITE_TAC[candle_analytic_regular_at_def]);
     (MATCH_MP_TAC candle_q_packed_object_center_first_neg_contains THEN
      ASM_REWRITE_TAC[])]));;

let candle_q_packed_object_box_all_neg_contains = prove
 (`!outer_boxes value_bound gradient_bounds packed_hessian e.
     LENGTH packed_hessian = 21 /\
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_box_jet
         value_bound gradient_bounds packed_hessian) /\
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment e /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                value_bound gradient_bounds packed_hessian)
              environment e)
     ==>
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment (Candle_analytic_neg e) /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                (candle_q_interval_neg value_bound)
                (candle_q_dim_interval_list_neg gradient_bounds)
                (candle_q_packed_object_hessian_neg packed_hessian))
              environment (Candle_analytic_neg e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
  let input_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains outer_boxes environment
             ==> candle_analytic_regular_at environment e /\
                 candle_q_dim_analytic_contains 6
                   (candle_q_packed_object_box_jet
                     value_bound gradient_bounds packed_hessian)
                   environment e`))
      (ASSUME `candle_q_stack_contains outer_boxes environment`) in
  MP_TAC input_at THEN STRIP_TAC THEN
  (CONJ_TAC THENL
    [(ASM_REWRITE_TAC[candle_analytic_regular_at_def]);
     (MATCH_MP_TAC candle_q_packed_object_box_neg_contains THEN
      ASM_REWRITE_TAC[])]));;

let candle_q_packed_object_item_neg_raw_analytic_invariant = prove
 (`!center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e.
     LENGTH packed_hessian = 21 /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain
       (candle_q_interval_neg center_value)
       (candle_q_dim_interval_list_neg center_gradient)
       (candle_q_interval_neg value_bound)
       (candle_q_dim_interval_list_neg gradient_bounds)
       (candle_q_packed_object_hessian_neg packed_hessian)
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "hessian_length")
      (LABEL_TAC "input_invariant")) THEN
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "input_domain"))) THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def;
              candle_analytic_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  USE_THEN "input_domain"
    (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "box_shape")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_all")
          (LABEL_TAC "box_all")))) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_list_neg_length]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC
      (MATCH_MP
        (SPECL
          [`value_bound:((num#num)#num)#((num#num)#num)`;
           `gradient_bounds:
             (((num#num)#num)#((num#num)#num))list`;
           `packed_hessian:
             (((num#num)#num)#((num#num)#num))list`]
          candle_q_packed_object_box_jet_neg)
        (ASSUME
          `LENGTH
            (packed_hessian:
              (((num#num)#num)#((num#num)#num))list) = 21`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
    USE_THEN "box_shape" ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(MATCH_MP_TAC candle_q_packed_object_center_all_neg_contains THEN
     ASM_REWRITE_TAC[]);
    (MP_TAC
      (SPECL
        [`outer_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `value_bound:((num#num)#num)#((num#num)#num)`;
         `gradient_bounds:
           (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `box_e:candle_analytic_expr`]
        candle_q_packed_object_box_all_neg_contains) THEN
     ASM_REWRITE_TAC[])]);;

let candle_q_packed_object_item_neg_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     LENGTH packed_hessian = 21 /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain
       (candle_q_interval_neg center_value)
       (candle_q_dim_interval_list_neg center_gradient)
       (candle_q_packed_object_value_bound6 radii
         (candle_q_interval_neg center_value)
         (candle_q_dim_interval_list_neg center_gradient)
         (candle_q_packed_object_hessian_neg packed_hessian))
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_dim_interval_list_neg center_gradient)
         (candle_q_packed_object_hessian_neg packed_hessian))
       (candle_q_packed_object_hessian_neg packed_hessian)
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       `domain:bool`;
       `candle_q_interval_neg center_value`;
       `candle_q_dim_interval_list_neg center_gradient`;
       `candle_q_interval_neg value_bound`;
       `candle_q_dim_interval_list_neg gradient_bounds`;
       `candle_q_packed_object_hessian_neg packed_hessian`;
       `Candle_analytic_neg center_e`;
       `Candle_analytic_neg box_e`]
      candle_q_packed_object_item_recomplete_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_packed_object_item_neg_raw_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_hessian_neg_length;
     candle_q_packed_object_hessian_neg_expand;
     candle_q_packed_object_box_jet_neg;
     candle_q_packed_object_center_first_neg_contains;
     candle_q_packed_object_box_neg_contains;
     candle_q_packed_object_center_all_neg_contains;
     candle_q_packed_object_box_all_neg_contains;
     candle_q_packed_object_item_neg_raw_analytic_invariant;
     candle_q_packed_object_item_neg_analytic_invariant] then
  failwith "packed source object neg sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_NEG_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
