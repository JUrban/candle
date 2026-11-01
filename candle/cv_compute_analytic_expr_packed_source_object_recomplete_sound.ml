(* ========================================================================== *)
(* Faithful Taylor recompletion preserves the packed object invariant.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Object-q algebraic operations retain their   *)
(* exact center jet and packed Hessian, then recompute whole-cell value and  *)
(* gradient bounds.  This theorem packages that common completion step.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_complete_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_algebraic_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_recomplete_sound = struct

open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_error_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_complete_sound;;
open Candle_cv_analytic_expr_packed_source_object_merge_sound;;

let candle_q_packed_object_item_recomplete_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       (candle_q_packed_object_value_bound6
         radii center_value center_gradient packed_hessian)
       (candle_q_packed_object_gradient_complete6
         radii center_gradient packed_hessian)
       packed_hessian center_e box_e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "geometry")
        (LABEL_TAC "input_invariant"))) THEN
  let completed =
    MATCH_MP
      (ISPECL
        [`outer_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `center_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `outer_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`; `domain:bool`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `value_bound:((num#num)#num)#((num#num)#num)`;
         `gradient_bounds:
           (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
        candle_q_packed_object_item_faithful_complete_analytic_invariant)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (outer_boxes:
               (((num#num)#num)#((num#num)#num))list) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             outer_boxes center_boxes outer_boxes radii`;
         ASSUME
           `candle_q_packed_object_item_analytic_invariant
             center_boxes outer_boxes domain center_value center_gradient
             value_bound gradient_bounds packed_hessian center_e box_e`]) in
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "input_domain"))) THEN
  MP_TAC completed THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_result_analytic_invariant_def;
     candle_q_dim_taylor_model_result_domain_def;
     candle_q_dim_taylor_model_result_center_def;
     candle_q_dim_taylor_model_proxy_def;
     candle_q_dim_taylor_model_result_value_bound_def;
     candle_q_dim_taylor_model_result_gradient_bounds_def;
     candle_q_dim_taylor_model_result_hessian_def;
     candle_q_dim_taylor_model_result_make_def;
     candle_q_dim_jet_make_def; FST; SND] THEN
  CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
  DISCH_THEN (LABEL_TAC "completed_domain") THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  USE_THEN "input_domain"
    (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
      (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (LABEL_TAC "center_all") (K ALL_TAC)))) THEN
  USE_THEN "completed_domain"
    (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "completed_regular_all")
        (CONJUNCTS_THEN2 (K ALL_TAC)
          (CONJUNCTS_THEN2 (K ALL_TAC)
            (CONJUNCTS_THEN2 (LABEL_TAC "completed_shape")
              (LABEL_TAC "completed_contains_all")))))) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "center_length" ACCEPT_TAC;
    USE_THEN "completed_shape" MP_TAC THEN
    REWRITE_TAC[candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_make_def];
    USE_THEN "center_all" ACCEPT_TAC;
    X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
    MP_TAC
      (MATCH_MP
        (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
          (ISPECL
            [`outer_boxes:
               (((num#num)#num)#((num#num)#num))list`;
             `environment:real list`]
            (INST_TYPE [`:6`,`:N`]
              candle_q_stack_contains_vector_witness)))
        (CONJ
          (ASSUME
            `LENGTH
              (outer_boxes:
                (((num#num)#num)#((num#num)#num))list) = 6`)
          (ASSUME
            `candle_q_stack_contains outer_boxes environment`))) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `z:real^6`
        (CONJUNCTS_THEN2 (LABEL_TAC "z_in") SUBST1_TAC)) THEN
    CONJ_TAC THENL
     [USE_THEN "completed_regular_all"
        (fun th -> MATCH_MP_TAC (SPEC `z:real^6` th));
      REWRITE_TAC[candle_q_packed_object_box_jet_def;
                  candle_q_dim_jet_make_def] THEN
      USE_THEN "completed_contains_all"
        (fun th -> MATCH_MP_TAC (SPEC `z:real^6` th))] THEN
    ASM_REWRITE_TAC[]]);;

if hyp candle_q_packed_object_item_recomplete_analytic_invariant <> [] then
  failwith "packed source object recomplete sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_RECOMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
