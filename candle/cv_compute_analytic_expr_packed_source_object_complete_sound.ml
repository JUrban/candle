(* ========================================================================== *)
(* Faithful completion of an authenticated packed source object.             *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source-object invariant records the       *)
(* center and whole-box states produced by the logical source replay.  The   *)
(* final object checker does not retain the latter value/gradient fields: it *)
(* completes them faithfully from the center fields, packed Hessian, and     *)
(* authenticated radii.  This unit joins those two already-proved contracts. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_complete_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_complete_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_complete_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_taylor_model_packed_object_complete_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_compute;;

let candle_packed_source_object_dimindex_six =
  DIMINDEX_CONV `dimindex (:6)`;;

let candle_q_packed_object_item_faithful_complete_analytic_invariant = prove
 (`!source_boxes center_boxes outer_boxes radii domain
       center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e.
     LENGTH source_boxes = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant (ARB:real^6)
       source_boxes
       (candle_q_dim_taylor_model_result_make domain
         (candle_q_dim_jet_make center_value center_gradient
           (candle_q_packed_hessian6_expand packed_hessian))
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed_hessian)
         (candle_q_packed_object_gradient_complete6
           radii center_gradient packed_hessian)
         (candle_q_packed_hessian6_expand packed_hessian))
       center_e box_e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
        (LABEL_TAC "object_invariant"))) THEN
  MP_TAC
    (ISPECL
      [`source_boxes:
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
      candle_q_packed_object_item_source_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (LABEL_TAC "source_invariant") THEN
  USE_THEN "object_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "object_domain"))) THEN
  USE_THEN "correspondence" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_correspondence_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_correspondence")
        (CONJUNCTS_THEN2 (LABEL_TAC "radii_cover")
          (LABEL_TAC "outer_cover")))) THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `center_value:((num#num)#num)#((num#num)#num)`;
       `center_gradient:
         (((num#num)#num)#((num#num)#num))list`;
       `packed_hessian:
         (((num#num)#num)#((num#num)#num))list`;
       `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
      candle_q_packed_object_complete6_source_analytic_invariant) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  USE_THEN "source_invariant" MP_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_result_analytic_invariant_def;
     candle_q_packed_object_result_domain;
     candle_q_packed_object_result_center;
     candle_q_packed_object_result_proxy] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
      (CONJUNCTS_THEN2 (LABEL_TAC "source_regular")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
            (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
              (LABEL_TAC "source_contains")))))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_packed_source_object_dimindex_six];
    ASM_MESON_TAC
      [candle_packed_source_object_dimindex_six;
       candle_q_packed_object_center_jet_def;
       candle_q_dim_jet_make_def];
    ASM_MESON_TAC
      [candle_packed_source_object_dimindex_six;
       candle_q_packed_object_center_jet_def;
       candle_q_dim_jet_make_def];
    ASM_MESON_TAC[candle_packed_source_object_dimindex_six];
    MATCH_MP_TAC
      (REWRITE_RULE
        [candle_packed_source_object_dimindex_six;
         candle_q_packed_object_box_jet_def;
         candle_q_dim_jet_hessian_def; candle_q_dim_jet_make_def; FST; SND]
        (ISPECL
          [`box_e:candle_analytic_expr`;
           `candle_q_packed_object_box_jet
             value_bound gradient_bounds packed_hessian`;
           `candle_q_box_lower_vector source_boxes:real^6`;
           `candle_q_box_upper_vector source_boxes:real^6`]
          candle_q_dim_analytic_jet_hessian_box_contains)) THEN
    ASM_MESON_TAC
      [candle_packed_source_object_dimindex_six;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_make_def]]);;

let candle_cv_q_packed_object_item_accept6_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii domain
       center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e.
     LENGTH source_boxes = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e /\
     candle_cv_q_packed_object_accept6
       (candle_cv_bool domain)
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed_hessian) = Cexp_num 1
     ==>
     m_cell_pass (candle_analytic_denote_dim box_e)
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
        (CONJUNCTS_THEN2 (LABEL_TAC "object_invariant")
          (LABEL_TAC "accepted")))) THEN
  let accepted =
    MATCH_MP
      (SPECL
        [`domain:bool`; `radii:((num#num)#num)list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
           (((num#num)#num)#((num#num)#num))list`]
        candle_cv_q_packed_object_accept6_negative)
      (ASSUME
        `candle_cv_q_packed_object_accept6
          (candle_cv_bool domain)
          (candle_cv_q_list radii)
          (candle_cv_q_interval center_value)
          (candle_cv_q_interval_list center_gradient)
          (candle_cv_q_interval_list packed_hessian) = Cexp_num 1`) in
  let domain_th,accepted_rest = CONJ_PAIR accepted in
  let _,accepted_rest = CONJ_PAIR accepted_rest in
  let _,accepted_rest = CONJ_PAIR accepted_rest in
  let _,negative = CONJ_PAIR accepted_rest in
  let complete_invariant =
    MATCH_MP
      (ISPECL
        [`source_boxes:
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
             (source_boxes:
               (((num#num)#num)#((num#num)#num))list) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             source_boxes center_boxes outer_boxes radii`;
         ASSUME
           `candle_q_packed_object_item_analytic_invariant
             center_boxes outer_boxes domain center_value center_gradient
             value_bound gradient_bounds packed_hessian center_e box_e`]) in
  let enabled =
    MATCH_MP
      (REWRITE_RULE
        [candle_q_dim_taylor_model_result_analytic_invariant_def;
         candle_q_dim_taylor_model_result_domain_def;
         candle_q_dim_taylor_model_result_make_def; FST; SND]
        complete_invariant)
      domain_th in
  let _,enabled_rest = CONJ_PAIR enabled in
  let _,enabled_rest = CONJ_PAIR enabled_rest in
  let _,enabled_rest = CONJ_PAIR enabled_rest in
  let _,enabled_rest = CONJ_PAIR enabled_rest in
  let _,source_contains = CONJ_PAIR enabled_rest in
  REWRITE_TAC[m_cell_pass] THEN
  X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
  let point_contains =
    MATCH_MP
      (SPEC `p:real^6` source_contains)
      (ASSUME
        `(p:real^6) IN interval
          [candle_q_box_lower_vector source_boxes,
           candle_q_box_upper_vector source_boxes]`) in
  let value_rule =
    REWRITE_RULE [candle_q_dim_taylor_model_result_make_def]
      (ISPECL
        [`box_e:candle_analytic_expr`;
         `candle_q_dim_taylor_model_proxy
           (candle_q_dim_taylor_model_result_make (domain:bool)
             (candle_q_dim_jet_make center_value center_gradient
               (candle_q_packed_hessian6_expand packed_hessian))
             (candle_q_packed_object_value_bound6
               radii center_value center_gradient packed_hessian)
             (candle_q_packed_object_gradient_complete6
               radii center_gradient packed_hessian)
             (candle_q_packed_hessian6_expand packed_hessian))`;
         `p:real^6`]
        candle_q_dim_analytic_contains_denote_value) in
  let value_contains = MATCH_MP value_rule point_contains in
  MP_TAC
    (REWRITE_RULE
      [candle_q_dim_taylor_model_proxy_def;
       candle_q_dim_taylor_model_result_value_bound_def;
       candle_q_dim_taylor_model_result_make_def;
       candle_q_dim_jet_f_def; candle_q_dim_jet_make_def; FST; SND]
      value_contains) THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  MP_TAC negative THEN REAL_ARITH_TAC);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_item_faithful_complete_analytic_invariant;
     candle_cv_q_packed_object_item_accept6_cell_pass]
then failwith "packed source object complete sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_COMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
