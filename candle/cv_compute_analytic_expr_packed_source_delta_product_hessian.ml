(* ========================================================================== *)
(* Exact compact Hessian for 4 * x_i * delta.                                *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the generic product-rule operation    *)
(* used by the three authenticated four-coordinate delta instructions.       *)
(* It preserves the optimized checker's upper-triangular order and exact     *)
(* add-then-scale association.                                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_gradient.ml";;

module Candle_cv_analytic_expr_packed_source_delta_product_hessian = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;

let candle_q_packed_delta_scale4_def = new_definition
 `candle_q_packed_delta_scale4 value =
    let twice = candle_q_interval_add value value in
    candle_q_interval_add twice twice`;;

let candle_real_packed_delta_scale4_def = new_definition
 `candle_real_packed_delta_scale4 value =
    let twice = value + value in twice + twice`;;

let candle_cv_q_packed_delta_scale4_def = new_definition
 `candle_cv_q_packed_delta_scale4 value =
    let twice = candle_cv_q_interval_add value value in
    candle_cv_q_interval_add twice twice`;;

let candle_cv_q_packed_delta_scale4_correct = prove
 (`!value.
     candle_cv_q_packed_delta_scale4 (candle_cv_q_interval value) =
     candle_cv_q_interval (candle_q_packed_delta_scale4 value)`,
  REWRITE_TAC[candle_cv_q_packed_delta_scale4_def;
              candle_q_packed_delta_scale4_def;
              candle_cv_q_interval_add_correct;
              LET_DEF; LET_END_DEF]);;

let candle_q_packed_delta_scale4_sound = prove
 (`!interval value.
     candle_q_interval_contains interval value
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_scale4 interval)
       (candle_real_packed_delta_scale4 value)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_scale4_def;
              candle_real_packed_delta_scale4_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
  MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[]);;

let candle_real_packed_delta_scale4_eq = prove
 (`!value. candle_real_packed_delta_scale4 value = &4 * value`,
  REWRITE_TAC[candle_real_packed_delta_scale4_def;
              LET_DEF; LET_END_DEF] THEN REAL_ARITH_TAC);;

let candle_q_packed_delta_product_hessian_entry_def = new_definition
 `candle_q_packed_delta_product_hessian_entry coordinate box_coordinate
      delta_gradient row_index column_index delta_hessian =
    let base = candle_q_interval_mul box_coordinate delta_hessian in
    let with_row =
      if row_index = coordinate then
        candle_q_interval_add base
          (candle_q_interval_lookup column_index delta_gradient)
      else base in
    let complete =
      if column_index = coordinate then
        candle_q_interval_add with_row
          (candle_q_interval_lookup row_index delta_gradient)
      else with_row in
    candle_q_packed_delta_scale4 complete`;;

let candle_real_packed_delta_product_hessian_entry_def = new_definition
 `candle_real_packed_delta_product_hessian_entry coordinate box_coordinate
      delta_gradient row_index column_index delta_hessian =
    let base = box_coordinate * delta_hessian in
    let with_row =
      if row_index = coordinate then
        base + candle_q_real_lookup column_index delta_gradient
      else base in
    let complete =
      if column_index = coordinate then
        with_row + candle_q_real_lookup row_index delta_gradient
      else with_row in
    candle_real_packed_delta_scale4 complete`;;

let candle_q_packed_delta_lookup_contains = prove
 (`!index intervals values.
     ALL2 candle_q_interval_contains intervals values
     ==>
     candle_q_interval_contains
       (candle_q_interval_lookup index intervals)
       (candle_q_real_lookup index values)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC
    (ISPEC
      `intervals:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
  MP_TAC (ISPEC `values:real list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[ALL2; candle_q_interval_lookup_def;
                  candle_q_real_lookup_def;
                  candle_q_zero_interval_contains] THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_delta_product_hessian_entry_sound = prove
 (`!coordinate box_coordinate delta_gradient row_index column_index
       delta_hessian box_value gradient_values hessian_value.
     candle_q_interval_contains box_coordinate box_value /\
     ALL2 candle_q_interval_contains delta_gradient gradient_values /\
     candle_q_interval_contains delta_hessian hessian_value
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_product_hessian_entry coordinate
         box_coordinate delta_gradient row_index column_index delta_hessian)
       (candle_real_packed_delta_product_hessian_entry coordinate
         box_value gradient_values row_index column_index hessian_value)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`row_index:num`;
       `delta_gradient:(((num#num)#num)#((num#num)#num))list`;
       `gradient_values:real list`]
      candle_q_packed_delta_lookup_contains) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`column_index:num`;
       `delta_gradient:(((num#num)#num)#((num#num)#num))list`;
       `gradient_values:real list`]
      candle_q_packed_delta_lookup_contains) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`box_coordinate:((num#num)#num)#((num#num)#num)`;
       `delta_hessian:((num#num)#num)#((num#num)#num)`;
       `box_value:real`; `hessian_value:real`]
      candle_q_interval_mul_sound) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_product_hessian_entry_def;
              candle_real_packed_delta_product_hessian_entry_def;
              LET_DEF; LET_END_DEF] THEN
  (ASM_CASES_TAC `(row_index:num) = coordinate` THEN
   ASM_CASES_TAC `(column_index:num) = coordinate`) THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_packed_delta_scale4_sound THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_packed_delta_scale4_sound THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_packed_delta_scale4_sound THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_packed_delta_scale4_sound THEN
    ASM_MESON_TAC[]]);;

let candle_cv_q_packed_delta_product_hessian_entry_def = new_definition
 `candle_cv_q_packed_delta_product_hessian_entry coordinate box_coordinate
      delta_gradient row_index column_index delta_hessian =
    let base = candle_cv_q_interval_mul box_coordinate delta_hessian in
    let with_row = Cexp_if (Cexp_eq row_index coordinate)
      (candle_cv_q_interval_add base
        (candle_cv_q_interval_lookup column_index delta_gradient))
      base in
    let complete = Cexp_if (Cexp_eq column_index coordinate)
      (candle_cv_q_interval_add with_row
        (candle_cv_q_interval_lookup row_index delta_gradient))
      with_row in
    candle_cv_q_packed_delta_scale4 complete`;;

let candle_cv_q_packed_delta_product_hessian_entry_correct = prove
 (`!coordinate box_coordinate delta_gradient row_index column_index
       delta_hessian.
     candle_cv_q_packed_delta_product_hessian_entry
       (Cexp_num coordinate) (candle_cv_q_interval box_coordinate)
       (candle_cv_q_interval_list delta_gradient)
       (Cexp_num row_index) (Cexp_num column_index)
       (candle_cv_q_interval delta_hessian) =
     candle_cv_q_interval
       (candle_q_packed_delta_product_hessian_entry coordinate
         box_coordinate delta_gradient row_index column_index delta_hessian)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(row_index:num) = coordinate` THEN
  ASM_CASES_TAC `(column_index:num) = coordinate` THEN
  ASM_REWRITE_TAC[candle_cv_q_packed_delta_product_hessian_entry_def;
                  candle_q_packed_delta_product_hessian_entry_def;
                  candle_cv_q_interval_mul_correct;
                  candle_cv_q_interval_lookup_correct;
                  candle_cv_q_interval_add_correct;
                  candle_cv_q_packed_delta_scale4_correct;
                  LET_DEF; LET_END_DEF;
                  cexp_eq_def; injectivity "cval"; cexp_if_def]);;

let candle_q_packed_delta_product_hessian_def = define
 `(candle_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient [] entries = []) /\
  (candle_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (CONS index_pair index_tail) [] = []) /\
  (candle_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (CONS index_pair index_tail)
      (CONS entry_value entry_tail) =
     CONS
       (candle_q_packed_delta_product_hessian_entry coordinate
         box_coordinate delta_gradient (FST index_pair) (SND index_pair)
         entry_value)
       (candle_q_packed_delta_product_hessian coordinate box_coordinate
         delta_gradient index_tail entry_tail))`;;

let candle_real_packed_delta_product_hessian_def = define
 `(candle_real_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient [] entries = []) /\
  (candle_real_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (CONS index_pair index_tail) [] = []) /\
  (candle_real_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (CONS index_pair index_tail)
      (CONS entry_value entry_tail) =
     CONS
       (candle_real_packed_delta_product_hessian_entry coordinate
         box_coordinate delta_gradient (FST index_pair) (SND index_pair)
         entry_value)
       (candle_real_packed_delta_product_hessian coordinate box_coordinate
         delta_gradient index_tail entry_tail))`;;

let candle_q_packed_delta_product_hessian_sound = prove
 (`!indices coordinate box_coordinate delta_gradient entries
       box_value gradient_values real_entries.
     candle_q_interval_contains box_coordinate box_value /\
     ALL2 candle_q_interval_contains delta_gradient gradient_values /\
     ALL2 candle_q_interval_contains entries real_entries
     ==>
     ALL2 candle_q_interval_contains
       (candle_q_packed_delta_product_hessian coordinate box_coordinate
         delta_gradient indices entries)
       (candle_real_packed_delta_product_hessian coordinate box_value
         gradient_values indices real_entries)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_delta_product_hessian_def;
                candle_real_packed_delta_product_hessian_def; ALL2];
    POP_ASSUM (LABEL_TAC "product_hessian_ih") THEN
    REPEAT GEN_TAC THEN
    MP_TAC
      (ISPEC
        `entries:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    MP_TAC (ISPEC `real_entries:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `real_entry:real`
          (X_CHOOSE_THEN `real_tail:real list` SUBST_ALL_TAC))) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN
          `interval_entry:((num#num)#num)#((num#num)#num)`
          (X_CHOOSE_THEN
            `interval_tail:(((num#num)#num)#((num#num)#num))list`
            SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; candle_q_packed_delta_product_hessian_def;
                candle_real_packed_delta_product_hessian_def] THEN
    ASM_MESON_TAC[candle_q_packed_delta_product_hessian_entry_sound]]);;

let candle_cv_q_packed_delta_indices_def = define
 `(candle_cv_q_packed_delta_indices ([]:(num#num)list) = Cexp_num 0) /\
  (candle_cv_q_packed_delta_indices (CONS index_pair index_tail) =
     Cexp_pair (Cexp_pair (Cexp_num (FST index_pair))
                  (Cexp_num (SND index_pair)))
       (candle_cv_q_packed_delta_indices index_tail))`;;

let candle_cv_q_packed_delta_product_hessian_def = define
 `(candle_cv_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (Cexp_num index_end) entries = Cexp_num 0) /\
  (candle_cv_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (Cexp_pair encoded_index index_tail)
      (Cexp_num entry_end) = Cexp_num 0) /\
  (candle_cv_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient (Cexp_pair encoded_index index_tail)
      (Cexp_pair entry_value entry_tail) =
     Cexp_pair
       (candle_cv_q_packed_delta_product_hessian_entry coordinate
         box_coordinate delta_gradient (Cexp_fst encoded_index)
         (Cexp_snd encoded_index) entry_value)
       (candle_cv_q_packed_delta_product_hessian coordinate box_coordinate
         delta_gradient index_tail entry_tail))`;;

let candle_cv_q_packed_delta_product_hessian_correct = prove
 (`!indices coordinate box_coordinate delta_gradient entries.
     candle_cv_q_packed_delta_product_hessian
       (Cexp_num coordinate) (candle_cv_q_interval box_coordinate)
       (candle_cv_q_interval_list delta_gradient)
       (candle_cv_q_packed_delta_indices indices)
       (candle_cv_q_interval_list entries) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_product_hessian coordinate box_coordinate
         delta_gradient indices entries)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_q_packed_delta_indices_def;
                candle_cv_q_interval_list_def;
                candle_cv_q_packed_delta_product_hessian_def;
                candle_q_packed_delta_product_hessian_def];
    POP_ASSUM (LABEL_TAC "product_hessian_cv_ih") THEN
    REPEAT GEN_TAC THEN
    MP_TAC
      (ISPEC
        `entries:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN
          `interval_entry:((num#num)#num)#((num#num)#num)`
          (X_CHOOSE_THEN
            `interval_tail:(((num#num)#num)#((num#num)#num))list`
            SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_cv_q_packed_delta_indices_def;
                    candle_cv_q_interval_list_def;
                    candle_cv_q_packed_delta_product_hessian_def;
                    candle_q_packed_delta_product_hessian_def;
                    candle_cv_q_packed_delta_product_hessian_entry_correct;
                    cexp_fst_def; cexp_snd_def]]);;

let candle_q_packed_delta_hessian_indices_def = new_definition
 `candle_q_packed_delta_hessian_indices =
    [(0,0);(0,1);(0,2);(0,3);(0,4);(0,5);
     (1,1);(1,2);(1,3);(1,4);(1,5);
     (2,2);(2,3);(2,4);(2,5);
     (3,3);(3,4);(3,5);(4,4);(4,5);(5,5)]`;;

let candle_cv_q_packed_source_delta_product_hessian_compute_eqs =
  candle_cv_q_packed_source_delta_gradient_compute_eqs @
  map SPEC_ALL
    [candle_cv_q_packed_delta_scale4_def;
     candle_cv_q_packed_delta_product_hessian_entry_def;
     candle_cv_q_packed_delta_product_hessian_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_delta_scale4_correct;
     candle_q_packed_delta_scale4_sound;
     candle_real_packed_delta_scale4_eq;
     candle_q_packed_delta_lookup_contains;
     candle_q_packed_delta_product_hessian_entry_sound;
     candle_cv_q_packed_delta_product_hessian_entry_correct;
     candle_q_packed_delta_product_hessian_sound;
     candle_cv_q_packed_delta_product_hessian_correct] then
  failwith "packed source delta product Hessian: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_PRODUCT_HESSIAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
