(* ========================================================================== *)
(* Direct analytic soundness of exact object-q addition.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_recomplete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_add_sound = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;

(* These operations deliberately use raw exact rational addition.  They are
   the HOL representation of the MAP2 operations in the HOL4 object-q state;
   no normalization is inserted at this boundary. *)

let candle_q_packed_object_interval_list_add_def = new_definition
 `candle_q_packed_object_interval_list_add xs ys =
    MAP2 candle_q_interval_add xs ys`;;

let candle_q_packed_object_interval_matrix_add_def = new_definition
 `candle_q_packed_object_interval_matrix_add xs ys =
    MAP2 candle_q_packed_object_interval_list_add xs ys`;;

let candle_q_packed_object_hessian_add_def = new_definition
 `candle_q_packed_object_hessian_add left right =
    MAP2 candle_q_interval_add left right`;;

let candle_q_packed_object_interval_list_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_q_packed_object_interval_list_add xs ys) =
         LENGTH xs`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_interval_list_add_def; LENGTH_MAP2]);;

let candle_q_packed_object_interval_list_add_lookup = prove
 (`!xs ys i.
     LENGTH xs = LENGTH ys /\ i < LENGTH xs
     ==>
     candle_q_interval_lookup i
       (candle_q_packed_object_interval_list_add xs ys) =
     candle_q_interval_add
       (candle_q_interval_lookup i xs)
       (candle_q_interval_lookup i ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH
      (ys:(((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_packed_object_interval_list_add_def;
               LENGTH_MAP2; EL_MAP2;
               candle_q_interval_lookup_in_range]);;

let candle_q_packed_object_interval_matrix_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_q_packed_object_interval_matrix_add xs ys) =
         LENGTH xs`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_interval_matrix_add_def; LENGTH_MAP2]);;

let candle_q_packed_object_interval_matrix_add_row_lookup = prove
 (`!xs ys i.
     LENGTH xs = LENGTH ys /\ i < LENGTH xs
     ==>
     candle_q_dim_interval_row_lookup i
       (candle_q_packed_object_interval_matrix_add xs ys) =
     candle_q_packed_object_interval_list_add
       (candle_q_dim_interval_row_lookup i xs)
       (candle_q_dim_interval_row_lookup i ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < LENGTH
      (ys:((((num#num)#num)#((num#num)#num))list)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_packed_object_interval_matrix_add_def;
               LENGTH_MAP2; EL_MAP2;
               candle_q_dim_interval_row_lookup_in_range]);;

let candle_q_packed_object_interval_list_add_list_of_seq = prove
 (`!n xs ys.
     LENGTH xs = n /\ LENGTH ys = n
     ==>
     candle_q_packed_object_interval_list_add xs ys =
     list_of_seq
       (\i. candle_q_interval_add
         (candle_q_interval_lookup i xs)
         (candle_q_interval_lookup i ys)) n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[candle_q_packed_object_interval_list_add_def;
               LENGTH_MAP2; EL_MAP2; EL_LIST_OF_SEQ;
               candle_q_interval_lookup_in_range]);;

let candle_q_packed_object_interval_matrix_add_list_of_seq = prove
 (`!n xs ys.
     candle_q_dim_interval_matrix_shape n xs /\
     candle_q_dim_interval_matrix_shape n ys
     ==>
     candle_q_packed_object_interval_matrix_add xs ys =
     list_of_seq
       (\i. list_of_seq
         (\j. candle_q_interval_add
           (candle_q_interval_lookup j
             (candle_q_dim_interval_row_lookup i xs))
           (candle_q_interval_lookup j
             (candle_q_dim_interval_row_lookup i ys))) n) n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[candle_q_packed_object_interval_matrix_add_def;
               candle_q_packed_object_interval_list_add_def;
               LENGTH_MAP2; EL_MAP2; EL_LIST_OF_SEQ;
               candle_q_dim_interval_row_lookup_in_range;
               candle_q_interval_lookup_in_range] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH
      (xs:((((num#num)#num)#((num#num)#num))list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < LENGTH
      (ys:((((num#num)#num)#((num#num)#num))list)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (EL i
      (xs:((((num#num)#num)#((num#num)#num))list)list)) = n`
   ASSUME_TAC THENL
   [MP_TAC
      (MATCH_MP
        (SPECL
          [`n:num`;
           `xs:((((num#num)#num)#((num#num)#num))list)list`;
           `i:num`]
          candle_q_dim_interval_rows_width_lookup_length)
        (CONJ
          (ASSUME
            `candle_q_dim_interval_rows_width n
              (xs:((((num#num)#num)#((num#num)#num))list)list)`)
          (ASSUME `i < LENGTH
            (xs:((((num#num)#num)#((num#num)#num))list)list)`))) THEN
    ASM_SIMP_TAC[candle_q_dim_interval_row_lookup_in_range];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (EL i
      (ys:((((num#num)#num)#((num#num)#num))list)list)) = n`
   ASSUME_TAC THENL
   [MP_TAC
      (MATCH_MP
        (SPECL
          [`n:num`;
           `ys:((((num#num)#num)#((num#num)#num))list)list`;
           `i:num`]
          candle_q_dim_interval_rows_width_lookup_length)
        (CONJ
          (ASSUME
            `candle_q_dim_interval_rows_width n
              (ys:((((num#num)#num)#((num#num)#num))list)list)`)
          (ASSUME `i < LENGTH
            (ys:((((num#num)#num)#((num#num)#num))list)list)`))) THEN
    ASM_SIMP_TAC[candle_q_dim_interval_row_lookup_in_range];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_LIST_OF_SEQ;
               EL_MAP2; EL_LIST_OF_SEQ;
               candle_q_interval_lookup_in_range]);;

let candle_q_packed_object_hessian_add_length = prove
 (`!left right.
     LENGTH left = LENGTH right
     ==> LENGTH (candle_q_packed_object_hessian_add left right) =
         LENGTH left`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_hessian_add_def; LENGTH_MAP2]);;

let candle_q_packed_object_hessian_add_expand = prove
 (`!left right.
     LENGTH left = 21 /\ LENGTH right = 21
     ==>
     candle_q_packed_hessian6_expand
       (candle_q_packed_object_hessian_add left right) =
     candle_q_packed_object_interval_matrix_add
       (candle_q_packed_hessian6_expand left)
       (candle_q_packed_hessian6_expand right)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i < 21
        ==> EL i (MAP2 candle_q_interval_add left right) =
            candle_q_interval_add (EL i left) (EL i right)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < LENGTH
        (right:(((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP2];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_packed_object_hessian_add_def;
              candle_q_packed_object_interval_matrix_add_def;
              candle_q_packed_object_interval_list_add_def;
              candle_q_packed_hessian6_expand_def; MAP2] THEN
  let lookup =
    ASSUME
      `!i. i < 21
           ==> EL i (MAP2 candle_q_interval_add left right) =
               candle_q_interval_add (EL i left) (EL i right)` in
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

let candle_q_dim_interval_rows_width_square_list_of_seq = prove
 (`!n m f.
     candle_q_dim_interval_rows_width n
       (list_of_seq
         (\i. list_of_seq
           (f i:num->((num#num)#num)#((num#num)#num)) n) m)`,
  REWRITE_TAC[candle_q_dim_interval_rows_width_all;
              GSYM ALL_EL; LENGTH_LIST_OF_SEQ] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ]);;

let candle_q_dim_jet_exact_add_shape = prove
 (`!n a b.
     candle_q_dim_jet_shape n (candle_q_dim_jet_add n a b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_add_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              LENGTH_LIST_OF_SEQ;
              candle_q_dim_interval_rows_width_square_list_of_seq]);;

let candle_q_dim_jet_exact_add_components_sound = prove
 (`!n a b va vb ga gb ha hb.
     candle_q_dim_jet_contains_components n a va ga ha /\
     candle_q_dim_jet_contains_components n b vb gb hb
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_add n a b)
       (va + vb) (\i. ga i + gb i) (\i j. ha i j + hb i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_add_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[candle_q_dim_jet_add_def;
                   candle_q_dim_jet_gradient_at_def;
                   candle_q_dim_jet_gradient_def;
                   candle_q_dim_jet_make_def; FST; SND;
                   candle_q_interval_lookup_list_of_seq] THEN
      MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
       [MATCH_MP_TAC
          (REWRITE_RULE
            [candle_q_dim_jet_gradient_at_def;
             candle_q_dim_jet_gradient_def]
            (SPEC `i:num`
              (ASSUME
                `!i. i < n
                     ==> candle_q_interval_contains
                           (candle_q_dim_jet_gradient_at a i) (ga i)`))) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC
          (REWRITE_RULE
            [candle_q_dim_jet_gradient_at_def;
             candle_q_dim_jet_gradient_def]
            (SPEC `i:num`
              (ASSUME
                `!i. i < n
                     ==> candle_q_interval_contains
                           (candle_q_dim_jet_gradient_at b i) (gb i)`))) THEN
        ASM_REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[candle_q_dim_jet_add_def;
                   candle_q_dim_jet_hessian_at_def;
                   candle_q_dim_jet_hessian_def;
                   candle_q_dim_jet_make_def; FST; SND;
                   candle_q_interval_lookup_list_of_seq;
                   candle_q_dim_interval_row_lookup_list_of_seq] THEN
      MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
       [MATCH_MP_TAC
          (REWRITE_RULE
            [candle_q_dim_jet_hessian_at_def;
             candle_q_dim_jet_hessian_def]
            (SPECL [`i:num`; `j:num`]
              (ASSUME
                `!i j. i < n /\ j < n
                       ==> candle_q_interval_contains
                             (candle_q_dim_jet_hessian_at a i j)
                             (ha i j)`))) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC
          (REWRITE_RULE
            [candle_q_dim_jet_hessian_at_def;
             candle_q_dim_jet_hessian_def]
            (SPECL [`i:num`; `j:num`]
              (ASSUME
                `!i j. i < n /\ j < n
                       ==> candle_q_interval_contains
                             (candle_q_dim_jet_hessian_at b i j)
                             (hb i j)`))) THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_q_packed_object_box_jet_add = prove
 (`!left_value left_gradient left_hessian
       right_value right_gradient right_hessian.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21
     ==>
     candle_q_packed_object_box_jet
       (candle_q_interval_add left_value right_value)
       (candle_q_packed_object_interval_list_add
         left_gradient right_gradient)
       (candle_q_packed_object_hessian_add left_hessian right_hessian) =
     candle_q_dim_jet_add 6
       (candle_q_packed_object_box_jet
         left_value left_gradient left_hessian)
       (candle_q_packed_object_box_jet
         right_value right_gradient right_hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_add_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  SUBGOAL_THEN
   `candle_q_packed_object_interval_list_add
      left_gradient right_gradient =
    list_of_seq
      (\i. candle_q_interval_add
        (candle_q_interval_lookup i left_gradient)
        (candle_q_interval_lookup i right_gradient)) 6`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_interval_list_add_list_of_seq THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_packed_hessian6_expand
      (candle_q_packed_object_hessian_add left_hessian right_hessian) =
    candle_q_packed_object_interval_matrix_add
      (candle_q_packed_hessian6_expand left_hessian)
      (candle_q_packed_hessian6_expand right_hessian)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_hessian_add_expand THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def; FST; SND] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  MATCH_MP_TAC candle_q_packed_object_interval_matrix_add_list_of_seq THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all;
              candle_q_packed_hessian6_expand_shape]);;

let candle_q_packed_object_center_first_add_contains = prove
 (`!left_value left_gradient left_e
       right_value right_gradient right_e environment.
     LENGTH left_gradient = 6 /\ LENGTH right_gradient = 6 /\
     candle_q_packed_object_center_first_contains
       left_value left_gradient environment left_e /\
     candle_q_packed_object_center_first_contains
       right_value right_gradient environment right_e
     ==>
     candle_q_packed_object_center_first_contains
       (candle_q_interval_add left_value right_value)
       (candle_q_packed_object_interval_list_add
         left_gradient right_gradient)
       environment (Candle_analytic_add left_e right_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_object_center_first_contains_def]) THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_interval_list_add_lookup] THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_MESON_TAC[]]);;

let candle_q_packed_object_box_add_contains = prove
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
         (candle_q_interval_add left_value right_value)
         (candle_q_packed_object_interval_list_add
           left_gradient right_gradient)
         (candle_q_packed_object_hessian_add
           left_hessian right_hessian))
       environment (Candle_analytic_add left_e right_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_packed_object_box_jet
      (candle_q_interval_add left_value right_value)
      (candle_q_packed_object_interval_list_add
        left_gradient right_gradient)
      (candle_q_packed_object_hessian_add left_hessian right_hessian) =
    candle_q_dim_jet_add 6
      (candle_q_packed_object_box_jet
        left_value left_gradient left_hessian)
      (candle_q_packed_object_box_jet
        right_value right_gradient right_hessian)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_box_jet_add THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_dim_analytic_contains_def]) THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  MATCH_MP_TAC candle_q_dim_jet_exact_add_components_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_center_all_add_contains = prove
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
              (Candle_analytic_add left_e right_e) /\
            candle_q_packed_object_center_first_contains
              (candle_q_interval_add left_value right_value)
              (candle_q_packed_object_interval_list_add
                left_gradient right_gradient)
              environment (Candle_analytic_add left_e right_e))`,
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
  (CONJ_TAC THENL
    [(ASM_REWRITE_TAC[candle_analytic_regular_at_def]);
     (MATCH_MP_TAC candle_q_packed_object_center_first_add_contains THEN
      ASM_REWRITE_TAC[])]));;

let candle_q_packed_object_box_all_add_contains = prove
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
              (Candle_analytic_add left_e right_e) /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                (candle_q_interval_add left_value right_value)
                (candle_q_packed_object_interval_list_add
                  left_gradient right_gradient)
                (candle_q_packed_object_hessian_add
                  left_hessian right_hessian))
              environment (Candle_analytic_add left_e right_e))`,
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
  (CONJ_TAC THENL
    [(ASM_REWRITE_TAC[candle_analytic_regular_at_def]);
     (MATCH_MP_TAC candle_q_packed_object_box_add_contains THEN
      ASM_REWRITE_TAC[])]));;

let candle_q_packed_object_item_add_raw_analytic_invariant = prove
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
       (candle_q_interval_add left_center_value right_center_value)
       (candle_q_packed_object_interval_list_add
         left_center_gradient right_center_gradient)
       (candle_q_interval_add left_value_bound right_value_bound)
       (candle_q_packed_object_interval_list_add
         left_gradient_bounds right_gradient_bounds)
       (candle_q_packed_object_hessian_add left_hessian right_hessian)
       (Candle_analytic_add left_center_e right_center_e)
       (Candle_analytic_add left_box_e right_box_e)`,
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
  CONJ_TAC THENL
   [MP_TAC
      (SPECL
        [`left_center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `right_center_gradient:
           (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_interval_list_add_length) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `candle_q_packed_object_box_jet
        (candle_q_interval_add left_value_bound right_value_bound)
        (candle_q_packed_object_interval_list_add
          left_gradient_bounds right_gradient_bounds)
        (candle_q_packed_object_hessian_add
          left_hessian right_hessian) =
      candle_q_dim_jet_add 6
        (candle_q_packed_object_box_jet
          left_value_bound left_gradient_bounds left_hessian)
        (candle_q_packed_object_box_jet
          right_value_bound right_gradient_bounds right_hessian)`
     SUBST1_TAC THENL
     [MATCH_MP_TAC candle_q_packed_object_box_jet_add THEN
      ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC candle_q_dim_jet_exact_add_shape];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(MATCH_MP_TAC candle_q_packed_object_center_all_add_contains THEN
     ASM_REWRITE_TAC[]);
    (MATCH_MP_TAC candle_q_packed_object_box_all_add_contains THEN
     ASM_REWRITE_TAC[])]);;

let candle_q_packed_object_item_add_analytic_invariant = prove
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
       (candle_q_interval_add left_center_value right_center_value)
       (candle_q_packed_object_interval_list_add
         left_center_gradient right_center_gradient)
       (candle_q_packed_object_value_bound6 radii
         (candle_q_interval_add left_center_value right_center_value)
         (candle_q_packed_object_interval_list_add
           left_center_gradient right_center_gradient)
         (candle_q_packed_object_hessian_add
           left_hessian right_hessian))
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_packed_object_interval_list_add
           left_center_gradient right_center_gradient)
         (candle_q_packed_object_hessian_add
           left_hessian right_hessian))
       (candle_q_packed_object_hessian_add left_hessian right_hessian)
       (Candle_analytic_add left_center_e right_center_e)
       (Candle_analytic_add left_box_e right_box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
         (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`;
       `left_domain /\ right_domain`;
       `candle_q_interval_add left_center_value right_center_value`;
       `candle_q_packed_object_interval_list_add
          left_center_gradient right_center_gradient`;
       `candle_q_interval_add left_value_bound right_value_bound`;
       `candle_q_packed_object_interval_list_add
          left_gradient_bounds right_gradient_bounds`;
       `candle_q_packed_object_hessian_add left_hessian right_hessian`;
       `Candle_analytic_add left_center_e right_center_e`;
       `Candle_analytic_add left_box_e right_box_e`]
      candle_q_packed_object_item_recomplete_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_packed_object_item_add_raw_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_interval_list_add_length;
     candle_q_packed_object_interval_list_add_lookup;
     candle_q_packed_object_interval_list_add_list_of_seq;
     candle_q_packed_object_interval_matrix_add_length;
     candle_q_packed_object_interval_matrix_add_row_lookup;
     candle_q_packed_object_interval_matrix_add_list_of_seq;
     candle_q_packed_object_hessian_add_length;
     candle_q_packed_object_hessian_add_expand;
     candle_q_dim_interval_rows_width_square_list_of_seq;
     candle_q_dim_jet_exact_add_shape;
     candle_q_dim_jet_exact_add_components_sound;
     candle_q_packed_object_box_jet_add;
     candle_q_packed_object_center_first_add_contains;
     candle_q_packed_object_box_add_contains;
     candle_q_packed_object_center_all_add_contains;
     candle_q_packed_object_box_all_add_contains;
     candle_q_packed_object_item_add_raw_analytic_invariant;
     candle_q_packed_object_item_add_analytic_invariant] then
  failwith "packed source object add sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ADD_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
