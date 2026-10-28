(* ========================================================================== *)
(* Exact compact Hessian of the Flyspeck delta polynomial.                    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The optimized word checker stores the upper   *)
(* triangle in the order 00,01,...,05,11,...,55.  This ordinary operation     *)
(* mirrors its exact object-rational witness and proves all 21 entries sound  *)
(* together, rather than as coordinate-specific special cases.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_value.ml";;

module Candle_cv_analytic_expr_packed_source_delta_hessian = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_packed_source_delta_value;;

let candle_q_packed_delta_sums_def = define
 `(candle_q_packed_delta_sums [] = []) /\
  (candle_q_packed_delta_sums (CONS interval_head interval_tail) =
     CONS (candle_q_packed_delta_sum interval_head)
       (candle_q_packed_delta_sums interval_tail))`;;

let candle_real_packed_delta_sums_def = define
 `(candle_real_packed_delta_sums [] = []) /\
  (candle_real_packed_delta_sums (CONS real_head real_tail) =
     CONS (candle_real_packed_delta_sum real_head)
       (candle_real_packed_delta_sums real_tail))`;;

let candle_cv_q_packed_delta_sums_def = define
 `(candle_cv_q_packed_delta_sums (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_packed_delta_sums (Cexp_pair row_value row_lists) =
     Cexp_pair (candle_cv_q_packed_delta_sum row_value)
       (candle_cv_q_packed_delta_sums row_lists))`;;

let candle_cv_q_packed_delta_sums_correct = prove
 (`!row_lists.
     candle_cv_q_packed_delta_sums
       (candle_cv_q_interval_matrix row_lists) =
     candle_cv_q_interval_list (candle_q_packed_delta_sums row_lists)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_matrix_def;
                  candle_cv_q_interval_list_def;
                  candle_cv_q_packed_delta_sums_def;
                  candle_q_packed_delta_sums_def;
                  candle_cv_q_packed_delta_sum_correct]);;

let candle_q_packed_delta_sums_sound = prove
 (`!interval_rows real_rows.
     ALL2 (ALL2 candle_q_interval_contains) interval_rows real_rows
     ==>
     ALL2 candle_q_interval_contains
       (candle_q_packed_delta_sums interval_rows)
       (candle_real_packed_delta_sums real_rows)`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `real_rows:(real list)list` THEN
    MP_TAC (ISPEC `real_rows:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `value:real list`
          (X_CHOOSE_THEN `rest:(real list)list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; candle_q_packed_delta_sums_def;
                candle_real_packed_delta_sums_def];
    POP_ASSUM (LABEL_TAC "sums_ih") THEN
    X_GEN_TAC `real_rows:(real list)list` THEN
    MP_TAC (ISPEC `real_rows:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `value:real list`
          (X_CHOOSE_THEN `rest:(real list)list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; candle_q_packed_delta_sums_def;
                candle_real_packed_delta_sums_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "head_relation")
        (LABEL_TAC "tail_relation")) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_packed_delta_sum_sound THEN
      USE_THEN "head_relation" ACCEPT_TAC;
      USE_THEN "sums_ih" MATCH_MP_TAC THEN
      USE_THEN "tail_relation" ACCEPT_TAC]]);;

let candle_q_packed_delta_hessian_rows_six_def = new_definition
 `candle_q_packed_delta_hessian_rows_six x0 x1 x2 x3 x4 x5 =
    let n0 = candle_q_interval_neg x0 in
    let n1 = candle_q_interval_neg x1 in
    let n2 = candle_q_interval_neg x2 in
    let n3 = candle_q_interval_neg x3 in
    let n4 = candle_q_interval_neg x4 in
    let n5 = candle_q_interval_neg x5 in
    [[n3;n3];
     [x3;x4;n5];
     [x3;n4;x5];
     [n0;n0;x1;x2;n3;n3;x4;x5];
     [x1;n2;x3];
     [n1;x2;x3];
     [n4;n4];
     [n3;x4;x5];
     [x0;n2;x4];
     [x0;n1;n1;x2;x3;n4;n4;x5];
     [n0;x2;x4];
     [n5;n5];
     [x0;n1;x5];
     [n0;x1;x5];
     [x0;x1;n2;n2;x3;x4;n5;n5];
     [n0;n0];
     [x0;x1;n5];
     [x0;x2;n4];
     [n1;n1];
     [x1;x2;n3];
     [n2;n2]]`;;

let candle_real_packed_delta_hessian_rows_six_def = new_definition
 `candle_real_packed_delta_hessian_rows_six v0 v1 v2 v3 v4 v5 =
    [[--v3;--v3];
     [v3;v4;--v5];
     [v3;--v4;v5];
     [--v0;--v0;v1;v2;--v3;--v3;v4;v5];
     [v1;--v2;v3];
     [--v1;v2;v3];
     [--v4;--v4];
     [--v3;v4;v5];
     [v0;--v2;v4];
     [v0;--v1;--v1;v2;v3;--v4;--v4;v5];
     [--v0;v2;v4];
     [--v5;--v5];
     [v0;--v1;v5];
     [--v0;v1;v5];
     [v0;v1;--v2;--v2;v3;v4;--v5;--v5];
     [--v0;--v0];
     [v0;v1;--v5];
     [v0;v2;--v4];
     [--v1;--v1];
     [v1;v2;--v3];
     [--v2;--v2]]`;;

let candle_q_packed_delta_hessian_six_def = new_definition
 `candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5 =
    candle_q_packed_delta_sums
      (candle_q_packed_delta_hessian_rows_six x0 x1 x2 x3 x4 x5)`;;

let candle_real_packed_delta_hessian_six_def = new_definition
 `candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5 =
    candle_real_packed_delta_sums
      (candle_real_packed_delta_hessian_rows_six v0 v1 v2 v3 v4 v5)`;;

let candle_q_packed_delta_hessian_rows_six_sound = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5
     ==>
     ALL2 (ALL2 candle_q_interval_contains)
       (candle_q_packed_delta_hessian_rows_six x0 x1 x2 x3 x4 x5)
       (candle_real_packed_delta_hessian_rows_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_hessian_rows_six_def;
              candle_real_packed_delta_hessian_rows_six_def;
              LET_DEF; LET_END_DEF; ALL2] THEN
  ASM_SIMP_TAC[candle_q_interval_neg_sound]);;

let candle_q_packed_delta_hessian_six_sound = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5
     ==>
     ALL2 candle_q_interval_contains
       (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)
       (candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_hessian_six_def;
              candle_real_packed_delta_hessian_six_def] THEN
  MATCH_MP_TAC candle_q_packed_delta_sums_sound THEN
  MATCH_MP_TAC candle_q_packed_delta_hessian_rows_six_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_packed_delta_two_def = new_definition
 `candle_cv_q_packed_delta_two a b =
    Cexp_pair a (Cexp_pair b (Cexp_num 0))`;;

let candle_cv_q_packed_delta_three_def = new_definition
 `candle_cv_q_packed_delta_three a b c =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_num 0)))`;;

let candle_cv_q_packed_delta_eight_def = new_definition
 `candle_cv_q_packed_delta_eight a b c d e f g h =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_pair d
      (Cexp_pair e (Cexp_pair f (Cexp_pair g
        (Cexp_pair h (Cexp_num 0))))))))`;;

let candle_cv_q_packed_delta_two_correct = prove
 (`!a b.
     candle_cv_q_packed_delta_two
       (candle_cv_q_interval a) (candle_cv_q_interval b) =
     candle_cv_q_interval_list [a;b]`,
  REWRITE_TAC[candle_cv_q_packed_delta_two_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_packed_delta_three_correct = prove
 (`!a b c.
     candle_cv_q_packed_delta_three
       (candle_cv_q_interval a) (candle_cv_q_interval b)
       (candle_cv_q_interval c) =
     candle_cv_q_interval_list [a;b;c]`,
  REWRITE_TAC[candle_cv_q_packed_delta_three_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_packed_delta_eight_correct = prove
 (`!a b c d e f g h.
     candle_cv_q_packed_delta_eight
       (candle_cv_q_interval a) (candle_cv_q_interval b)
       (candle_cv_q_interval c) (candle_cv_q_interval d)
       (candle_cv_q_interval e) (candle_cv_q_interval f)
       (candle_cv_q_interval g) (candle_cv_q_interval h) =
     candle_cv_q_interval_list [a;b;c;d;e;f;g;h]`,
  REWRITE_TAC[candle_cv_q_packed_delta_eight_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_packed_delta_hessian_rows_six_def = new_definition
 `candle_cv_q_packed_delta_hessian_rows_six x0 x1 x2 x3 x4 x5 =
    let n0 = candle_cv_q_interval_neg x0 in
    let n1 = candle_cv_q_interval_neg x1 in
    let n2 = candle_cv_q_interval_neg x2 in
    let n3 = candle_cv_q_interval_neg x3 in
    let n4 = candle_cv_q_interval_neg x4 in
    let n5 = candle_cv_q_interval_neg x5 in
    let row_lists = Cexp_num 0 in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_two n2 n2) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x1 x2 n3) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_two n1 n1) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x0 x2 n4) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x0 x1 n5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_two n0 n0) row_lists in
    let row_lists = Cexp_pair
      (candle_cv_q_packed_delta_eight x0 x1 n2 n2 x3 x4 n5 n5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three n0 x1 x5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x0 n1 x5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_two n5 n5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three n0 x2 x4) row_lists in
    let row_lists = Cexp_pair
      (candle_cv_q_packed_delta_eight x0 n1 n1 x2 x3 n4 n4 x5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x0 n2 x4) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three n3 x4 x5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_two n4 n4) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three n1 x2 x3) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x1 n2 x3) row_lists in
    let row_lists = Cexp_pair
      (candle_cv_q_packed_delta_eight n0 n0 x1 x2 n3 n3 x4 x5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x3 n4 x5) row_lists in
    let row_lists = Cexp_pair (candle_cv_q_packed_delta_three x3 x4 n5) row_lists in
    Cexp_pair (candle_cv_q_packed_delta_two n3 n3) row_lists`;;

let candle_cv_q_packed_delta_hessian_rows_six_correct = prove
 (`!x0 x1 x2 x3 x4 x5.
     candle_cv_q_packed_delta_hessian_rows_six
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_interval_matrix
       (candle_q_packed_delta_hessian_rows_six x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_delta_hessian_rows_six_def;
              candle_q_packed_delta_hessian_rows_six_def;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_packed_delta_two_correct;
              candle_cv_q_packed_delta_three_correct;
              candle_cv_q_packed_delta_eight_correct;
              candle_cv_q_interval_matrix_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_q_packed_delta_hessian_six_def = new_definition
 `candle_cv_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5 =
    candle_cv_q_packed_delta_sums
      (candle_cv_q_packed_delta_hessian_rows_six x0 x1 x2 x3 x4 x5)`;;

let candle_cv_q_packed_delta_hessian_six_correct = prove
 (`!x0 x1 x2 x3 x4 x5.
     candle_cv_q_packed_delta_hessian_six
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_delta_hessian_six_def;
              candle_q_packed_delta_hessian_six_def;
              candle_cv_q_packed_delta_hessian_rows_six_correct;
              candle_cv_q_packed_delta_sums_correct]);;

let candle_cv_q_packed_source_delta_hessian_compute_eqs =
  candle_cv_q_packed_source_delta_value_compute_eqs @
  map SPEC_ALL
    [candle_cv_q_packed_delta_sums_def;
     candle_cv_q_packed_delta_two_def;
     candle_cv_q_packed_delta_three_def;
     candle_cv_q_packed_delta_eight_def;
     candle_cv_q_packed_delta_hessian_rows_six_def;
     candle_cv_q_packed_delta_hessian_six_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_delta_sums_correct;
     candle_q_packed_delta_sums_sound;
     candle_q_packed_delta_hessian_rows_six_sound;
     candle_q_packed_delta_hessian_six_sound;
     candle_cv_q_packed_delta_two_correct;
     candle_cv_q_packed_delta_three_correct;
     candle_cv_q_packed_delta_eight_correct;
     candle_cv_q_packed_delta_hessian_rows_six_correct;
     candle_cv_q_packed_delta_hessian_six_correct] then
  failwith "packed source delta Hessian: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_HESSIAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
