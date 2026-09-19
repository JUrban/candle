(* ========================================================================== *)
(* Real denotation of the exact coefficient accumulator.                     *)
(*                                                                            *)
(* This is the checked bridge between the natural-pair computation and the   *)
(* generic real inequality fold. No parsing or theorem construction is       *)
(* trusted here: every compatibility equation is proved in HOL.              *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_sound.ml";;

module Candle_cv_linear_combination_realize = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_sound;;

let candle_lc_zreal_def = new_definition
 `candle_lc_zreal (z:num#num) = &(FST z) - &(SND z)`;;

let candle_lc_vec_real_def = define
 `(candle_lc_vec_real ([]:real list) ([]:(num#num)list) = &0) /\
  (candle_lc_vec_real [] (CONS z zs) = &0) /\
  (candle_lc_vec_real (CONS x xs) [] = &0) /\
  (candle_lc_vec_real (CONS x xs) (CONS z zs) =
     candle_lc_zreal z * x + candle_lc_vec_real xs zs)`;;

let candle_lc_acc_real_def = new_definition
 `candle_lc_acc_real (variables:real list)
                     (acc:(num#num)list#(num#num)) =
    (candle_lc_vec_real variables (FST acc),
     candle_lc_zreal (SND acc))`;;

let candle_lc_row_real_def = new_definition
 `candle_lc_row_real (variables:real list)
                     (row:num#((num#num)list#(num#num))) =
    (FST row,
     (candle_lc_vec_real variables (FST (SND row)),
      candle_lc_zreal (SND (SND row))))`;;

let candle_lc_zreal_add = prove
 (`!x y. candle_lc_zreal (candle_lc_zadd x y) =
         candle_lc_zreal x + candle_lc_zreal y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_zreal_def; candle_lc_zadd_def;
              GSYM REAL_OF_NUM_ADD; real_sub; REAL_NEG_ADD;
              REAL_ADD_AC]);;

let candle_lc_zreal_scale = prove
 (`!k x. candle_lc_zreal (candle_lc_zscale k x) =
         &k * candle_lc_zreal x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_zreal_def; candle_lc_zscale_def;
              GSYM REAL_OF_NUM_MUL; REAL_SUB_LDISTRIB]);;

let candle_lc_vec_real_add = prove
 (`!variables xs ys.
     candle_lc_vec_real variables (candle_lc_vec_add xs ys) =
     candle_lc_vec_real variables xs + candle_lc_vec_real variables ys`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `xs:(num#num)list` list_CASES) THEN
    MP_TAC (ISPEC `ys:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_lc_vec_add_def; candle_lc_vec_real_def;
                REAL_ADD_LID; REAL_ADD_RID];
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `xs:(num#num)list` list_CASES) THEN
    MP_TAC (ISPEC `ys:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_lc_vec_add_def; candle_lc_vec_real_def;
                    candle_lc_zreal_add; REAL_ADD_RDISTRIB;
                    REAL_ADD_AC; REAL_ADD_RID]]);;

let candle_lc_vec_real_scale = prove
 (`!variables k xs.
     candle_lc_vec_real variables (candle_lc_vec_scale k xs) =
     &k * candle_lc_vec_real variables xs`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `xs:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_lc_vec_scale_def; candle_lc_vec_real_def;
                REAL_MUL_RZERO];
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `xs:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_lc_vec_scale_def; candle_lc_vec_real_def;
                    candle_lc_zreal_scale; REAL_ADD_LDISTRIB;
                    REAL_MUL_ASSOC; REAL_MUL_RZERO]]);;

let candle_lc_accumulate_real = prove
 (`!variables acc row.
     candle_lc_acc_real variables (candle_lc_accumulate acc row) =
     candle_lc_real_accumulate
       (candle_lc_acc_real variables acc)
       (candle_lc_row_real variables row)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_acc_real_def; candle_lc_row_real_def;
              candle_lc_accumulate_def; candle_lc_real_accumulate_def;
              candle_lc_vec_real_add; candle_lc_vec_real_scale;
              candle_lc_zreal_add; candle_lc_zreal_scale]);;

let candle_lc_fold_real_reverse = prove
 (`!rows variables acc.
     candle_lc_acc_real variables (candle_lc_fold acc rows) =
     candle_lc_real_fold
       (candle_lc_acc_real variables acc)
       (MAP (candle_lc_row_real variables) rows)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[MAP; candle_lc_real_fold_def; candle_lc_fold_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[MAP; candle_lc_real_fold_def; candle_lc_fold_def] THEN
    ONCE_REWRITE_TAC[GSYM candle_lc_accumulate_real] THEN
    ASM_MESON_TAC[]]);;

let candle_lc_fold_real = prove
 (`!rows variables acc.
     candle_lc_real_fold
       (candle_lc_acc_real variables acc)
       (MAP (candle_lc_row_real variables) rows) =
     candle_lc_acc_real variables (candle_lc_fold acc rows)`,
  MESON_TAC[candle_lc_fold_real_reverse]);;

end;;
