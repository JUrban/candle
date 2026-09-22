(* ========================================================================== *)
(* Real denotation and soundness bridge for sparse LP certificate arithmetic. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. This layer proves that sparse insertion, merge, *)
(* scaling, and folding preserve the weighted real linear combination.        *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_sparse_verdict.ml";;
needs "candle/cv_compute_linear_combination_realize.ml";;

module Candle_cv_linear_combination_sparse_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_sound;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_linear_combination_sparse_verdict;;

let candle_lc_sparse_vec_real_def = define
 `(candle_lc_sparse_vec_real (variables:real list)
      ([]:(num#(num#num))list) = &0) /\
  (candle_lc_sparse_vec_real variables (CONS (index,z) entries) =
     candle_lc_zreal z * EL index variables +
     candle_lc_sparse_vec_real variables entries)`;;

let candle_lc_sparse_vec_real_cons = prove
 (`!variables x entries.
     candle_lc_sparse_vec_real variables (CONS x entries) =
     candle_lc_zreal (SND x) * EL (FST x) variables +
     candle_lc_sparse_vec_real variables entries`,
  REWRITE_TAC[FORALL_PAIR_THM;
              CONJUNCT2 candle_lc_sparse_vec_real_def; FST; SND]);;

let candle_lc_sparse_acc_real_def = new_definition
 `candle_lc_sparse_acc_real (variables:real list)
     (acc:(num#(num#num))list#(num#num)) =
    (candle_lc_sparse_vec_real variables (FST acc),
     candle_lc_zreal (SND acc))`;;

let candle_lc_sparse_row_real_def = new_definition
 `candle_lc_sparse_row_real (variables:real list)
     (lcrow:num#((num#(num#num))list#(num#num))) =
    (FST lcrow,
     (candle_lc_sparse_vec_real variables (FST (SND lcrow)),
      candle_lc_zreal (SND (SND lcrow))))`;;

let candle_lc_sparse_insert_real = prove
 (`!variables x entries.
     candle_lc_sparse_vec_real variables
       (candle_lc_sparse_insert x entries) =
     candle_lc_zreal (SND x) * EL (FST x) variables +
     candle_lc_sparse_vec_real variables entries`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`entries:(num#(num#num))list`,
            `entries:(num#(num#num))list`) THEN
  LIST_INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_insert_def] THEN
    REWRITE_TAC[CONJUNCT1 candle_lc_sparse_vec_real_def;
                candle_lc_sparse_vec_real_cons;
                FST; SND; REAL_ADD_RID];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_insert_def] THEN
    ASM_CASES_TAC
      `FST (x:num#(num#num)) < FST (h:num#(num#num))` THEN
    ASM_CASES_TAC
      `FST (h:num#(num#num)) < FST (x:num#(num#num))` THEN
    ASM_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_vec_real_def;
                    candle_lc_sparse_vec_real_cons;
                    FST; SND; candle_lc_zreal_add] THEN
    TRY ASM_ARITH_TAC THEN
    MP_TAC (SPECL [`FST (x:num#(num#num))`;
                   `FST (h:num#(num#num))`] candle_lc_num_order_eq) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let candle_lc_sparse_add_real = prove
 (`!variables xs ys.
     candle_lc_sparse_vec_real variables (candle_lc_sparse_add xs ys) =
     candle_lc_sparse_vec_real variables xs +
     candle_lc_sparse_vec_real variables ys`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_add_def] THEN
    REWRITE_TAC[candle_lc_sparse_vec_real_def; REAL_ADD_LID];
    GEN_TAC THEN
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_add_def] THEN
    ASM_REWRITE_TAC[candle_lc_sparse_insert_real;
                    candle_lc_sparse_vec_real_cons] THEN
    REAL_ARITH_TAC]);;

let candle_lc_sparse_scale_real = prove
 (`!variables k entries.
     candle_lc_sparse_vec_real variables
       (candle_lc_sparse_scale k entries) =
     &k * candle_lc_sparse_vec_real variables entries`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_scale_def] THEN
    REWRITE_TAC[candle_lc_sparse_vec_real_def; REAL_MUL_RZERO];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_scale_def] THEN
    ASM_REWRITE_TAC[candle_lc_sparse_vec_real_cons;
                    candle_lc_zreal_scale; FST; SND] THEN
    REAL_ARITH_TAC]);;

let candle_lc_sparse_accumulate_real = prove
 (`!variables acc lcrow.
     candle_lc_sparse_acc_real variables
       (candle_lc_sparse_accumulate acc lcrow) =
     candle_lc_real_accumulate
       (candle_lc_sparse_acc_real variables acc)
       (candle_lc_sparse_row_real variables lcrow)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_sparse_acc_real_def;
              candle_lc_sparse_row_real_def;
              candle_lc_sparse_accumulate_def;
              candle_lc_real_accumulate_def;
              candle_lc_sparse_add_real;
              candle_lc_sparse_scale_real;
              candle_lc_zreal_add;
              candle_lc_zreal_scale]);;

let candle_lc_sparse_fold_real = prove
 (`!lcrows variables acc.
     candle_lc_real_fold
       (candle_lc_sparse_acc_real variables acc)
       (MAP (candle_lc_sparse_row_real variables) lcrows) =
     candle_lc_sparse_acc_real variables
       (candle_lc_sparse_fold acc lcrows)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_fold_def] THEN
    REWRITE_TAC[MAP; candle_lc_real_fold_def];
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_fold_def] THEN
    REWRITE_TAC[MAP; candle_lc_real_fold_def] THEN
    ONCE_REWRITE_TAC[GSYM candle_lc_sparse_accumulate_real] THEN
    ASM_REWRITE_TAC[]]);;

let candle_lc_sparse_zero_real = prove
 (`!variables entries.
     candle_lc_sparse_zero entries
     ==> candle_lc_sparse_vec_real variables entries = &0`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_lc_sparse_vec_real_def];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_zero_def] THEN
    REWRITE_TAC[candle_lc_sparse_vec_real_cons] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[candle_lc_zreal_def; REAL_SUB_REFL;
                    REAL_MUL_LZERO; REAL_ADD_LID] THEN
    ASM_MESON_TAC[]]);;

let candle_lc_sparse_rhs_negative = prove
 (`!rhs:num#num.
     FST rhs < SND rhs ==> candle_lc_zreal rhs < &0`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_lc_zreal_def; FST; SND] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC);;

let candle_lc_sparse_zero_acc_real = prove
 (`!variables.
     candle_lc_sparse_acc_real variables
       (([]:(num#(num#num))list),(0,0)) = (&0,&0)`,
  REWRITE_TAC[candle_lc_sparse_acc_real_def;
              candle_lc_sparse_vec_real_def;
              candle_lc_zreal_def; FST; SND; REAL_SUB_REFL]);;

let candle_lc_sparse_infeasible_sound = prove
 (`!variables lcrows.
     candle_lc_sparse_infeasible
       (candle_lc_sparse_fold
         (([]:(num#(num#num))list),(0,0)) lcrows)
     ==> ~ALL candle_lc_real_row_holds
          (MAP (candle_lc_sparse_row_real variables) lcrows)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_sparse_infeasible_def] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC
    (SPEC `MAP (candle_lc_sparse_row_real (variables:real list)) lcrows`
      candle_lc_real_fold_from_zero) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM (SPEC `variables:real list`
    candle_lc_sparse_zero_acc_real)] THEN
  REWRITE_TAC[candle_lc_sparse_fold_real;
              candle_lc_sparse_acc_real_def; FST; SND] THEN
  MP_TAC
    (SPECL
      [`variables:real list`;
       `FST (candle_lc_sparse_fold
         (([]:(num#(num#num))list),(0,0)) lcrows)`]
      candle_lc_sparse_zero_real) THEN
  MP_TAC
    (SPEC
      `SND (candle_lc_sparse_fold
        (([]:(num#(num#num))list),(0,0)) lcrows)`
      candle_lc_sparse_rhs_negative) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_cv_lc_sparse_fold_verdict_sound = prove
 (`!variables lcrows.
     candle_cv_lc_sparse_fold_verdict
       (candle_cv_lc_sparse_acc
         (([]:(num#(num#num))list),(0,0)))
       (candle_cv_lc_sparse_rows lcrows) = Cexp_num (SUC 0)
     ==> ~ALL candle_lc_real_row_holds
          (MAP (candle_lc_sparse_row_real variables) lcrows)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC
    `candle_lc_sparse_infeasible
      (candle_lc_sparse_fold
        (([]:(num#(num#num))list),(0,0)) lcrows)` THENL
   [ASM_REWRITE_TAC[candle_cv_lc_sparse_fold_verdict_correct;
                    injectivity "cval"] THEN
    MP_TAC
      (SPECL
        [`variables:real list`;
         `lcrows:(num#((num#(num#num))list#(num#num)))list`]
        candle_lc_sparse_infeasible_sound) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_cv_lc_sparse_fold_verdict_correct;
                    injectivity "cval"] THEN ARITH_TAC]);;

end;;
