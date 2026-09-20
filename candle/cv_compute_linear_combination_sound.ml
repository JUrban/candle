(* ========================================================================== *)
(* Generic soundness for bulk nonnegative real linear combinations.           *)
(*                                                                            *)
(* This theorem layer is independent of cval evaluation. The later Flyspeck  *)
(* adapter must prove that its authenticated inequalities instantiate these   *)
(* premises and that the computed normalized map denotes the same real sum.   *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_core.ml";;

module Candle_cv_linear_combination_sound = struct

let candle_lc_real_accumulate_def = new_definition
 `candle_lc_real_accumulate
    (acc:real#real) (lcrow:num#(real#real)) =
    (FST acc + &(FST lcrow) * FST (SND lcrow),
     SND acc + &(FST lcrow) * SND (SND lcrow))`;;

let candle_lc_real_fold_def = define
 `(candle_lc_real_fold (acc:real#real) [] = acc) /\
  (candle_lc_real_fold acc (CONS (lcrow:num#(real#real)) rows) =
     candle_lc_real_fold (candle_lc_real_accumulate acc lcrow) rows)`;;

let candle_lc_real_row_holds_def = new_definition
 `candle_lc_real_row_holds (lcrow:num#(real#real)) <=>
    FST (SND lcrow) <= SND (SND lcrow)`;;

let candle_lc_real_accumulate_sound = prove
 (`!acc lcrow.
     FST acc <= SND acc /\ candle_lc_real_row_holds lcrow
     ==> FST (candle_lc_real_accumulate acc lcrow) <=
         SND (candle_lc_real_accumulate acc lcrow)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_real_accumulate_def;
              candle_lc_real_row_holds_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_POS]);;

let candle_lc_real_fold_sound = prove
 (`!rows acc.
     FST acc <= SND acc /\ ALL candle_lc_real_row_holds rows
     ==> FST (candle_lc_real_fold acc rows) <=
         SND (candle_lc_real_fold acc rows)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_lc_real_fold_def; ALL];
    ASM_REWRITE_TAC[candle_lc_real_fold_def; ALL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_lc_real_accumulate_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_lc_real_fold_from_zero = prove
 (`!rows.
     ALL candle_lc_real_row_holds rows
     ==> FST (candle_lc_real_fold (&0,&0) rows) <=
         SND (candle_lc_real_fold (&0,&0) rows)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC candle_lc_real_fold_sound THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

end;;
