(* ========================================================================== *)
(* Historical supplied roots: reflected exact square-bound checker.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_root_certificate_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_compute = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_sound;;

let candle_fs_hist_root_certificate_def = new_definition
 `candle_fs_hist_root_certificate input_lower input_upper
      root_lower root_upper <=>
    0 < input_lower /\ input_lower <= input_upper /\
    0 < root_lower /\ root_lower <= root_upper /\
    root_lower * root_lower <= input_lower * candle_fs_scale /\
    input_upper * candle_fs_scale <= root_upper * root_upper`;;

let candle_cv_fs_hist_bool_not_def = new_definition
 `candle_cv_fs_hist_bool_not value =
    Cexp_if value (Cexp_num 0) (Cexp_num 1)`;;

let candle_cv_fs_hist_bool_and_def = new_definition
 `candle_cv_fs_hist_bool_and left right =
    Cexp_if left right (Cexp_num 0)`;;

let candle_cv_fs_hist_num_le_def = new_definition
 `candle_cv_fs_hist_num_le left right =
    candle_cv_fs_hist_bool_not (Cexp_less right left)`;;

let candle_cv_fs_hist_bool_not_correct = prove
 (`!b. candle_cv_fs_hist_bool_not (candle_cv_bool b) =
       candle_cv_bool (~b)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_bool_not_def; candle_cv_bool_def] THEN
  MP_TAC (ARITH_RULE `1 = SUC 0`) THEN DISCH_THEN SUBST1_TAC THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_SIMP_TAC[cexp_if_def; NOT_CLAUSES; COND_CLAUSES]);;

let candle_cv_fs_hist_bool_and_correct = prove
 (`!a b.
     candle_cv_fs_hist_bool_and (candle_cv_bool a) (candle_cv_bool b) =
     candle_cv_bool (a /\ b)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `a:bool` THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[candle_cv_fs_hist_bool_and_def; candle_cv_bool_def;
                  cexp_if_def]);;

let candle_cv_fs_hist_num_less_correct = prove
 (`!left right.
     Cexp_less (Cexp_num left) (Cexp_num right) =
     candle_cv_bool (left < right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_less_def; candle_cv_bool_def]);;

let candle_cv_fs_hist_num_equal_correct = prove
 (`!left right.
     Cexp_eq (Cexp_num left) (Cexp_num right) =
     candle_cv_bool (left = right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_eq_def; candle_cv_bool_def; injectivity "cval"]);;

let candle_cv_fs_hist_num_ispair_correct = prove
 (`!value. Cexp_ispair (Cexp_num value) = candle_cv_bool F`,
  REWRITE_TAC[cexp_ispair_def; candle_cv_bool_def]);;

let candle_cv_fs_hist_pair_ispair_correct = prove
 (`!left right. Cexp_ispair (Cexp_pair left right) = candle_cv_bool T`,
  REWRITE_TAC[cexp_ispair_def; candle_cv_bool_def]);;

let candle_cv_fs_hist_num_le_correct = prove
 (`!left right.
     candle_cv_fs_hist_num_le (Cexp_num left) (Cexp_num right) =
     candle_cv_bool (left <= right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_num_le_def;
              candle_cv_fs_hist_num_less_correct;
              candle_cv_fs_hist_bool_not_correct; NOT_LT]);;

(* [input] is produced internally by the fixed-scale evaluator.  [root_value] is
   untrusted certificate data, so the shape checks below fail closed before
   its four numeric leaves may authorize the exact comparisons. *)

let candle_cv_fs_hist_root_certificate_def = new_definition
 `candle_cv_fs_hist_root_certificate input root_value =
    let input_lower = Cexp_fst (Cexp_fst input) in
    let input_upper = Cexp_fst (Cexp_snd input) in
    let root_lower_pair = Cexp_fst root_value in
    let root_upper_pair = Cexp_snd root_value in
    let root_lower = Cexp_fst root_lower_pair in
    let root_upper = Cexp_fst root_upper_pair in
    let root_shape =
      candle_cv_fs_hist_bool_and (Cexp_ispair root_value)
       (candle_cv_fs_hist_bool_and (Cexp_ispair root_lower_pair)
        (candle_cv_fs_hist_bool_and (Cexp_ispair root_upper_pair)
         (candle_cv_fs_hist_bool_and
           (candle_cv_fs_hist_bool_not (Cexp_ispair root_lower))
          (candle_cv_fs_hist_bool_and
           (candle_cv_fs_hist_bool_not (Cexp_ispair root_upper))
          (candle_cv_fs_hist_bool_and
           (Cexp_eq (Cexp_snd root_lower_pair) (Cexp_num 0))
           (Cexp_eq (Cexp_snd root_upper_pair) (Cexp_num 0))))))) in
    candle_cv_fs_hist_bool_and root_shape
     (candle_cv_fs_hist_bool_and
       (Cexp_less (Cexp_num 0) input_lower)
      (candle_cv_fs_hist_bool_and
       (candle_cv_fs_hist_num_le input_lower input_upper)
      (candle_cv_fs_hist_bool_and
       (Cexp_less (Cexp_num 0) root_lower)
      (candle_cv_fs_hist_bool_and
       (candle_cv_fs_hist_num_le root_lower root_upper)
      (candle_cv_fs_hist_bool_and
       (candle_cv_fs_hist_num_le
         (Cexp_mul root_lower root_lower)
         (Cexp_mul input_lower candle_cv_fs_scale))
       (candle_cv_fs_hist_num_le
         (Cexp_mul input_upper candle_cv_fs_scale)
         (Cexp_mul root_upper root_upper)))))))`;;

let candle_cv_fs_hist_root_certificate_correct = prove
 (`!input_lower input_upper root_lower root_upper.
     candle_cv_fs_hist_root_certificate
       (candle_cv_fs_interval
         ((input_lower,0),(input_upper,0)))
       (candle_cv_fs_interval
         ((root_lower,0),(root_upper,0))) =
     Cexp_num
       (if candle_fs_hist_root_certificate input_lower input_upper
             root_lower root_upper
        then 1 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_root_certificate_def;
              candle_fs_hist_root_certificate_def;
              candle_cv_fs_interval_def;
              candle_cv_lc_z_def;
              candle_cv_fs_scale_correct;
              cexp_fst_def; cexp_snd_def; cexp_mul_def;
              candle_cv_fs_hist_num_ispair_correct;
              candle_cv_fs_hist_pair_ispair_correct;
              candle_cv_fs_hist_num_equal_correct;
              candle_cv_fs_hist_bool_not_correct;
              candle_cv_fs_hist_bool_and_correct;
              candle_cv_fs_hist_num_less_correct;
              candle_cv_fs_hist_num_le_correct;
              candle_cv_bool_def;
              ARITH_RULE `1 = SUC 0`;
              LET_DEF; LET_END_DEF; injectivity "cval"] THEN
  REWRITE_TAC[candle_cv_fs_hist_bool_not_def;
              candle_cv_fs_hist_bool_and_def] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN
  REPEAT
   (COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]) THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  REWRITE_TAC[cexp_if_def] THEN
  ARITH_TAC);;

let candle_fs_hist_root_certificate_contains = prove
 (`!input_lower input_upper root_lower root_upper x.
     candle_fs_hist_root_certificate input_lower input_upper
       root_lower root_upper /\
     candle_fs_interval_contains
       ((input_lower,0),(input_upper,0)) x
     ==> candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) (sqrt x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_certificate_def] THEN
  MESON_TAC[candle_fs_hist_root_certificate_sound]);;

(* Malformed untrusted roots are rejected before any endpoint comparison can
   authorize them.  These constructor-level facts are also regression tests
   for the short-circuiting shape gate used by the program wrapper. *)

let candle_cv_fs_hist_root_certificate_reject_outer_num = prove
 (`!input value.
     candle_cv_fs_hist_root_certificate input (Cexp_num value) =
     Cexp_num 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_root_certificate_def;
              candle_cv_fs_hist_bool_and_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def;
              cexp_if_def; LET_DEF; LET_END_DEF]);;

let candle_cv_fs_hist_root_certificate_reject_lower_num = prove
 (`!input value upper.
     candle_cv_fs_hist_root_certificate input
       (Cexp_pair (Cexp_num value) upper) = Cexp_num 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_root_certificate_def;
              candle_cv_fs_hist_bool_and_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def;
              cexp_if_def; LET_DEF; LET_END_DEF]);;

let candle_cv_fs_hist_root_certificate_reject_upper_num = prove
 (`!input lower value.
     candle_cv_fs_hist_root_certificate input
       (Cexp_pair lower (Cexp_num value)) = Cexp_num 0`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `lower:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_hist_root_certificate_def;
              candle_cv_fs_hist_bool_not_def;
              candle_cv_fs_hist_bool_and_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def;
              cexp_if_def; LET_DEF; LET_END_DEF]);;

end;;
