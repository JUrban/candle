(* ========================================================================== *)
(* Reflected exact-interval programs for coarse nonlinear reconstruction.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A postfix program batches a complete           *)
(* polynomial evaluation behind one Kernel.compute call.  Its ordinary        *)
(* semantics and cval implementation are connected by proved representation   *)
(* theorems, and the ordinary semantics preserves real interval containment.  *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_mul_core.ml";;

module Candle_cv_exact_interval_program = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_linear_combination_realize;;

let candle_q_instruction_INDUCT,candle_q_instruction_RECURSION = define_type
  "candle_q_instruction =
       Candle_q_push num num num
     | Candle_q_load num
     | Candle_q_neg
     | Candle_q_add
     | Candle_q_mul";;

let candle_q_zero_def = new_definition
 `candle_q_zero = (((0,0),0):(num#num)#num)`;;

let candle_q_zero_interval_def = new_definition
 `candle_q_zero_interval =
    (candle_q_zero,candle_q_zero):
      ((num#num)#num)#((num#num)#num)`;;

let candle_q_real_lookup_def = define
 `(candle_q_real_lookup n ([]:real list) = &0) /\
  (candle_q_real_lookup 0 (CONS h t) = h) /\
  (candle_q_real_lookup (SUC n) (CONS h t) =
     candle_q_real_lookup n t)`;;

let candle_q_interval_lookup_def = define
 `(candle_q_interval_lookup n
     ([]:(((num#num)#num)#((num#num)#num))list) =
       candle_q_zero_interval) /\
  (candle_q_interval_lookup 0 (CONS h t) = h) /\
  (candle_q_interval_lookup (SUC n) (CONS h t) =
     candle_q_interval_lookup n t)`;;

let candle_q_real_head_def = define
 `(candle_q_real_head ([]:real list) = &0) /\
  (candle_q_real_head (CONS h t) = h)`;;

let candle_q_real_tail_def = define
 `(candle_q_real_tail ([]:real list) = []) /\
  (candle_q_real_tail (CONS h t) = t)`;;

let candle_q_interval_head_def = define
 `(candle_q_interval_head
     ([]:(((num#num)#num)#((num#num)#num))list) =
       candle_q_zero_interval) /\
  (candle_q_interval_head (CONS h t) = h)`;;

let candle_q_interval_tail_def = define
 `(candle_q_interval_tail
     ([]:(((num#num)#num)#((num#num)#num))list) = []) /\
  (candle_q_interval_tail (CONS h t) = t)`;;

let candle_q_real_step_def = define
 `(candle_q_real_step env (Candle_q_push p n d) stack =
     CONS (candle_q_real ((p,n),d)) stack) /\
  (candle_q_real_step env (Candle_q_load i) stack =
     CONS (candle_q_real_lookup i env) stack) /\
  (candle_q_real_step env Candle_q_neg stack =
     CONS (--(candle_q_real_head stack))
       (candle_q_real_tail stack)) /\
  (candle_q_real_step env Candle_q_add stack =
     CONS
       (candle_q_real_head (candle_q_real_tail stack) +
        candle_q_real_head stack)
       (candle_q_real_tail (candle_q_real_tail stack))) /\
  (candle_q_real_step env Candle_q_mul stack =
     CONS
       (candle_q_real_head (candle_q_real_tail stack) *
        candle_q_real_head stack)
       (candle_q_real_tail (candle_q_real_tail stack)))`;;

let candle_q_interval_step_def = define
 `(candle_q_interval_step env (Candle_q_push p n d) stack =
     CONS ((((p,n),d),((p,n),d)):
             ((num#num)#num)#((num#num)#num)) stack) /\
  (candle_q_interval_step env (Candle_q_load i) stack =
     CONS (candle_q_interval_lookup i env) stack) /\
  (candle_q_interval_step env Candle_q_neg stack =
     CONS
       (candle_q_interval_neg (candle_q_interval_head stack))
       (candle_q_interval_tail stack)) /\
  (candle_q_interval_step env Candle_q_add stack =
     CONS
       (candle_q_interval_add
         (candle_q_interval_head (candle_q_interval_tail stack))
         (candle_q_interval_head stack))
       (candle_q_interval_tail (candle_q_interval_tail stack))) /\
  (candle_q_interval_step env Candle_q_mul stack =
     CONS
       (candle_q_interval_mul
         (candle_q_interval_head (candle_q_interval_tail stack))
         (candle_q_interval_head stack))
       (candle_q_interval_tail (candle_q_interval_tail stack)))`;;

let candle_q_real_run_def = define
 `(candle_q_real_run env [] stack = stack) /\
  (candle_q_real_run env (CONS h t) stack =
     candle_q_real_run env t (candle_q_real_step env h stack))`;;

let candle_q_interval_run_def = define
 `(candle_q_interval_run env [] stack = stack) /\
  (candle_q_interval_run env (CONS h t) stack =
     candle_q_interval_run env t
       (candle_q_interval_step env h stack))`;;

let candle_q_stack_contains_def = define
 `(candle_q_stack_contains
     ([]:(((num#num)#num)#((num#num)#num))list) ([]:real list) <=> T) /\
  (candle_q_stack_contains [] (CONS y ys) <=> F) /\
  (candle_q_stack_contains (CONS i is) [] <=> F) /\
  (candle_q_stack_contains (CONS i is) (CONS y ys) <=>
     candle_q_interval_contains i y /\
     candle_q_stack_contains is ys)`;;

let candle_q_zero_interval_contains = prove
 (`candle_q_interval_contains candle_q_zero_interval (&0)`,
  REWRITE_TAC[candle_q_zero_interval_def; candle_q_zero_def;
              candle_q_interval_contains_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND; real_div;
              REAL_SUB_REFL; REAL_MUL_LZERO; REAL_LE_REFL]);;

let candle_q_stack_head_contains = prove
 (`!is ys. candle_q_stack_contains is ys
           ==> candle_q_interval_contains
                 (candle_q_interval_head is)
                 (candle_q_real_head ys)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC
    `is:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
  MP_TAC (ISPEC `ys:real list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  REWRITE_TAC[candle_q_stack_contains_def; candle_q_interval_head_def;
              candle_q_real_head_def; candle_q_zero_interval_contains] THEN
  MESON_TAC[]);;

let candle_q_stack_tail_contains = prove
 (`!is ys. candle_q_stack_contains is ys
           ==> candle_q_stack_contains
                 (candle_q_interval_tail is)
                 (candle_q_real_tail ys)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC
    `is:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
  MP_TAC (ISPEC `ys:real list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  REWRITE_TAC[candle_q_stack_contains_def; candle_q_interval_tail_def;
              candle_q_real_tail_def] THEN
  MESON_TAC[]);;

let candle_q_stack_lookup_contains = prove
 (`!n is ys. candle_q_stack_contains is ys
             ==> candle_q_interval_contains
                   (candle_q_interval_lookup n is)
                   (candle_q_real_lookup n ys)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC
    `is:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
  MP_TAC (ISPEC `ys:real list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[candle_q_stack_contains_def;
                  candle_q_interval_lookup_def; candle_q_real_lookup_def;
                  candle_q_zero_interval_contains] THEN
  ASM_MESON_TAC[]);;

let candle_q_exact_interval_contains = prove
 (`!q:(num#num)#num.
     candle_q_interval_contains (q,q) (candle_q_real q)`,
  REWRITE_TAC[candle_q_interval_contains_def; REAL_LE_REFL]);;

let candle_q_interval_step_sound = prove
 (`!instruction ienv r_env i_stack r_stack.
     candle_q_stack_contains ienv r_env /\
     candle_q_stack_contains i_stack r_stack
     ==> candle_q_stack_contains
           (candle_q_interval_step ienv instruction i_stack)
           (candle_q_real_step r_env instruction r_stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_interval_step_def; candle_q_real_step_def;
              candle_q_stack_contains_def] THENL
   [REWRITE_TAC[candle_q_exact_interval_contains] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[candle_q_stack_lookup_contains];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_neg_sound THEN
      MATCH_MP_TAC candle_q_stack_head_contains THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_stack_tail_contains THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_stack_head_contains THEN
        MATCH_MP_TAC candle_q_stack_tail_contains THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_stack_head_contains THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_q_stack_tail_contains THEN
      MATCH_MP_TAC candle_q_stack_tail_contains THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_mul_sound THEN CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_stack_head_contains THEN
        MATCH_MP_TAC candle_q_stack_tail_contains THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_stack_head_contains THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_q_stack_tail_contains THEN
      MATCH_MP_TAC candle_q_stack_tail_contains THEN ASM_REWRITE_TAC[]]]);;

let candle_q_interval_run_sound = prove
 (`!program ienv r_env i_stack r_stack.
     candle_q_stack_contains ienv r_env /\
     candle_q_stack_contains i_stack r_stack
     ==> candle_q_stack_contains
           (candle_q_interval_run ienv program i_stack)
           (candle_q_real_run r_env program r_stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_interval_run_def; candle_q_real_run_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC candle_q_interval_step_sound THEN
  ASM_REWRITE_TAC[]);;

(* -------------------------------------------------------------------------- *)
(* cval encoding and evaluator.                                               *)
(* -------------------------------------------------------------------------- *)

let candle_cv_q_instruction_def = define
 `(candle_cv_q_instruction (Candle_q_push p n d) =
     Cexp_pair (Cexp_num 0) (candle_cv_q ((p,n),d))) /\
  (candle_cv_q_instruction (Candle_q_load i) =
     Cexp_pair (Cexp_num 1) (Cexp_num i)) /\
  (candle_cv_q_instruction Candle_q_neg = Cexp_num 2) /\
  (candle_cv_q_instruction Candle_q_add = Cexp_num 3) /\
  (candle_cv_q_instruction Candle_q_mul = Cexp_num 4)`;;

let candle_cv_q_instruction_list_def = define
 `(candle_cv_q_instruction_list [] = Cexp_num 0) /\
  (candle_cv_q_instruction_list (CONS h t) =
     Cexp_pair (candle_cv_q_instruction h)
       (candle_cv_q_instruction_list t))`;;

let candle_cv_q_interval_list_def = define
 `(candle_cv_q_interval_list [] = Cexp_num 0) /\
  (candle_cv_q_interval_list (CONS h t) =
     Cexp_pair (candle_cv_q_interval h)
       (candle_cv_q_interval_list t))`;;

let candle_cv_q_zero_interval_def = new_definition
 `candle_cv_q_zero_interval =
    candle_cv_q_interval candle_q_zero_interval`;;

let candle_cv_q_zero_interval_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_zero_interval_def; candle_q_zero_def;
                    candle_cv_q_interval_def; candle_cv_q_def;
                    Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                    FST; SND]))
    candle_cv_q_zero_interval_def;;

let candle_cv_q_interval_head_def = new_definition
 `candle_cv_q_interval_head stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      candle_cv_q_zero_interval`;;

let candle_cv_q_interval_tail_def = new_definition
 `candle_cv_q_interval_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_q_interval_lookup_def = define
 `(candle_cv_q_interval_lookup (Cexp_num n) (Cexp_num z) =
     candle_cv_q_zero_interval) /\
  (candle_cv_q_interval_lookup (Cexp_pair p q) env =
     candle_cv_q_zero_interval) /\
  (candle_cv_q_interval_lookup (Cexp_num 0) (Cexp_pair h t) = h) /\
  (candle_cv_q_interval_lookup (Cexp_num (SUC n)) (Cexp_pair h t) =
     candle_cv_q_interval_lookup (Cexp_num n) t)`;;

let candle_cv_q_interval_step_def = new_definition
 `candle_cv_q_interval_step env instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (Cexp_pair (Cexp_snd instruction) (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_q_interval_lookup (Cexp_snd instruction) env) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_q_interval_neg (candle_cv_q_interval_head stack))
          (candle_cv_q_interval_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_q_interval_add
              (candle_cv_q_interval_head
                (candle_cv_q_interval_tail stack))
              (candle_cv_q_interval_head stack))
            (candle_cv_q_interval_tail
              (candle_cv_q_interval_tail stack)))
          (Cexp_pair
            (candle_cv_q_interval_mul
              (candle_cv_q_interval_head
                (candle_cv_q_interval_tail stack))
              (candle_cv_q_interval_head stack))
            (candle_cv_q_interval_tail
              (candle_cv_q_interval_tail stack)))))`;;

let candle_cv_q_interval_run_def = define
 `(candle_cv_q_interval_run env (Cexp_num z) stack = stack) /\
  (candle_cv_q_interval_run env (Cexp_pair h t) stack =
     candle_cv_q_interval_run env t
       (candle_cv_q_interval_step env h stack))`;;

let candle_cv_q_interval_lookup_compute = prove
 (`!n env.
     candle_cv_q_interval_lookup n env =
     Cexp_if (Cexp_ispair n)
       candle_cv_q_zero_interval
       (Cexp_if (Cexp_ispair env)
         (Cexp_if (Cexp_eq n (Cexp_num 0))
           (Cexp_fst env)
           (candle_cv_q_interval_lookup
             (Cexp_sub n (Cexp_num 1)) (Cexp_snd env)))
         candle_cv_q_zero_interval)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `n:cval` (cases "cval")) THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `env:cval` (cases "cval")) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC)
    (SPEC `a:num` num_CASES) THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_lookup_def; cexp_if_def;
                  cexp_ispair_def; cexp_eq_def; cexp_fst_def; cexp_snd_def;
                  cexp_sub_def; distinctness "cval"; injectivity "cval";
                  NOT_SUC; SUC_SUB1]);;

let candle_cv_q_interval_run_compute = prove
 (`!env program stack.
     candle_cv_q_interval_run env program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_q_interval_run env (Cexp_snd program)
         (candle_cv_q_interval_step env (Cexp_fst program) stack))
       stack`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_interval_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_interval_program_compute_eqs =
  candle_cv_q_interval_mul_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_zero_interval_compute;
    candle_cv_q_interval_head_def;
    candle_cv_q_interval_tail_def;
    candle_cv_q_interval_lookup_compute;
    candle_cv_q_interval_step_def;
    candle_cv_q_interval_run_compute];;

let candle_cv_q_interval_head_correct = prove
 (`!stack.
     candle_cv_q_interval_head (candle_cv_q_interval_list stack) =
     candle_cv_q_interval (candle_q_interval_head stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_head_def;
              candle_cv_q_interval_list_def; candle_q_interval_head_def;
              candle_cv_q_zero_interval_def; cexp_if_def; cexp_ispair_def;
              cexp_fst_def]);;

let candle_cv_q_interval_tail_correct = prove
 (`!stack.
     candle_cv_q_interval_tail (candle_cv_q_interval_list stack) =
     candle_cv_q_interval_list (candle_q_interval_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_tail_def;
              candle_cv_q_interval_list_def; candle_q_interval_tail_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_q_interval_lookup_correct = prove
 (`!n env.
     candle_cv_q_interval_lookup (Cexp_num n)
       (candle_cv_q_interval_list env) =
     candle_cv_q_interval (candle_q_interval_lookup n env)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_lookup_def;
                  candle_cv_q_interval_list_def;
                  candle_q_interval_lookup_def;
                  candle_cv_q_zero_interval_def]);;

let candle_one_ne_zero =
  EQT_ELIM (NUM_REDUCE_CONV `~(1 = 0)`);;

let candle_four_ne_two =
  EQT_ELIM (NUM_REDUCE_CONV `~(4 = 2)`);;

let candle_four_ne_three =
  EQT_ELIM (NUM_REDUCE_CONV `~(4 = 3)`);;

let candle_three_ne_two =
  EQT_ELIM (NUM_REDUCE_CONV `~(3 = 2)`);;

let candle_cv_q_interval_step_correct = prove
 (`!instruction env stack.
     candle_cv_q_interval_step
       (candle_cv_q_interval_list env)
       (candle_cv_q_instruction instruction)
       (candle_cv_q_interval_list stack) =
     candle_cv_q_interval_list
       (candle_q_interval_step env instruction stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_step_def;
              candle_cv_q_instruction_def; candle_q_interval_step_def;
              candle_cv_q_interval_list_def;
              cexp_fst_def; cexp_snd_def;
              cexp_eq_def; cexp_if_def; cexp_ispair_def;
              distinctness "cval"; injectivity "cval"; NOT_SUC;
              candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_cv_q_interval_lookup_correct;
              candle_cv_q_interval_head_correct;
              candle_cv_q_interval_tail_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_interval_add_correct;
              candle_cv_q_interval_mul_correct] THEN
  REWRITE_TAC[candle_cv_q_interval_def]);;

let candle_cv_q_interval_run_correct = prove
 (`!program env stack.
     candle_cv_q_interval_run
       (candle_cv_q_interval_list env)
       (candle_cv_q_instruction_list program)
       (candle_cv_q_interval_list stack) =
     candle_cv_q_interval_list
       (candle_q_interval_run env program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_instruction_list_def;
                  candle_cv_q_interval_run_def;
                  candle_q_interval_run_def;
                  candle_cv_q_interval_step_correct]);;

end;;
