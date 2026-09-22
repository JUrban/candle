(* ========================================================================== *)
(* One-program second-order interval jets for a whole-box Taylor checker.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A single authenticated postfix program is the *)
(* source expression.  Its value, gradient, and Hessian are propagated as     *)
(* ordinary exact-interval data inside Kernel.compute.  No derivative-bound   *)
(* theorems are constructed before the reflected computation.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_whole_box_taylor.ml";;

module Candle_cv_whole_box_jet = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;

(* A jet is (f,(fx,(fy,(fxx,(fxy,fyy))))). *)

let candle_q_one_def = new_definition
 `candle_q_one = (((1,0),0):(num#num)#num)`;;

let candle_q_one_interval_def = new_definition
 `candle_q_one_interval =
    (candle_q_one,candle_q_one):
      ((num#num)#num)#((num#num)#num)`;;

let candle_q_jet_make_def = new_definition
 `candle_q_jet_make
    (f:((num#num)#num)#((num#num)#num)) fx fy fxx fxy fyy =
    (f,(fx,(fy,(fxx,(fxy,fyy)))))`;;

let candle_q_jet_f_def = new_definition
 `candle_q_jet_f
    (jet:(((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))#
           ((((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))#
             (((num#num)#num)#((num#num)#num))))))) = FST jet`;;

let candle_q_jet_fx_def = new_definition
 `candle_q_jet_fx jet = FST (SND jet)`;;

let candle_q_jet_fy_def = new_definition
 `candle_q_jet_fy jet = FST (SND (SND jet))`;;

let candle_q_jet_fxx_def = new_definition
 `candle_q_jet_fxx jet = FST (SND (SND (SND jet)))`;;

let candle_q_jet_fxy_def = new_definition
 `candle_q_jet_fxy jet = FST (SND (SND (SND (SND jet))))`;;

let candle_q_jet_fyy_def = new_definition
 `candle_q_jet_fyy jet = SND (SND (SND (SND (SND jet))))`;;

let candle_q_jet_zero_def = new_definition
 `candle_q_jet_zero =
    candle_q_jet_make
      candle_q_zero_interval candle_q_zero_interval
      candle_q_zero_interval candle_q_zero_interval
      candle_q_zero_interval candle_q_zero_interval`;;

let candle_q_jet_constant_def = new_definition
 `candle_q_jet_constant q =
    candle_q_jet_make (q,q)
      candle_q_zero_interval candle_q_zero_interval
      candle_q_zero_interval candle_q_zero_interval
      candle_q_zero_interval`;;

let candle_q_jet_x_def = new_definition
 `candle_q_jet_x ix =
    candle_q_jet_make ix candle_q_one_interval
      candle_q_zero_interval candle_q_zero_interval
      candle_q_zero_interval candle_q_zero_interval`;;

let candle_q_jet_y_def = new_definition
 `candle_q_jet_y iy =
    candle_q_jet_make iy candle_q_zero_interval
      candle_q_one_interval candle_q_zero_interval
      candle_q_zero_interval candle_q_zero_interval`;;

let candle_q_jet_variable_def = define
 `(candle_q_jet_variable ix iy 0 = candle_q_jet_x ix) /\
  (candle_q_jet_variable ix iy (SUC 0) = candle_q_jet_y iy) /\
  (candle_q_jet_variable ix iy (SUC (SUC n)) = candle_q_jet_zero)`;;

let candle_q_jet_interval_twice_def = new_definition
 `candle_q_jet_interval_twice x = candle_q_interval_add x x`;;

let candle_q_jet_neg_def = new_definition
 `candle_q_jet_neg a =
    candle_q_jet_make
      (candle_q_interval_neg (candle_q_jet_f a))
      (candle_q_interval_neg (candle_q_jet_fx a))
      (candle_q_interval_neg (candle_q_jet_fy a))
      (candle_q_interval_neg (candle_q_jet_fxx a))
      (candle_q_interval_neg (candle_q_jet_fxy a))
      (candle_q_interval_neg (candle_q_jet_fyy a))`;;

let candle_q_jet_add_def = new_definition
 `candle_q_jet_add a b =
    candle_q_jet_make
      (candle_q_interval_add (candle_q_jet_f a) (candle_q_jet_f b))
      (candle_q_interval_add (candle_q_jet_fx a) (candle_q_jet_fx b))
      (candle_q_interval_add (candle_q_jet_fy a) (candle_q_jet_fy b))
      (candle_q_interval_add (candle_q_jet_fxx a) (candle_q_jet_fxx b))
      (candle_q_interval_add (candle_q_jet_fxy a) (candle_q_jet_fxy b))
      (candle_q_interval_add (candle_q_jet_fyy a) (candle_q_jet_fyy b))`;;

let candle_q_jet_mul_def = new_definition
 `candle_q_jet_mul a b =
    candle_q_jet_make
      (candle_q_interval_mul (candle_q_jet_f a) (candle_q_jet_f b))
      (candle_q_interval_add
        (candle_q_interval_mul (candle_q_jet_fx a) (candle_q_jet_f b))
        (candle_q_interval_mul (candle_q_jet_f a) (candle_q_jet_fx b)))
      (candle_q_interval_add
        (candle_q_interval_mul (candle_q_jet_fy a) (candle_q_jet_f b))
        (candle_q_interval_mul (candle_q_jet_f a) (candle_q_jet_fy b)))
      (candle_q_interval_add
        (candle_q_interval_add
          (candle_q_interval_mul (candle_q_jet_fxx a) (candle_q_jet_f b))
          (candle_q_interval_mul (candle_q_jet_f a) (candle_q_jet_fxx b)))
        (candle_q_jet_interval_twice
          (candle_q_interval_mul (candle_q_jet_fx a) (candle_q_jet_fx b))))
      (candle_q_interval_add
        (candle_q_interval_add
          (candle_q_interval_mul (candle_q_jet_fxy a) (candle_q_jet_f b))
          (candle_q_interval_mul (candle_q_jet_fx a) (candle_q_jet_fy b)))
        (candle_q_interval_add
          (candle_q_interval_mul (candle_q_jet_fy a) (candle_q_jet_fx b))
          (candle_q_interval_mul (candle_q_jet_f a) (candle_q_jet_fxy b))))
      (candle_q_interval_add
        (candle_q_interval_add
          (candle_q_interval_mul (candle_q_jet_fyy a) (candle_q_jet_f b))
          (candle_q_interval_mul (candle_q_jet_f a) (candle_q_jet_fyy b)))
        (candle_q_jet_interval_twice
          (candle_q_interval_mul (candle_q_jet_fy a) (candle_q_jet_fy b))))`;;

let candle_q_jet_head_def = define
 `(candle_q_jet_head [] = candle_q_jet_zero) /\
  (candle_q_jet_head (CONS h t) = h)`;;

let candle_q_jet_tail_def = define
 `(candle_q_jet_tail [] = []) /\
  (candle_q_jet_tail (CONS h t) = t)`;;

let candle_q_jet_step_def = define
 `(candle_q_jet_step ix iy (Candle_q_push p n d) stack =
     CONS (candle_q_jet_constant ((p,n),d)) stack) /\
  (candle_q_jet_step ix iy (Candle_q_load index) stack =
     CONS (candle_q_jet_variable ix iy index) stack) /\
  (candle_q_jet_step ix iy Candle_q_neg stack =
     CONS (candle_q_jet_neg (candle_q_jet_head stack))
       (candle_q_jet_tail stack)) /\
  (candle_q_jet_step ix iy Candle_q_add stack =
     CONS
       (candle_q_jet_add
         (candle_q_jet_head (candle_q_jet_tail stack))
         (candle_q_jet_head stack))
       (candle_q_jet_tail (candle_q_jet_tail stack))) /\
  (candle_q_jet_step ix iy Candle_q_mul stack =
     CONS
       (candle_q_jet_mul
         (candle_q_jet_head (candle_q_jet_tail stack))
         (candle_q_jet_head stack))
       (candle_q_jet_tail (candle_q_jet_tail stack))) /\
  (candle_q_jet_step ix iy Candle_q_square stack =
     CONS
       (candle_q_jet_mul
         (candle_q_jet_head stack) (candle_q_jet_head stack))
       (candle_q_jet_tail stack))`;;

let candle_q_jet_run_def = define
 `(candle_q_jet_run ix iy [] stack = stack) /\
  (candle_q_jet_run ix iy (CONS h t) stack =
     candle_q_jet_run ix iy t (candle_q_jet_step ix iy h stack))`;;

let candle_q_jet_program_def = new_definition
 `candle_q_jet_program ix iy program =
    candle_q_jet_head (candle_q_jet_run ix iy program [])`;;

(* Exact real forward-mode semantics for the same value/gradient/Hessian jet. *)

let candle_real_jet_make_def = new_definition
 `candle_real_jet_make
    (f:real) fx fy fxx fxy fyy = (f,(fx,(fy,(fxx,(fxy,fyy)))))`;;

let candle_real_jet_f_def = new_definition
 `candle_real_jet_f (jet:real#(real#(real#(real#(real#real))))) = FST jet`;;

let candle_real_jet_fx_def = new_definition
 `candle_real_jet_fx jet = FST (SND jet)`;;

let candle_real_jet_fy_def = new_definition
 `candle_real_jet_fy jet = FST (SND (SND jet))`;;

let candle_real_jet_fxx_def = new_definition
 `candle_real_jet_fxx jet = FST (SND (SND (SND jet)))`;;

let candle_real_jet_fxy_def = new_definition
 `candle_real_jet_fxy jet = FST (SND (SND (SND (SND jet))))`;;

let candle_real_jet_fyy_def = new_definition
 `candle_real_jet_fyy jet = SND (SND (SND (SND (SND jet))))`;;

let candle_real_jet_zero_def = new_definition
 `candle_real_jet_zero = candle_real_jet_make (&0) (&0) (&0) (&0) (&0) (&0)`;;

let candle_real_jet_constant_def = new_definition
 `candle_real_jet_constant q =
    candle_real_jet_make (candle_q_real q) (&0) (&0) (&0) (&0) (&0)`;;

let candle_real_jet_x_def = new_definition
 `candle_real_jet_x x = candle_real_jet_make x (&1) (&0) (&0) (&0) (&0)`;;

let candle_real_jet_y_def = new_definition
 `candle_real_jet_y y = candle_real_jet_make y (&0) (&1) (&0) (&0) (&0)`;;

let candle_real_jet_variable_def = define
 `(candle_real_jet_variable x y 0 = candle_real_jet_x x) /\
  (candle_real_jet_variable x y (SUC 0) = candle_real_jet_y y) /\
  (candle_real_jet_variable x y (SUC (SUC n)) = candle_real_jet_zero)`;;

let candle_real_jet_neg_def = new_definition
 `candle_real_jet_neg a =
    candle_real_jet_make
      (--(candle_real_jet_f a)) (--(candle_real_jet_fx a))
      (--(candle_real_jet_fy a)) (--(candle_real_jet_fxx a))
      (--(candle_real_jet_fxy a)) (--(candle_real_jet_fyy a))`;;

let candle_real_jet_add_def = new_definition
 `candle_real_jet_add a b =
    candle_real_jet_make
      (candle_real_jet_f a + candle_real_jet_f b)
      (candle_real_jet_fx a + candle_real_jet_fx b)
      (candle_real_jet_fy a + candle_real_jet_fy b)
      (candle_real_jet_fxx a + candle_real_jet_fxx b)
      (candle_real_jet_fxy a + candle_real_jet_fxy b)
      (candle_real_jet_fyy a + candle_real_jet_fyy b)`;;

let candle_real_jet_mul_def = new_definition
 `candle_real_jet_mul a b =
    candle_real_jet_make
      (candle_real_jet_f a * candle_real_jet_f b)
      (candle_real_jet_fx a * candle_real_jet_f b +
       candle_real_jet_f a * candle_real_jet_fx b)
      (candle_real_jet_fy a * candle_real_jet_f b +
       candle_real_jet_f a * candle_real_jet_fy b)
      ((candle_real_jet_fxx a * candle_real_jet_f b +
        candle_real_jet_f a * candle_real_jet_fxx b) +
       (candle_real_jet_fx a * candle_real_jet_fx b +
        candle_real_jet_fx a * candle_real_jet_fx b))
      ((candle_real_jet_fxy a * candle_real_jet_f b +
        candle_real_jet_fx a * candle_real_jet_fy b) +
       (candle_real_jet_fy a * candle_real_jet_fx b +
        candle_real_jet_f a * candle_real_jet_fxy b))
      ((candle_real_jet_fyy a * candle_real_jet_f b +
        candle_real_jet_f a * candle_real_jet_fyy b) +
       (candle_real_jet_fy a * candle_real_jet_fy b +
        candle_real_jet_fy a * candle_real_jet_fy b))`;;

let candle_real_jet_head_def = define
 `(candle_real_jet_head [] = candle_real_jet_zero) /\
  (candle_real_jet_head (CONS h t) = h)`;;

let candle_real_jet_tail_def = define
 `(candle_real_jet_tail [] = []) /\
  (candle_real_jet_tail (CONS h t) = t)`;;

let candle_real_jet_step_def = define
 `(candle_real_jet_step x y (Candle_q_push p n d) stack =
     CONS (candle_real_jet_constant ((p,n),d)) stack) /\
  (candle_real_jet_step x y (Candle_q_load index) stack =
     CONS (candle_real_jet_variable x y index) stack) /\
  (candle_real_jet_step x y Candle_q_neg stack =
     CONS (candle_real_jet_neg (candle_real_jet_head stack))
       (candle_real_jet_tail stack)) /\
  (candle_real_jet_step x y Candle_q_add stack =
     CONS
       (candle_real_jet_add
         (candle_real_jet_head (candle_real_jet_tail stack))
         (candle_real_jet_head stack))
       (candle_real_jet_tail (candle_real_jet_tail stack))) /\
  (candle_real_jet_step x y Candle_q_mul stack =
     CONS
       (candle_real_jet_mul
         (candle_real_jet_head (candle_real_jet_tail stack))
         (candle_real_jet_head stack))
       (candle_real_jet_tail (candle_real_jet_tail stack))) /\
  (candle_real_jet_step x y Candle_q_square stack =
     CONS
       (candle_real_jet_mul
         (candle_real_jet_head stack) (candle_real_jet_head stack))
       (candle_real_jet_tail stack))`;;

let candle_real_jet_run_def = define
 `(candle_real_jet_run x y [] stack = stack) /\
  (candle_real_jet_run x y (CONS h t) stack =
     candle_real_jet_run x y t (candle_real_jet_step x y h stack))`;;

let candle_real_jet_program_def = new_definition
 `candle_real_jet_program x y program =
    candle_real_jet_head (candle_real_jet_run x y program [])`;;

let candle_real_jet_values_def = define
 `(candle_real_jet_values [] = ([]:real list)) /\
  (candle_real_jet_values (CONS h t) =
     CONS (candle_real_jet_f h) (candle_real_jet_values t))`;;

let candle_real_jet_variable_f = prove
 (`!index x y.
     candle_real_jet_f (candle_real_jet_variable x y index) =
     candle_q_real_lookup index [x;y]`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `index:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [REWRITE_TAC[candle_real_jet_variable_def; candle_real_jet_x_def;
                candle_real_jet_make_def; candle_real_jet_f_def;
                candle_q_real_lookup_def; FST; SND];
    MP_TAC (SPEC `n:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `m:num` SUBST1_TAC)) THEN
    REWRITE_TAC[candle_real_jet_variable_def; candle_real_jet_y_def;
                candle_real_jet_zero_def; candle_real_jet_make_def;
                candle_real_jet_f_def; candle_q_real_lookup_def; FST; SND]]);;

let candle_real_jet_head_f = prove
 (`!stack.
     candle_real_jet_f (candle_real_jet_head stack) =
     candle_q_real_head (candle_real_jet_values stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_real_jet_head_def; candle_real_jet_values_def;
              candle_real_jet_zero_def; candle_real_jet_make_def;
              candle_real_jet_f_def; candle_q_real_head_def; FST; SND]);;

let candle_real_jet_tail_values = prove
 (`!stack.
     candle_real_jet_values (candle_real_jet_tail stack) =
     candle_q_real_tail (candle_real_jet_values stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_real_jet_tail_def; candle_real_jet_values_def;
              candle_q_real_tail_def]);;

let candle_real_jet_step_values = prove
 (`!instruction x y stack.
     candle_real_jet_values (candle_real_jet_step x y instruction stack) =
     candle_q_real_step [x;y] instruction (candle_real_jet_values stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_jet_step_def; candle_q_real_step_def;
              candle_real_jet_values_def; candle_real_jet_constant_def;
              candle_real_jet_neg_def; candle_real_jet_add_def;
              candle_real_jet_mul_def; candle_real_jet_make_def;
              candle_real_jet_f_def; candle_real_jet_variable_f;
              candle_real_jet_head_f; candle_real_jet_tail_values;
              FST; SND]);;

let candle_real_jet_run_values = prove
 (`!program x y stack.
     candle_real_jet_values (candle_real_jet_run x y program stack) =
     candle_q_real_run [x;y] program (candle_real_jet_values stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_real_jet_run_def; candle_q_real_run_def;
                  candle_real_jet_step_values]);;

let candle_real_jet_program_f = prove
 (`!program x y.
     candle_real_jet_f (candle_real_jet_program x y program) =
     candle_q_real_head (candle_q_real_run [x;y] program [])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_jet_program_def; candle_real_jet_head_f;
              candle_real_jet_run_values; candle_real_jet_values_def]);;

let candle_q_jet_contains_def = new_definition
 `candle_q_jet_contains ijet rjet <=>
    candle_q_interval_contains (candle_q_jet_f ijet)
      (candle_real_jet_f rjet) /\
    candle_q_interval_contains (candle_q_jet_fx ijet)
      (candle_real_jet_fx rjet) /\
    candle_q_interval_contains (candle_q_jet_fy ijet)
      (candle_real_jet_fy rjet) /\
    candle_q_interval_contains (candle_q_jet_fxx ijet)
      (candle_real_jet_fxx rjet) /\
    candle_q_interval_contains (candle_q_jet_fxy ijet)
      (candle_real_jet_fxy rjet) /\
    candle_q_interval_contains (candle_q_jet_fyy ijet)
      (candle_real_jet_fyy rjet)`;;

let candle_q_jet_stack_contains_def = define
 `(candle_q_jet_stack_contains [] [] <=> T) /\
  (candle_q_jet_stack_contains [] (CONS r rs) <=> F) /\
  (candle_q_jet_stack_contains (CONS i is) [] <=> F) /\
  (candle_q_jet_stack_contains (CONS i is) (CONS r rs) <=>
     candle_q_jet_contains i r /\ candle_q_jet_stack_contains is rs)`;;

let candle_q_real_one = prove
 (`candle_q_real candle_q_one = &1`,
  REWRITE_TAC[candle_q_one_def; candle_q_real_def; candle_q_den_def;
              Candle_cv_linear_combination_realize.candle_lc_zreal_def;
              FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_one_interval_contains = prove
 (`candle_q_interval_contains candle_q_one_interval (&1)`,
  REWRITE_TAC[candle_q_one_interval_def; candle_q_interval_contains_def;
              candle_q_real_one; FST; SND; REAL_LE_REFL]);;

let candle_q_jet_constant_contains = prove
 (`!q. candle_q_jet_contains (candle_q_jet_constant q)
          (candle_real_jet_constant q)`,
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_constant_def;
              candle_real_jet_constant_def; candle_q_jet_make_def;
              candle_real_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; candle_real_jet_f_def;
              candle_real_jet_fx_def; candle_real_jet_fy_def;
              candle_real_jet_fxx_def; candle_real_jet_fxy_def;
              candle_real_jet_fyy_def; FST; SND;
              candle_q_exact_interval_contains;
              candle_q_zero_interval_contains]);;

let candle_q_jet_x_contains = prove
 (`!ix x. candle_q_interval_contains ix x
           ==> candle_q_jet_contains (candle_q_jet_x ix)
                 (candle_real_jet_x x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_x_def;
              candle_real_jet_x_def; candle_q_jet_make_def;
              candle_real_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; candle_real_jet_f_def;
              candle_real_jet_fx_def; candle_real_jet_fy_def;
              candle_real_jet_fxx_def; candle_real_jet_fxy_def;
              candle_real_jet_fyy_def; FST; SND;
              candle_q_one_interval_contains;
              candle_q_zero_interval_contains]);;

let candle_q_jet_y_contains = prove
 (`!iy y. candle_q_interval_contains iy y
           ==> candle_q_jet_contains (candle_q_jet_y iy)
                 (candle_real_jet_y y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_y_def;
              candle_real_jet_y_def; candle_q_jet_make_def;
              candle_real_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; candle_real_jet_f_def;
              candle_real_jet_fx_def; candle_real_jet_fy_def;
              candle_real_jet_fxx_def; candle_real_jet_fxy_def;
              candle_real_jet_fyy_def; FST; SND;
              candle_q_one_interval_contains;
              candle_q_zero_interval_contains]);;

let candle_q_jet_zero_contains = prove
 (`candle_q_jet_contains candle_q_jet_zero candle_real_jet_zero`,
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_zero_def;
              candle_real_jet_zero_def; candle_q_jet_make_def;
              candle_real_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; candle_real_jet_f_def;
              candle_real_jet_fx_def; candle_real_jet_fy_def;
              candle_real_jet_fxx_def; candle_real_jet_fxy_def;
              candle_real_jet_fyy_def; FST; SND;
              candle_q_zero_interval_contains]);;

let candle_q_jet_variable_contains = prove
 (`!index ix iy x y.
     candle_q_interval_contains ix x /\
     candle_q_interval_contains iy y
     ==> candle_q_jet_contains (candle_q_jet_variable ix iy index)
           (candle_real_jet_variable x y index)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC `index:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [ASM_SIMP_TAC[candle_q_jet_variable_def; candle_real_jet_variable_def;
                 candle_q_jet_x_contains];
    MP_TAC (SPEC `n:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `m:num` SUBST1_TAC)) THEN
    ASM_SIMP_TAC[candle_q_jet_variable_def; candle_real_jet_variable_def;
                 candle_q_jet_y_contains; candle_q_jet_zero_contains]]);;

let candle_q_jet_neg_contains = prove
 (`!i r. candle_q_jet_contains i r
         ==> candle_q_jet_contains (candle_q_jet_neg i)
               (candle_real_jet_neg r)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_neg_def;
              candle_real_jet_neg_def; candle_q_jet_make_def;
              candle_real_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; candle_real_jet_f_def;
              candle_real_jet_fx_def; candle_real_jet_fy_def;
              candle_real_jet_fxx_def; candle_real_jet_fxy_def;
              candle_real_jet_fyy_def; FST; SND] THEN
  MESON_TAC[candle_q_interval_neg_sound]);;

let candle_q_jet_add_contains = prove
 (`!i1 i2 r1 r2.
     candle_q_jet_contains i1 r1 /\ candle_q_jet_contains i2 r2
     ==> candle_q_jet_contains (candle_q_jet_add i1 i2)
           (candle_real_jet_add r1 r2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_add_def;
              candle_real_jet_add_def; candle_q_jet_make_def;
              candle_real_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; candle_real_jet_f_def;
              candle_real_jet_fx_def; candle_real_jet_fy_def;
              candle_real_jet_fxx_def; candle_real_jet_fxy_def;
              candle_real_jet_fyy_def; FST; SND] THEN
  MESON_TAC[candle_q_interval_add_sound]);;

let candle_q_jet_mul_contains = prove
 (`!i1 i2 r1 r2.
     candle_q_jet_contains i1 r1 /\ candle_q_jet_contains i2 r2
     ==> candle_q_jet_contains (candle_q_jet_mul i1 i2)
           (candle_real_jet_mul r1 r2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_jet_contains_def; candle_q_jet_mul_def;
              candle_real_jet_mul_def; candle_q_jet_interval_twice_def;
              candle_q_jet_make_def; candle_real_jet_make_def;
              candle_q_jet_f_def; candle_q_jet_fx_def;
              candle_q_jet_fy_def; candle_q_jet_fxx_def;
              candle_q_jet_fxy_def; candle_q_jet_fyy_def;
              candle_real_jet_f_def; candle_real_jet_fx_def;
              candle_real_jet_fy_def; candle_real_jet_fxx_def;
              candle_real_jet_fxy_def; candle_real_jet_fyy_def;
              FST; SND] THEN
  MESON_TAC[candle_q_interval_add_sound; candle_q_interval_mul_sound]);;

let candle_q_jet_stack_head_contains = prove
  (`!is rs. candle_q_jet_stack_contains is rs
           ==> candle_q_jet_contains
                 (candle_q_jet_head is) (candle_real_jet_head rs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC
    `is:((((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))#
           ((((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))#
             (((num#num)#num)#((num#num)#num)))))))list`
    list_CASES) THEN
  MP_TAC (ISPEC
    `rs:(real#(real#(real#(real#(real#real)))))list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  REWRITE_TAC[candle_q_jet_stack_contains_def; candle_q_jet_head_def;
              candle_real_jet_head_def; candle_q_jet_zero_contains] THEN
  MESON_TAC[]);;

let candle_q_jet_stack_tail_contains = prove
  (`!is rs. candle_q_jet_stack_contains is rs
           ==> candle_q_jet_stack_contains
                 (candle_q_jet_tail is) (candle_real_jet_tail rs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC
    `is:((((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))#
           ((((num#num)#num)#((num#num)#num))#
            ((((num#num)#num)#((num#num)#num))#
             (((num#num)#num)#((num#num)#num)))))))list`
    list_CASES) THEN
  MP_TAC (ISPEC
    `rs:(real#(real#(real#(real#(real#real)))))list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  REWRITE_TAC[candle_q_jet_stack_contains_def; candle_q_jet_tail_def;
              candle_real_jet_tail_def] THEN MESON_TAC[]);;

let candle_q_jet_step_contains = prove
 (`!instruction ix iy x y is rs.
     candle_q_interval_contains ix x /\
     candle_q_interval_contains iy y /\
     candle_q_jet_stack_contains is rs
     ==> candle_q_jet_stack_contains
           (candle_q_jet_step ix iy instruction is)
           (candle_real_jet_step x y instruction rs)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_jet_step_def; candle_real_jet_step_def;
              candle_q_jet_stack_contains_def] THENL
   [ASM_REWRITE_TAC[candle_q_jet_constant_contains];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_jet_variable_contains THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_jet_neg_contains THEN
      MATCH_MP_TAC candle_q_jet_stack_head_contains THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_jet_add_contains THEN CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_jet_stack_head_contains THEN
        MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_jet_stack_head_contains THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN
      MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_jet_mul_contains THEN CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_jet_stack_head_contains THEN
        MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_jet_stack_head_contains THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN
      MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_jet_mul_contains THEN CONJ_TAC THEN
      MATCH_MP_TAC candle_q_jet_stack_head_contains THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_jet_stack_tail_contains THEN ASM_REWRITE_TAC[]]]);;

let candle_q_jet_run_contains = prove
 (`!program ix iy x y is rs.
     candle_q_interval_contains ix x /\
     candle_q_interval_contains iy y /\
     candle_q_jet_stack_contains is rs
     ==> candle_q_jet_stack_contains
           (candle_q_jet_run ix iy program is)
           (candle_real_jet_run x y program rs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_jet_run_def; candle_real_jet_run_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC candle_q_jet_step_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_q_jet_program_contains = prove
 (`!program ix iy x y.
     candle_q_interval_contains ix x /\
     candle_q_interval_contains iy y
     ==> candle_q_jet_contains
           (candle_q_jet_program ix iy program)
           (candle_real_jet_program x y program)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_jet_program_def; candle_real_jet_program_def] THEN
  MATCH_MP_TAC candle_q_jet_stack_head_contains THEN
  MATCH_MP_TAC candle_q_jet_run_contains THEN
  ASM_REWRITE_TAC[candle_q_jet_stack_contains_def]);;

let candle_cv_q_one_def = new_definition
 `candle_cv_q_one =
    Cexp_pair (Cexp_pair (Cexp_num 1) (Cexp_num 0)) (Cexp_num 0)`;;

let candle_cv_q_one_interval_def = new_definition
 `candle_cv_q_one_interval =
    Cexp_pair candle_cv_q_one candle_cv_q_one`;;

let candle_cv_q_jet_make_def = new_definition
 `candle_cv_q_jet_make f fx fy fxx fxy fyy =
    Cexp_pair f
      (Cexp_pair fx
        (Cexp_pair fy
          (Cexp_pair fxx (Cexp_pair fxy fyy))))`;;

let candle_cv_q_jet_f_def = new_definition
 `candle_cv_q_jet_f jet = Cexp_fst jet`;;

let candle_cv_q_jet_fx_def = new_definition
 `candle_cv_q_jet_fx jet = Cexp_fst (Cexp_snd jet)`;;

let candle_cv_q_jet_fy_def = new_definition
 `candle_cv_q_jet_fy jet = Cexp_fst (Cexp_snd (Cexp_snd jet))`;;

let candle_cv_q_jet_fxx_def = new_definition
 `candle_cv_q_jet_fxx jet =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd jet)))`;;

let candle_cv_q_jet_fxy_def = new_definition
 `candle_cv_q_jet_fxy jet =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd jet))))`;;

let candle_cv_q_jet_fyy_def = new_definition
 `candle_cv_q_jet_fyy jet =
    Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd jet))))`;;

let candle_cv_q_jet_zero_def = new_definition
 `candle_cv_q_jet_zero =
    candle_cv_q_jet_make
      candle_cv_q_zero_interval candle_cv_q_zero_interval
      candle_cv_q_zero_interval candle_cv_q_zero_interval
      candle_cv_q_zero_interval candle_cv_q_zero_interval`;;

let candle_cv_q_jet_constant_def = new_definition
 `candle_cv_q_jet_constant q =
    candle_cv_q_jet_make (Cexp_pair q q)
      candle_cv_q_zero_interval candle_cv_q_zero_interval
      candle_cv_q_zero_interval candle_cv_q_zero_interval
      candle_cv_q_zero_interval`;;

let candle_cv_q_jet_x_def = new_definition
 `candle_cv_q_jet_x ix =
    candle_cv_q_jet_make ix candle_cv_q_one_interval
      candle_cv_q_zero_interval candle_cv_q_zero_interval
      candle_cv_q_zero_interval candle_cv_q_zero_interval`;;

let candle_cv_q_jet_y_def = new_definition
 `candle_cv_q_jet_y iy =
    candle_cv_q_jet_make iy candle_cv_q_zero_interval
      candle_cv_q_one_interval candle_cv_q_zero_interval
      candle_cv_q_zero_interval candle_cv_q_zero_interval`;;

let candle_cv_q_jet_variable_def = new_definition
 `candle_cv_q_jet_variable ix iy index =
    Cexp_if (Cexp_eq index (Cexp_num 0)) (candle_cv_q_jet_x ix)
      (Cexp_if (Cexp_eq index (Cexp_num 1)) (candle_cv_q_jet_y iy)
        candle_cv_q_jet_zero)`;;

let candle_cv_q_jet_interval_twice_def = new_definition
 `candle_cv_q_jet_interval_twice x = candle_cv_q_interval_add x x`;;

let candle_cv_q_jet_neg_def = new_definition
 `candle_cv_q_jet_neg a =
    candle_cv_q_jet_make
      (candle_cv_q_interval_neg (candle_cv_q_jet_f a))
      (candle_cv_q_interval_neg (candle_cv_q_jet_fx a))
      (candle_cv_q_interval_neg (candle_cv_q_jet_fy a))
      (candle_cv_q_interval_neg (candle_cv_q_jet_fxx a))
      (candle_cv_q_interval_neg (candle_cv_q_jet_fxy a))
      (candle_cv_q_interval_neg (candle_cv_q_jet_fyy a))`;;

let candle_cv_q_jet_add_def = new_definition
 `candle_cv_q_jet_add a b =
    candle_cv_q_jet_make
      (candle_cv_q_interval_add
        (candle_cv_q_jet_f a) (candle_cv_q_jet_f b))
      (candle_cv_q_interval_add
        (candle_cv_q_jet_fx a) (candle_cv_q_jet_fx b))
      (candle_cv_q_interval_add
        (candle_cv_q_jet_fy a) (candle_cv_q_jet_fy b))
      (candle_cv_q_interval_add
        (candle_cv_q_jet_fxx a) (candle_cv_q_jet_fxx b))
      (candle_cv_q_interval_add
        (candle_cv_q_jet_fxy a) (candle_cv_q_jet_fxy b))
      (candle_cv_q_interval_add
        (candle_cv_q_jet_fyy a) (candle_cv_q_jet_fyy b))`;;

let candle_cv_q_jet_mul_def = new_definition
 `candle_cv_q_jet_mul a b =
    candle_cv_q_jet_make
      (candle_cv_q_interval_mul
        (candle_cv_q_jet_f a) (candle_cv_q_jet_f b))
      (candle_cv_q_interval_add
        (candle_cv_q_interval_mul
          (candle_cv_q_jet_fx a) (candle_cv_q_jet_f b))
        (candle_cv_q_interval_mul
          (candle_cv_q_jet_f a) (candle_cv_q_jet_fx b)))
      (candle_cv_q_interval_add
        (candle_cv_q_interval_mul
          (candle_cv_q_jet_fy a) (candle_cv_q_jet_f b))
        (candle_cv_q_interval_mul
          (candle_cv_q_jet_f a) (candle_cv_q_jet_fy b)))
      (candle_cv_q_interval_add
        (candle_cv_q_interval_add
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fxx a) (candle_cv_q_jet_f b))
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_f a) (candle_cv_q_jet_fxx b)))
        (candle_cv_q_jet_interval_twice
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fx a) (candle_cv_q_jet_fx b))))
      (candle_cv_q_interval_add
        (candle_cv_q_interval_add
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fxy a) (candle_cv_q_jet_f b))
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fx a) (candle_cv_q_jet_fy b)))
        (candle_cv_q_interval_add
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fy a) (candle_cv_q_jet_fx b))
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_f a) (candle_cv_q_jet_fxy b))))
      (candle_cv_q_interval_add
        (candle_cv_q_interval_add
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fyy a) (candle_cv_q_jet_f b))
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_f a) (candle_cv_q_jet_fyy b)))
        (candle_cv_q_jet_interval_twice
          (candle_cv_q_interval_mul
            (candle_cv_q_jet_fy a) (candle_cv_q_jet_fy b))))`;;

let candle_cv_q_jet_head_def = new_definition
 `candle_cv_q_jet_head stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack) candle_cv_q_jet_zero`;;

let candle_cv_q_jet_tail_def = new_definition
 `candle_cv_q_jet_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_q_jet_step_def = new_definition
 `candle_cv_q_jet_step ix iy instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_q_jet_constant (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_q_jet_variable ix iy (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_q_jet_neg (candle_cv_q_jet_head stack))
          (candle_cv_q_jet_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_q_jet_add
              (candle_cv_q_jet_head (candle_cv_q_jet_tail stack))
              (candle_cv_q_jet_head stack))
            (candle_cv_q_jet_tail (candle_cv_q_jet_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_q_jet_mul
                (candle_cv_q_jet_head (candle_cv_q_jet_tail stack))
                (candle_cv_q_jet_head stack))
              (candle_cv_q_jet_tail (candle_cv_q_jet_tail stack)))
            (Cexp_pair
              (candle_cv_q_jet_mul
                (candle_cv_q_jet_head stack)
                (candle_cv_q_jet_head stack))
              (candle_cv_q_jet_tail stack)))))`;;

let candle_cv_q_jet_run_def = define
 `(candle_cv_q_jet_run ix iy (Cexp_num z) stack = stack) /\
  (candle_cv_q_jet_run ix iy (Cexp_pair h t) stack =
     candle_cv_q_jet_run ix iy t
       (candle_cv_q_jet_step ix iy h stack))`;;

let candle_cv_q_jet_run_compute = prove
 (`!ix iy program stack.
     candle_cv_q_jet_run ix iy program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_q_jet_run ix iy (Cexp_snd program)
         (candle_cv_q_jet_step ix iy (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_jet_run_def; cexp_if_def; cexp_ispair_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_jet_program_def = new_definition
 `candle_cv_q_jet_program ix iy program =
    candle_cv_q_jet_head
      (candle_cv_q_jet_run ix iy program (Cexp_num 0))`;;

let candle_cv_q_jet_whole_box_upper_def = new_definition
 `candle_cv_q_jet_whole_box_upper program ix iy =
    candle_cv_q_taylor_upper
      (candle_cv_q_radius ix) (candle_cv_q_radius iy)
      (candle_cv_q_jet_f
        (candle_cv_q_jet_program
          (candle_cv_q_point_interval (candle_cv_q_midpoint ix))
          (candle_cv_q_point_interval (candle_cv_q_midpoint iy)) program))
      (candle_cv_q_jet_fx
        (candle_cv_q_jet_program
          (candle_cv_q_point_interval (candle_cv_q_midpoint ix))
          (candle_cv_q_point_interval (candle_cv_q_midpoint iy)) program))
      (candle_cv_q_jet_fy
        (candle_cv_q_jet_program
          (candle_cv_q_point_interval (candle_cv_q_midpoint ix))
          (candle_cv_q_point_interval (candle_cv_q_midpoint iy)) program))
      (candle_cv_q_jet_fxx (candle_cv_q_jet_program ix iy program))
      (candle_cv_q_jet_fxy (candle_cv_q_jet_program ix iy program))
      (candle_cv_q_jet_fyy (candle_cv_q_jet_program ix iy program))`;;

let candle_cv_q_jet_whole_box_check_def = new_definition
 `candle_cv_q_jet_whole_box_check program ix iy =
    candle_cv_q_whole_box_finish
      (candle_cv_q_le (Cexp_fst ix) (Cexp_snd ix))
      (candle_cv_q_le (Cexp_fst iy) (Cexp_snd iy))
      (candle_cv_q_jet_whole_box_upper program ix iy)`;;

let candle_cv_q_jet_whole_box_compute_eqs =
  candle_cv_q_whole_box_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_one_def;
    candle_cv_q_one_interval_def;
    candle_cv_q_jet_make_def;
    candle_cv_q_jet_f_def;
    candle_cv_q_jet_fx_def;
    candle_cv_q_jet_fy_def;
    candle_cv_q_jet_fxx_def;
    candle_cv_q_jet_fxy_def;
    candle_cv_q_jet_fyy_def;
    candle_cv_q_jet_zero_def;
    candle_cv_q_jet_constant_def;
    candle_cv_q_jet_x_def;
    candle_cv_q_jet_y_def;
    candle_cv_q_jet_variable_def;
    candle_cv_q_jet_interval_twice_def;
    candle_cv_q_jet_neg_def;
    candle_cv_q_jet_add_def;
    candle_cv_q_jet_mul_def;
    candle_cv_q_jet_head_def;
    candle_cv_q_jet_tail_def;
    candle_cv_q_jet_step_def;
    candle_cv_q_jet_run_compute;
    candle_cv_q_jet_program_def;
    candle_cv_q_jet_whole_box_upper_def;
    candle_cv_q_jet_whole_box_check_def];;

(* -------------------------------------------------------------------------- *)
(* Representation: the reflected evaluator is the ordinary interval-jet     *)
(* algorithm above, including its internally generated derivatives.          *)
(* -------------------------------------------------------------------------- *)

let candle_cv_q_jet_def = new_definition
 `candle_cv_q_jet jet =
    candle_cv_q_jet_make
      (candle_cv_q_interval (candle_q_jet_f jet))
      (candle_cv_q_interval (candle_q_jet_fx jet))
      (candle_cv_q_interval (candle_q_jet_fy jet))
      (candle_cv_q_interval (candle_q_jet_fxx jet))
      (candle_cv_q_interval (candle_q_jet_fxy jet))
      (candle_cv_q_interval (candle_q_jet_fyy jet))`;;

let candle_cv_q_jet_list_def = define
 `(candle_cv_q_jet_list [] = Cexp_num 0) /\
  (candle_cv_q_jet_list (CONS h t) =
     Cexp_pair (candle_cv_q_jet h) (candle_cv_q_jet_list t))`;;

let candle_cv_q_one_correct = prove
 (`candle_cv_q_one = candle_cv_q candle_q_one`,
  REWRITE_TAC[candle_cv_q_one_def; candle_q_one_def; candle_cv_q_def;
              Candle_cv_linear_combination_core.candle_cv_lc_z_def;
              FST; SND]);;

let candle_cv_q_one_interval_correct = prove
 (`candle_cv_q_one_interval = candle_cv_q_interval candle_q_one_interval`,
  REWRITE_TAC[candle_cv_q_one_interval_def; candle_q_one_interval_def;
              candle_cv_q_interval_def; candle_cv_q_one_correct; FST; SND]);;

let candle_cv_one_suc = ARITH_RULE `1 = SUC 0`;;

let candle_cv_q_jet_make_correct = prove
 (`!f fx fy fxx fxy fyy.
     candle_cv_q_jet_make
       (candle_cv_q_interval f) (candle_cv_q_interval fx)
       (candle_cv_q_interval fy) (candle_cv_q_interval fxx)
       (candle_cv_q_interval fxy) (candle_cv_q_interval fyy) =
     candle_cv_q_jet (candle_q_jet_make f fx fy fxx fxy fyy)`,
  REWRITE_TAC[candle_cv_q_jet_make_def; candle_cv_q_jet_def;
              candle_q_jet_make_def; candle_q_jet_f_def;
              candle_q_jet_fx_def; candle_q_jet_fy_def;
              candle_q_jet_fxx_def; candle_q_jet_fxy_def;
              candle_q_jet_fyy_def; FST; SND]);;

let candle_cv_q_jet_f_correct = prove
 (`!jet. candle_cv_q_jet_f (candle_cv_q_jet jet) =
         candle_cv_q_interval (candle_q_jet_f jet)`,
  REWRITE_TAC[candle_cv_q_jet_f_def; candle_cv_q_jet_def;
              candle_cv_q_jet_make_def; cexp_fst_def]);;

let candle_cv_q_jet_fx_correct = prove
 (`!jet. candle_cv_q_jet_fx (candle_cv_q_jet jet) =
         candle_cv_q_interval (candle_q_jet_fx jet)`,
  REWRITE_TAC[candle_cv_q_jet_fx_def; candle_cv_q_jet_def;
              candle_cv_q_jet_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_jet_fy_correct = prove
 (`!jet. candle_cv_q_jet_fy (candle_cv_q_jet jet) =
         candle_cv_q_interval (candle_q_jet_fy jet)`,
  REWRITE_TAC[candle_cv_q_jet_fy_def; candle_cv_q_jet_def;
              candle_cv_q_jet_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_jet_fxx_correct = prove
 (`!jet. candle_cv_q_jet_fxx (candle_cv_q_jet jet) =
         candle_cv_q_interval (candle_q_jet_fxx jet)`,
  REWRITE_TAC[candle_cv_q_jet_fxx_def; candle_cv_q_jet_def;
              candle_cv_q_jet_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_jet_fxy_correct = prove
 (`!jet. candle_cv_q_jet_fxy (candle_cv_q_jet jet) =
         candle_cv_q_interval (candle_q_jet_fxy jet)`,
  REWRITE_TAC[candle_cv_q_jet_fxy_def; candle_cv_q_jet_def;
              candle_cv_q_jet_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_jet_fyy_correct = prove
 (`!jet. candle_cv_q_jet_fyy (candle_cv_q_jet jet) =
         candle_cv_q_interval (candle_q_jet_fyy jet)`,
  REWRITE_TAC[candle_cv_q_jet_fyy_def; candle_cv_q_jet_def;
              candle_cv_q_jet_make_def; cexp_snd_def]);;

let candle_cv_q_jet_zero_correct = prove
 (`candle_cv_q_jet_zero = candle_cv_q_jet candle_q_jet_zero`,
  REWRITE_TAC[candle_cv_q_jet_zero_def; candle_q_jet_zero_def;
              candle_cv_q_zero_interval_def;
              candle_cv_q_jet_make_correct]);;

let candle_cv_q_jet_constant_correct = prove
 (`!q. candle_cv_q_jet_constant (candle_cv_q q) =
       candle_cv_q_jet (candle_q_jet_constant q)`,
  REWRITE_TAC[candle_cv_q_jet_constant_def; candle_q_jet_constant_def;
              candle_cv_q_jet_def; candle_q_jet_make_def;
              candle_q_jet_f_def; candle_q_jet_fx_def;
              candle_q_jet_fy_def; candle_q_jet_fxx_def;
              candle_q_jet_fxy_def; candle_q_jet_fyy_def;
              candle_cv_q_jet_make_def; candle_cv_q_zero_interval_def;
              candle_cv_q_interval_def; FST; SND]);;

let candle_cv_q_jet_x_correct = prove
 (`!ix. candle_cv_q_jet_x (candle_cv_q_interval ix) =
        candle_cv_q_jet (candle_q_jet_x ix)`,
  REWRITE_TAC[candle_cv_q_jet_x_def; candle_q_jet_x_def;
              candle_cv_q_one_interval_correct;
              candle_cv_q_zero_interval_def;
              candle_cv_q_jet_make_correct]);;

let candle_cv_q_jet_y_correct = prove
 (`!iy. candle_cv_q_jet_y (candle_cv_q_interval iy) =
        candle_cv_q_jet (candle_q_jet_y iy)`,
  REWRITE_TAC[candle_cv_q_jet_y_def; candle_q_jet_y_def;
              candle_cv_q_one_interval_correct;
              candle_cv_q_zero_interval_def;
              candle_cv_q_jet_make_correct]);;

let candle_cv_q_jet_variable_correct = prove
 (`!index ix iy.
     candle_cv_q_jet_variable
       (candle_cv_q_interval ix) (candle_cv_q_interval iy)
       (Cexp_num index) =
     candle_cv_q_jet (candle_q_jet_variable ix iy index)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `index:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [REWRITE_TAC[candle_cv_q_jet_variable_def; candle_q_jet_variable_def;
                cexp_eq_def; cexp_if_def; candle_cv_q_jet_x_correct;
                distinctness "cval"; injectivity "cval"] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[candle_cv_one_suc; injectivity "num"; NOT_SUC;
                cexp_if_def];
    MP_TAC (SPEC `n:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `m:num` SUBST1_TAC)) THEN
    REWRITE_TAC[candle_cv_q_jet_variable_def; candle_q_jet_variable_def;
                cexp_eq_def; cexp_if_def; injectivity "num"; NOT_SUC;
                distinctness "cval"; injectivity "cval";
                candle_cv_q_jet_y_correct; candle_cv_q_jet_zero_correct] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[candle_cv_one_suc; injectivity "num"; NOT_SUC;
                cexp_if_def]]);;

let candle_cv_q_jet_interval_twice_correct = prove
 (`!i. candle_cv_q_jet_interval_twice (candle_cv_q_interval i) =
       candle_cv_q_interval (candle_q_jet_interval_twice i)`,
  REWRITE_TAC[candle_cv_q_jet_interval_twice_def;
              candle_q_jet_interval_twice_def;
              candle_cv_q_interval_add_correct]);;

let candle_cv_q_jet_neg_correct = prove
 (`!a. candle_cv_q_jet_neg (candle_cv_q_jet a) =
       candle_cv_q_jet (candle_q_jet_neg a)`,
  REWRITE_TAC[candle_cv_q_jet_neg_def; candle_q_jet_neg_def;
              candle_cv_q_jet_f_correct; candle_cv_q_jet_fx_correct;
              candle_cv_q_jet_fy_correct; candle_cv_q_jet_fxx_correct;
              candle_cv_q_jet_fxy_correct; candle_cv_q_jet_fyy_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_jet_make_correct]);;

let candle_cv_q_jet_add_correct = prove
 (`!a b. candle_cv_q_jet_add (candle_cv_q_jet a) (candle_cv_q_jet b) =
         candle_cv_q_jet (candle_q_jet_add a b)`,
  REWRITE_TAC[candle_cv_q_jet_add_def; candle_q_jet_add_def;
              candle_cv_q_jet_f_correct; candle_cv_q_jet_fx_correct;
              candle_cv_q_jet_fy_correct; candle_cv_q_jet_fxx_correct;
              candle_cv_q_jet_fxy_correct; candle_cv_q_jet_fyy_correct;
              candle_cv_q_interval_add_correct;
              candle_cv_q_jet_make_correct]);;

let candle_cv_q_jet_mul_correct = prove
 (`!a b. candle_cv_q_jet_mul (candle_cv_q_jet a) (candle_cv_q_jet b) =
         candle_cv_q_jet (candle_q_jet_mul a b)`,
  REWRITE_TAC[candle_cv_q_jet_mul_def; candle_q_jet_mul_def;
              candle_cv_q_jet_f_correct; candle_cv_q_jet_fx_correct;
              candle_cv_q_jet_fy_correct; candle_cv_q_jet_fxx_correct;
              candle_cv_q_jet_fxy_correct; candle_cv_q_jet_fyy_correct;
              candle_cv_q_interval_add_correct;
              candle_cv_q_interval_mul_correct;
              candle_cv_q_jet_interval_twice_correct;
              candle_cv_q_jet_make_correct]);;

let candle_cv_q_jet_head_correct = prove
 (`!stack. candle_cv_q_jet_head (candle_cv_q_jet_list stack) =
           candle_cv_q_jet (candle_q_jet_head stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_list_def; candle_cv_q_jet_head_def;
              candle_q_jet_head_def; cexp_if_def; cexp_ispair_def;
              cexp_fst_def; candle_cv_q_jet_zero_correct]);;

let candle_cv_q_jet_tail_correct = prove
 (`!stack. candle_cv_q_jet_tail (candle_cv_q_jet_list stack) =
           candle_cv_q_jet_list (candle_q_jet_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_list_def; candle_cv_q_jet_tail_def;
              candle_q_jet_tail_def; cexp_if_def; cexp_ispair_def;
              cexp_snd_def]);;

let candle_cv_q_jet_step_correct = prove
 (`!instruction ix iy stack.
     candle_cv_q_jet_step
       (candle_cv_q_interval ix) (candle_cv_q_interval iy)
       (candle_cv_q_instruction instruction)
       (candle_cv_q_jet_list stack) =
     candle_cv_q_jet_list (candle_q_jet_step ix iy instruction stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_step_def; candle_q_jet_step_def;
              candle_cv_q_instruction_def; candle_cv_q_jet_list_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              cexp_ispair_def; distinctness "cval"; injectivity "cval";
              NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_five_ne_two; candle_five_ne_three;
              candle_five_ne_four;
              candle_cv_q_jet_constant_correct;
              candle_cv_q_jet_variable_correct;
              candle_cv_q_jet_head_correct; candle_cv_q_jet_tail_correct;
              candle_cv_q_jet_neg_correct; candle_cv_q_jet_add_correct;
              candle_cv_q_jet_mul_correct]);;

let candle_cv_q_jet_run_correct = prove
 (`!program ix iy stack.
     candle_cv_q_jet_run
       (candle_cv_q_interval ix) (candle_cv_q_interval iy)
       (candle_cv_q_instruction_list program)
       (candle_cv_q_jet_list stack) =
     candle_cv_q_jet_list (candle_q_jet_run ix iy program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_instruction_list_def;
                  candle_cv_q_jet_run_def; candle_q_jet_run_def;
                  candle_cv_q_jet_step_correct]);;

let candle_cv_q_jet_program_correct = prove
 (`!program ix iy.
     candle_cv_q_jet_program
       (candle_cv_q_interval ix) (candle_cv_q_interval iy)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_jet (candle_q_jet_program ix iy program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_program_def; candle_q_jet_program_def;
              GSYM candle_cv_q_jet_list_def;
              candle_cv_q_jet_run_correct;
              candle_cv_q_jet_head_correct]);;

let candle_q_jet_whole_box_upper_def = new_definition
 `candle_q_jet_whole_box_upper program ix iy =
    candle_q_taylor_upper
      (candle_q_radius ix) (candle_q_radius iy)
      (candle_q_jet_f
        (candle_q_jet_program
          (candle_q_point_interval (candle_q_midpoint ix))
          (candle_q_point_interval (candle_q_midpoint iy)) program))
      (candle_q_jet_fx
        (candle_q_jet_program
          (candle_q_point_interval (candle_q_midpoint ix))
          (candle_q_point_interval (candle_q_midpoint iy)) program))
      (candle_q_jet_fy
        (candle_q_jet_program
          (candle_q_point_interval (candle_q_midpoint ix))
          (candle_q_point_interval (candle_q_midpoint iy)) program))
      (candle_q_jet_fxx (candle_q_jet_program ix iy program))
      (candle_q_jet_fxy (candle_q_jet_program ix iy program))
      (candle_q_jet_fyy (candle_q_jet_program ix iy program))`;;

let candle_q_jet_whole_box_accept_def = new_definition
 `candle_q_jet_whole_box_accept program ix iy <=>
    candle_q_box_valid ix iy /\
    ~(candle_q_le candle_q_zero
       (candle_q_jet_whole_box_upper program ix iy))`;;

let candle_cv_q_jet_whole_box_upper_correct = prove
 (`!program ix iy.
     candle_cv_q_jet_whole_box_upper
       (candle_cv_q_instruction_list program)
       (candle_cv_q_interval ix) (candle_cv_q_interval iy) =
     candle_cv_q (candle_q_jet_whole_box_upper program ix iy)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_whole_box_upper_def;
              candle_q_jet_whole_box_upper_def;
              candle_cv_q_radius_correct; candle_cv_q_midpoint_correct;
              candle_cv_q_point_interval_correct;
              candle_cv_q_jet_program_correct;
              candle_cv_q_jet_f_correct; candle_cv_q_jet_fx_correct;
              candle_cv_q_jet_fy_correct; candle_cv_q_jet_fxx_correct;
              candle_cv_q_jet_fxy_correct; candle_cv_q_jet_fyy_correct;
              candle_cv_q_taylor_upper_correct]);;

let candle_cv_q_jet_whole_box_check_correct = prove
 (`!program ix iy.
     candle_cv_q_jet_whole_box_check
       (candle_cv_q_instruction_list program)
       (candle_cv_q_interval ix) (candle_cv_q_interval iy) =
     Cexp_pair
       (Cexp_num
         (if candle_q_jet_whole_box_accept program ix iy
          then SUC 0 else 0))
       (candle_cv_q (candle_q_jet_whole_box_upper program ix iy))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_jet_whole_box_check_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct;
              candle_cv_q_jet_whole_box_upper_correct;
              candle_cv_q_whole_box_finish_correct;
              candle_q_jet_whole_box_accept_def; candle_q_box_valid_def;
              CONJ_ASSOC]);;

(* -------------------------------------------------------------------------- *)
(* Analytic handoff.  The reflected checker above owns all recurring numeric *)
(* work.  A source family need only establish this Taylor-remainder contract *)
(* once, relating its original function to the exact real jet semantics.      *)
(* -------------------------------------------------------------------------- *)

let candle_q_midpoint_point_contains = prove
 (`!i. candle_q_interval_contains
          (candle_q_point_interval (candle_q_midpoint i))
          (candle_q_real (candle_q_midpoint i))`,
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_point_interval_def; FST; SND; REAL_LE_REFL]);;

let candle_q_box_radius_nonnegative = prove
 (`!i. candle_q_le (FST i) (SND i)
       ==> &0 <= candle_q_real (candle_q_radius i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_le_real; candle_q_radius_real] THEN
  REAL_ARITH_TAC);;

let candle_q_box_deviation = prove
 (`!i x. candle_q_le (FST i) (SND i) /\
          candle_q_interval_contains i x
          ==> abs (x - candle_q_real (candle_q_midpoint i)) <=
              candle_q_real (candle_q_radius i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_le_real; candle_q_interval_contains_def;
              candle_q_midpoint_real; candle_q_radius_real;
              REAL_ABS_BOUNDS] THEN
  REAL_ARITH_TAC);;

let candle_real_jet_taylor_contract_def = new_definition
 `candle_real_jet_taylor_contract program ix iy (f:real->real->real) <=>
    !x y.
      candle_q_interval_contains ix x /\
      candle_q_interval_contains iy y
      ==> ?u v.
        candle_q_interval_contains ix u /\
        candle_q_interval_contains iy v /\
        f x y <=
          candle_real_jet_f
            (candle_real_jet_program
              (candle_q_real (candle_q_midpoint ix))
              (candle_q_real (candle_q_midpoint iy)) program) +
          abs (x - candle_q_real (candle_q_midpoint ix)) *
          abs (candle_real_jet_fx
            (candle_real_jet_program
              (candle_q_real (candle_q_midpoint ix))
              (candle_q_real (candle_q_midpoint iy)) program)) +
          abs (y - candle_q_real (candle_q_midpoint iy)) *
          abs (candle_real_jet_fy
            (candle_real_jet_program
              (candle_q_real (candle_q_midpoint ix))
              (candle_q_real (candle_q_midpoint iy)) program)) +
          inv (&2) *
          (abs (x - candle_q_real (candle_q_midpoint ix)) *
             (abs (x - candle_q_real (candle_q_midpoint ix)) *
                abs (candle_real_jet_fxx
                  (candle_real_jet_program u v program)) +
              &2 * abs (y - candle_q_real (candle_q_midpoint iy)) *
                abs (candle_real_jet_fxy
                  (candle_real_jet_program u v program))) +
           abs (y - candle_q_real (candle_q_midpoint iy)) *
             (abs (y - candle_q_real (candle_q_midpoint iy)) *
                abs (candle_real_jet_fyy
                  (candle_real_jet_program u v program))))`;;

end;;
