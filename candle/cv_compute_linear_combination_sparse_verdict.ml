(* ========================================================================== *)
(* Sparse one-shot arithmetic verdict for exact LP linear combinations.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. A sparse row maps sorted variable indices to   *)
(* subtraction-free signed integers. Kernel.compute merges/scales all rows   *)
(* and returns only whether every variable cancels and the rhs is negative.  *)
(* This file establishes representation correctness; a separate soundness    *)
(* bridge connects a successful verdict to authenticated real inequalities.  *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_core.ml";;

module Candle_cv_linear_combination_sparse_verdict = struct

open Candle_cv_linear_combination_core;;


(* Ordinary exact sparse arithmetic. Entries are (variable index,signed
   coefficient), sorted by strictly increasing index by the later reifier. *)

let candle_lc_sparse_insert_def = new_recursive_definition list_RECURSION
 `(!x. candle_lc_sparse_insert x ([]:(num#(num#num))list) = [x]) /\
  (!x y ys. candle_lc_sparse_insert x (CONS y ys) =
     if FST x < FST y then CONS x (CONS y ys)
     else if FST y < FST x then
       CONS y (candle_lc_sparse_insert x ys)
     else CONS (FST x,candle_lc_zadd (SND x) (SND y)) ys)`;;


let candle_lc_sparse_add_def = new_recursive_definition list_RECURSION
 `(!ys. candle_lc_sparse_add ([]:(num#(num#num))list) ys = ys) /\
  (!x xs ys. candle_lc_sparse_add (CONS x xs) ys =
     candle_lc_sparse_add xs (candle_lc_sparse_insert x ys))`;;


let candle_lc_sparse_scale_def = new_recursive_definition list_RECURSION
 `(!k. candle_lc_sparse_scale k ([]:(num#(num#num))list) = []) /\
  (!k x xs. candle_lc_sparse_scale k (CONS x xs) =
     CONS (FST x,candle_lc_zscale k (SND x))
          (candle_lc_sparse_scale k xs))`;;


let candle_lc_sparse_accumulate_def = new_definition
 `candle_lc_sparse_accumulate
    (acc:(num#(num#num))list#(num#num))
    (lcrow:num#((num#(num#num))list#(num#num))) =
    (candle_lc_sparse_add (FST acc)
       (candle_lc_sparse_scale (FST lcrow) (FST (SND lcrow))),
     candle_lc_zadd (SND acc)
       (candle_lc_zscale (FST lcrow) (SND (SND lcrow))))`;;


let candle_lc_sparse_fold_def = define
 `(candle_lc_sparse_fold acc
      ([]:(num#((num#(num#num))list#(num#num)))list) = acc) /\
  (candle_lc_sparse_fold acc (CONS lcrow lcrows) =
     candle_lc_sparse_fold
       (candle_lc_sparse_accumulate acc lcrow) lcrows)`;;


let candle_lc_sparse_zero_def = define
 `(candle_lc_sparse_zero ([]:(num#(num#num))list) <=> T) /\
  (candle_lc_sparse_zero (CONS x xs) <=>
     FST (SND x) = SND (SND x) /\ candle_lc_sparse_zero xs)`;;


let candle_lc_sparse_infeasible_def = new_definition
 `candle_lc_sparse_infeasible
    (acc:(num#(num#num))list#(num#num)) <=>
    candle_lc_sparse_zero (FST acc) /\
    FST (SND acc) < SND (SND acc)`;;


(* cval encodings. A sparse list uses Cexp_num 0 as NIL and Cexp_pair as
   CONS, following the dense prototype. *)

let candle_cv_lc_sparse_entry_def = new_definition
 `candle_cv_lc_sparse_entry x =
    Cexp_pair (Cexp_num (FST x)) (candle_cv_lc_z (SND x))`;;


let candle_cv_lc_sparse_vec_def = new_recursive_definition list_RECURSION
 `(candle_cv_lc_sparse_vec ([]:(num#(num#num))list) = Cexp_num 0) /\
  (!x xs. candle_cv_lc_sparse_vec (CONS x xs) =
     Cexp_pair (candle_cv_lc_sparse_entry x)
               (candle_cv_lc_sparse_vec xs))`;;


let candle_cv_lc_sparse_acc_def = new_definition
 `candle_cv_lc_sparse_acc acc =
    Cexp_pair (candle_cv_lc_sparse_vec (FST acc))
              (candle_cv_lc_z (SND acc))`;;


let candle_cv_lc_sparse_row_def = new_definition
 `candle_cv_lc_sparse_row lcrow =
    Cexp_pair (Cexp_num (FST lcrow))
      (candle_cv_lc_sparse_acc (SND lcrow))`;;


let candle_cv_lc_sparse_rows_def = new_recursive_definition list_RECURSION
 `(candle_cv_lc_sparse_rows
      ([]:(num#((num#(num#num))list#(num#num)))list) = Cexp_num 0) /\
  (!lcrow lcrows. candle_cv_lc_sparse_rows (CONS lcrow lcrows) =
     Cexp_pair (candle_cv_lc_sparse_row lcrow)
               (candle_cv_lc_sparse_rows lcrows))`;;


let candle_cv_lc_sparse_insert_def = new_recursive_definition cval_RECURSION
 `(!x n. candle_cv_lc_sparse_insert x (Cexp_num n) =
     Cexp_pair x (Cexp_num 0)) /\
  (!x y ys. candle_cv_lc_sparse_insert x (Cexp_pair y ys) =
     Cexp_if (Cexp_less (Cexp_fst x) (Cexp_fst y))
       (Cexp_pair x (Cexp_pair y ys))
       (Cexp_if (Cexp_less (Cexp_fst y) (Cexp_fst x))
         (Cexp_pair y (candle_cv_lc_sparse_insert x ys))
         (Cexp_pair
           (Cexp_pair (Cexp_fst x)
             (candle_cv_lc_zadd (Cexp_snd x) (Cexp_snd y)))
           ys)))`;;


let candle_cv_lc_sparse_add_def = new_recursive_definition cval_RECURSION
 `(!m y. candle_cv_lc_sparse_add (Cexp_num m) y = y) /\
  (!x xs y. candle_cv_lc_sparse_add (Cexp_pair x xs) y =
     candle_cv_lc_sparse_add xs
       (candle_cv_lc_sparse_insert x y))`;;


let candle_cv_lc_sparse_scale_def = new_recursive_definition cval_RECURSION
 `(!k n. candle_cv_lc_sparse_scale k (Cexp_num n) = Cexp_num 0) /\
  (!k x xs. candle_cv_lc_sparse_scale k (Cexp_pair x xs) =
     Cexp_pair
       (Cexp_pair (Cexp_fst x)
         (candle_cv_lc_zscale k (Cexp_snd x)))
       (candle_cv_lc_sparse_scale k xs))`;;


let candle_cv_lc_sparse_accumulate_def = new_definition
 `candle_cv_lc_sparse_accumulate acc lcrow =
    Cexp_pair
      (candle_cv_lc_sparse_add (Cexp_fst acc)
        (candle_cv_lc_sparse_scale (Cexp_fst lcrow)
          (Cexp_fst (Cexp_snd lcrow))))
      (candle_cv_lc_zadd (Cexp_snd acc)
        (candle_cv_lc_zscale (Cexp_fst lcrow)
          (Cexp_snd (Cexp_snd lcrow))))`;;


let candle_cv_lc_sparse_fold_def = new_recursive_definition cval_RECURSION
 `(!acc n. candle_cv_lc_sparse_fold acc (Cexp_num n) = acc) /\
  (!acc lcrow lcrows.
     candle_cv_lc_sparse_fold acc (Cexp_pair lcrow lcrows) =
     candle_cv_lc_sparse_fold
       (candle_cv_lc_sparse_accumulate acc lcrow) lcrows)`;;


let candle_cv_lc_sparse_zero_def = new_recursive_definition cval_RECURSION
 `(!n. candle_cv_lc_sparse_zero (Cexp_num n) = Cexp_num (SUC 0)) /\
  (!x xs. candle_cv_lc_sparse_zero (Cexp_pair x xs) =
     Cexp_if (Cexp_less (Cexp_fst (Cexp_snd x))
                         (Cexp_snd (Cexp_snd x)))
       (Cexp_num 0)
       (Cexp_if (Cexp_less (Cexp_snd (Cexp_snd x))
                            (Cexp_fst (Cexp_snd x)))
         (Cexp_num 0)
         (candle_cv_lc_sparse_zero xs)))`;;


let candle_cv_lc_sparse_infeasible_def = new_definition
 `candle_cv_lc_sparse_infeasible acc =
    Cexp_if (candle_cv_lc_sparse_zero (Cexp_fst acc))
      (Cexp_less (Cexp_fst (Cexp_snd acc))
                 (Cexp_snd (Cexp_snd acc)))
      (Cexp_num 0)`;;


let candle_cv_lc_sparse_fold_verdict_def = new_definition
 `candle_cv_lc_sparse_fold_verdict acc lcrows =
    candle_cv_lc_sparse_infeasible
      (candle_cv_lc_sparse_fold acc lcrows)`;;

(* All-variable evaluator equations. *)

let candle_cv_lc_sparse_insert_compute = prove
 (`!x ys. candle_cv_lc_sparse_insert x ys =
     Cexp_if (Cexp_ispair ys)
       (Cexp_if (Cexp_less (Cexp_fst x)
                            (Cexp_fst (Cexp_fst ys)))
         (Cexp_pair x ys)
         (Cexp_if (Cexp_less (Cexp_fst (Cexp_fst ys))
                              (Cexp_fst x))
           (Cexp_pair (Cexp_fst ys)
             (candle_cv_lc_sparse_insert x (Cexp_snd ys)))
           (Cexp_pair
             (Cexp_pair (Cexp_fst x)
               (candle_cv_lc_zadd (Cexp_snd x)
                                  (Cexp_snd (Cexp_fst ys))))
             (Cexp_snd ys))))
       (Cexp_pair x (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_sparse_insert_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_sparse_add_compute = prove
 (`!xs ys. candle_cv_lc_sparse_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (candle_cv_lc_sparse_add (Cexp_snd xs)
         (candle_cv_lc_sparse_insert (Cexp_fst xs) ys))
       ys`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_sparse_add_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_sparse_scale_compute = prove
 (`!k xs. candle_cv_lc_sparse_scale k xs =
     Cexp_if (Cexp_ispair xs)
       (Cexp_pair
         (Cexp_pair (Cexp_fst (Cexp_fst xs))
           (candle_cv_lc_zscale k (Cexp_snd (Cexp_fst xs))))
         (candle_cv_lc_sparse_scale k (Cexp_snd xs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_sparse_scale_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_sparse_fold_compute = prove
 (`!acc lcrows. candle_cv_lc_sparse_fold acc lcrows =
     Cexp_if (Cexp_ispair lcrows)
       (candle_cv_lc_sparse_fold
         (candle_cv_lc_sparse_accumulate acc (Cexp_fst lcrows))
         (Cexp_snd lcrows))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `lcrows:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_sparse_fold_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_sparse_zero_compute = prove
 (`!xs. candle_cv_lc_sparse_zero xs =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if
         (Cexp_less (Cexp_fst (Cexp_snd (Cexp_fst xs)))
                    (Cexp_snd (Cexp_snd (Cexp_fst xs))))
         (Cexp_num 0)
         (Cexp_if
           (Cexp_less (Cexp_snd (Cexp_snd (Cexp_fst xs)))
                      (Cexp_fst (Cexp_snd (Cexp_fst xs))))
           (Cexp_num 0)
           (candle_cv_lc_sparse_zero (Cexp_snd xs))))
       (Cexp_ispair (Cexp_pair (Cexp_num 0) (Cexp_num 0)))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_sparse_zero_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_sparse_compute_eqs =
  map SPEC_ALL
   [candle_cv_lc_zadd_def;
    candle_cv_lc_zscale_def;
    candle_cv_lc_sparse_insert_compute;
    candle_cv_lc_sparse_add_compute;
    candle_cv_lc_sparse_scale_compute;
    candle_cv_lc_sparse_accumulate_def;
    candle_cv_lc_sparse_fold_compute;
    candle_cv_lc_sparse_zero_compute;
    candle_cv_lc_sparse_infeasible_def;
    candle_cv_lc_sparse_fold_verdict_def];;


(* Representation correctness for the complete sparse fold and one-bit
   verdict. *)

let candle_cv_lc_sparse_insert_correct = prove
 (`!x ys.
     candle_cv_lc_sparse_insert (candle_cv_lc_sparse_entry x)
       (candle_cv_lc_sparse_vec ys) =
     candle_cv_lc_sparse_vec (candle_lc_sparse_insert x ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                candle_cv_lc_sparse_entry_def;
                candle_cv_lc_sparse_insert_def] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_insert_def] THEN
    REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                candle_cv_lc_sparse_entry_def];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_insert_def] THEN
    ASM_CASES_TAC
      `FST (x:num#(num#num)) < FST (h:num#(num#num))` THEN
    ASM_CASES_TAC
      `FST (h:num#(num#num)) < FST (x:num#(num#num))` THEN
    ASM_REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                    candle_cv_lc_sparse_entry_def;
                    candle_cv_lc_sparse_insert_def;
                    FST; SND;
                    cexp_fst_def; cexp_snd_def; cexp_less_def;
                    cexp_if_def; candle_cv_lc_zadd_correct] THEN
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC
      [GSYM (SPEC `x:num#(num#num)` candle_cv_lc_sparse_entry_def)] THEN
    ASM_REWRITE_TAC[]]);;

let candle_cv_lc_sparse_add_correct = prove
 (`!xs ys.
     candle_cv_lc_sparse_add (candle_cv_lc_sparse_vec xs)
                             (candle_cv_lc_sparse_vec ys) =
     candle_cv_lc_sparse_vec (candle_lc_sparse_add xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                candle_cv_lc_sparse_add_def] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_add_def] THEN
    REWRITE_TAC[];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_add_def] THEN
    ASM_REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                    candle_cv_lc_sparse_add_def;
                    candle_cv_lc_sparse_insert_correct]]);;

let candle_cv_lc_sparse_scale_correct = prove
 (`!k xs.
     candle_cv_lc_sparse_scale (Cexp_num k)
       (candle_cv_lc_sparse_vec xs) =
     candle_cv_lc_sparse_vec (candle_lc_sparse_scale k xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                candle_cv_lc_sparse_scale_def] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_scale_def] THEN
    REWRITE_TAC[candle_cv_lc_sparse_vec_def];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_scale_def] THEN
    ASM_REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                    candle_cv_lc_sparse_entry_def;
                    candle_cv_lc_sparse_scale_def;
                    cexp_fst_def; cexp_snd_def;
                    candle_cv_lc_zscale_correct]]);;

let candle_cv_lc_sparse_accumulate_correct = prove
 (`!acc lcrow.
     candle_cv_lc_sparse_accumulate
       (candle_cv_lc_sparse_acc acc)
       (candle_cv_lc_sparse_row lcrow) =
     candle_cv_lc_sparse_acc
       (candle_lc_sparse_accumulate acc lcrow)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_lc_sparse_accumulate_def;
              candle_cv_lc_sparse_acc_def;
              candle_cv_lc_sparse_row_def;
              candle_lc_sparse_accumulate_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_lc_sparse_scale_correct;
              candle_cv_lc_sparse_add_correct;
              candle_cv_lc_zscale_correct;
              candle_cv_lc_zadd_correct]);;

let candle_cv_lc_sparse_fold_correct = prove
 (`!lcrows acc.
     candle_cv_lc_sparse_fold
       (candle_cv_lc_sparse_acc acc)
       (candle_cv_lc_sparse_rows lcrows) =
     candle_cv_lc_sparse_acc (candle_lc_sparse_fold acc lcrows)`,
  LIST_INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_fold_def] THEN
    REWRITE_TAC[candle_cv_lc_sparse_rows_def;
                candle_cv_lc_sparse_fold_def];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_fold_def] THEN
    ASM_REWRITE_TAC[candle_cv_lc_sparse_rows_def;
                    candle_cv_lc_sparse_fold_def;
                    candle_cv_lc_sparse_accumulate_correct]]);;

let candle_lc_num_order_eq = prove
 (`!m n:num. (m = n <=> ~(m < n) /\ ~(n < m))`,
  ARITH_TAC);;

let candle_cv_lc_sparse_zero_correct = prove
 (`!xs.
     candle_cv_lc_sparse_zero (candle_cv_lc_sparse_vec xs) =
     Cexp_num (if candle_lc_sparse_zero xs then SUC 0 else 0)`,
  LIST_INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[CONJUNCT1 candle_lc_sparse_zero_def] THEN
    REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                candle_cv_lc_sparse_zero_def];
    ONCE_REWRITE_TAC[CONJUNCT2 candle_lc_sparse_zero_def] THEN
    ASM_CASES_TAC `FST (SND (h:num#(num#num))) < SND (SND h)` THEN
    ASM_CASES_TAC `SND (SND (h:num#(num#num))) < FST (SND h)` THEN
    ASM_REWRITE_TAC[candle_cv_lc_sparse_vec_def;
                    candle_cv_lc_sparse_entry_def;
                    candle_cv_lc_sparse_zero_def;
                    candle_cv_lc_z_def;
                    cexp_fst_def; cexp_snd_def; cexp_less_def;
                    cexp_if_def; injectivity "cval";
                    candle_lc_num_order_eq]]);;

let candle_cv_lc_sparse_infeasible_correct = prove
 (`!acc.
     candle_cv_lc_sparse_infeasible (candle_cv_lc_sparse_acc acc) =
     Cexp_num (if candle_lc_sparse_infeasible acc then SUC 0 else 0)`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_cv_lc_sparse_infeasible_def;
              candle_cv_lc_sparse_acc_def; cexp_fst_def; cexp_snd_def;
              candle_cv_lc_sparse_zero_correct; candle_cv_lc_z_def;
              candle_lc_sparse_infeasible_def] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `candle_lc_sparse_zero
                   (p1:(num#(num#num))list)` THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_less_def]);;

let candle_cv_lc_sparse_fold_verdict_correct = prove
 (`!lcrows acc.
     candle_cv_lc_sparse_fold_verdict
       (candle_cv_lc_sparse_acc acc)
       (candle_cv_lc_sparse_rows lcrows) =
     Cexp_num
       (if candle_lc_sparse_infeasible
             (candle_lc_sparse_fold acc lcrows)
        then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_lc_sparse_fold_verdict_def;
              candle_cv_lc_sparse_fold_correct;
              candle_cv_lc_sparse_infeasible_correct]);;


end;;
