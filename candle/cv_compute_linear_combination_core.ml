(* ========================================================================== *)
(* Proof-producing exact linear-combination aggregation over cval.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Load after candle/compute.ml. This file only   *)
(* computes normalized coefficient vectors; the separate soundness bridge    *)
(* must connect a successful aggregate to Flyspeck's real inequalities.       *)
(* ========================================================================== *)

module Candle_cv_linear_combination_core = struct

(* A signed integer is represented without subtraction as (positive,negative).
   A vector is dense for this first prototype. A weighted row has shape
   (weight,(coefficients,rhs)), and an accumulator has shape
   (coefficients,rhs). *)

let candle_lc_zadd_def = new_definition
 `candle_lc_zadd (x:num#num) (y:num#num) =
    (FST x + FST y,SND x + SND y)`;;

let candle_lc_zscale_def = new_definition
 `candle_lc_zscale (k:num) (x:num#num) =
    (k * FST x,k * SND x)`;;

let candle_lc_vec_add_def = define
 `(candle_lc_vec_add ([]:(num#num)list) [] = []) /\
  (candle_lc_vec_add [] (CONS y ys) = CONS y ys) /\
  (candle_lc_vec_add (CONS x xs) [] = CONS x xs) /\
  (candle_lc_vec_add (CONS x xs) (CONS y ys) =
     CONS (candle_lc_zadd x y) (candle_lc_vec_add xs ys))`;;

let candle_lc_vec_scale_def = define
 `(candle_lc_vec_scale k ([]:(num#num)list) = []) /\
  (candle_lc_vec_scale k (CONS x xs) =
     CONS (candle_lc_zscale k x) (candle_lc_vec_scale k xs))`;;

let candle_lc_accumulate_def = new_definition
 `candle_lc_accumulate
    (acc:(num#num)list#(num#num))
    (lcrow:num#((num#num)list#(num#num))) =
    (candle_lc_vec_add (FST acc)
       (candle_lc_vec_scale (FST lcrow) (FST (SND lcrow))),
     candle_lc_zadd (SND acc)
       (candle_lc_zscale (FST lcrow) (SND (SND lcrow))))`;;

let candle_lc_fold_def = define
 `(candle_lc_fold acc ([]:(num#((num#num)list#(num#num)))list) = acc) /\
  (candle_lc_fold acc (CONS lcrow rows) =
     candle_lc_fold (candle_lc_accumulate acc lcrow) rows)`;;

(* cval encodings. Cexp_num 0 is the list terminator and Cexp_pair is CONS. *)

let candle_cv_lc_z_def = new_definition
 `candle_cv_lc_z x =
    Cexp_pair (Cexp_num (FST x)) (Cexp_num (SND x))`;;

let candle_cv_lc_vec_def = define
 `(candle_cv_lc_vec ([]:(num#num)list) = Cexp_num 0) /\
  (candle_cv_lc_vec (CONS x xs) =
     Cexp_pair (candle_cv_lc_z x) (candle_cv_lc_vec xs))`;;

let candle_cv_lc_acc_def = new_definition
 `candle_cv_lc_acc acc =
    Cexp_pair (candle_cv_lc_vec (FST acc)) (candle_cv_lc_z (SND acc))`;;

let candle_cv_lc_row_def = new_definition
 `candle_cv_lc_row lcrow =
    Cexp_pair (Cexp_num (FST lcrow)) (candle_cv_lc_acc (SND lcrow))`;;

let candle_cv_lc_rows_def = define
 `(candle_cv_lc_rows ([]:(num#((num#num)list#(num#num)))list) =
     Cexp_num 0) /\
  (candle_cv_lc_rows (CONS lcrow rows) =
     Cexp_pair (candle_cv_lc_row lcrow) (candle_cv_lc_rows rows))`;;

let candle_cv_lc_num_decode_def = define
 `(candle_cv_lc_num_decode (Cexp_num n) = n) /\
  (candle_cv_lc_num_decode (Cexp_pair x y) = 0)`;;

let candle_cv_lc_z_decode_def = define
 `(candle_cv_lc_z_decode (Cexp_num n) = (0,0)) /\
  (candle_cv_lc_z_decode (Cexp_pair x y) =
     (candle_cv_lc_num_decode x,candle_cv_lc_num_decode y))`;;

let candle_cv_lc_vec_decode_def = define
 `(candle_cv_lc_vec_decode (Cexp_num n) = []) /\
  (candle_cv_lc_vec_decode (Cexp_pair x xs) =
     CONS (candle_cv_lc_z_decode x) (candle_cv_lc_vec_decode xs))`;;

let candle_cv_lc_acc_decode_def = define
 `(candle_cv_lc_acc_decode (Cexp_num n) = ([],(0,0))) /\
  (candle_cv_lc_acc_decode (Cexp_pair xs rhs) =
     (candle_cv_lc_vec_decode xs,candle_cv_lc_z_decode rhs))`;;

let candle_cv_lc_z_roundtrip = prove
 (`!x:num#num. candle_cv_lc_z_decode (candle_cv_lc_z x) = x`,
  REWRITE_TAC[candle_cv_lc_z_decode_def; candle_cv_lc_z_def;
              candle_cv_lc_num_decode_def]);;

let candle_cv_lc_vec_roundtrip = prove
 (`!xs:(num#num)list.
     candle_cv_lc_vec_decode (candle_cv_lc_vec xs) = xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_lc_vec_decode_def; candle_cv_lc_vec_def;
                  candle_cv_lc_z_roundtrip]);;

let candle_cv_lc_acc_roundtrip = prove
 (`!acc:(num#num)list#(num#num).
     candle_cv_lc_acc_decode (candle_cv_lc_acc acc) = acc`,
  REWRITE_TAC[candle_cv_lc_acc_decode_def; candle_cv_lc_acc_def;
              candle_cv_lc_vec_roundtrip; candle_cv_lc_z_roundtrip]);;

let candle_cv_lc_zadd_def = new_definition
 `candle_cv_lc_zadd x y =
    Cexp_pair
      (Cexp_add (Cexp_fst x) (Cexp_fst y))
      (Cexp_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_lc_zscale_def = new_definition
 `candle_cv_lc_zscale k x =
    Cexp_pair
      (Cexp_mul k (Cexp_fst x))
      (Cexp_mul k (Cexp_snd x))`;;

let candle_cv_lc_vec_add_def = define
 `(candle_cv_lc_vec_add (Cexp_num m) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_lc_vec_add (Cexp_num m) (Cexp_pair y ys) =
     Cexp_pair y ys) /\
  (candle_cv_lc_vec_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_pair x xs) /\
  (candle_cv_lc_vec_add (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_lc_zadd x y)
               (candle_cv_lc_vec_add xs ys))`;;

let candle_cv_lc_vec_scale_def = define
 `(candle_cv_lc_vec_scale k (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_lc_vec_scale k (Cexp_pair x xs) =
     Cexp_pair (candle_cv_lc_zscale k x)
               (candle_cv_lc_vec_scale k xs))`;;

let candle_cv_lc_accumulate_def = new_definition
 `candle_cv_lc_accumulate acc lcrow =
    Cexp_pair
      (candle_cv_lc_vec_add (Cexp_fst acc)
        (candle_cv_lc_vec_scale (Cexp_fst lcrow)
          (Cexp_fst (Cexp_snd lcrow))))
      (candle_cv_lc_zadd (Cexp_snd acc)
        (candle_cv_lc_zscale (Cexp_fst lcrow)
          (Cexp_snd (Cexp_snd lcrow))))`;;

let candle_cv_lc_fold_def = define
 `(candle_cv_lc_fold acc (Cexp_num n) = acc) /\
  (candle_cv_lc_fold acc (Cexp_pair lcrow rows) =
     candle_cv_lc_fold (candle_cv_lc_accumulate acc lcrow) rows)`;;

(* All-variable equations are the only user equations supplied to the
   verified evaluator. *)

let candle_cv_lc_vec_add_compute = prove
 (`!x y. candle_cv_lc_vec_add x y =
     Cexp_if (Cexp_ispair x)
       (Cexp_if (Cexp_ispair y)
         (Cexp_pair
           (candle_cv_lc_zadd (Cexp_fst x) (Cexp_fst y))
           (candle_cv_lc_vec_add (Cexp_snd x) (Cexp_snd y)))
         x)
       (Cexp_if (Cexp_ispair y) y (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `x:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `y:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_vec_add_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_vec_scale_compute = prove
 (`!k x. candle_cv_lc_vec_scale k x =
     Cexp_if (Cexp_ispair x)
       (Cexp_pair (candle_cv_lc_zscale k (Cexp_fst x))
                  (candle_cv_lc_vec_scale k (Cexp_snd x)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `x:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_vec_scale_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_fold_compute = prove
 (`!acc rows. candle_cv_lc_fold acc rows =
     Cexp_if (Cexp_ispair rows)
       (candle_cv_lc_fold
         (candle_cv_lc_accumulate acc (Cexp_fst rows))
         (Cexp_snd rows))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `rows:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_fold_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_compute_eqs = map SPEC_ALL
 [candle_cv_lc_zadd_def;
  candle_cv_lc_zscale_def;
  candle_cv_lc_vec_add_compute;
  candle_cv_lc_vec_scale_compute;
  candle_cv_lc_accumulate_def;
  candle_cv_lc_fold_compute];;

(* Representation correctness. *)

let candle_cv_lc_zadd_correct = prove
 (`!x y. candle_cv_lc_zadd (candle_cv_lc_z x) (candle_cv_lc_z y) =
          candle_cv_lc_z (candle_lc_zadd x y)`,
  REWRITE_TAC[candle_cv_lc_zadd_def; candle_cv_lc_z_def;
              candle_lc_zadd_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def]);;

let candle_cv_lc_zscale_correct = prove
 (`!k x. candle_cv_lc_zscale (Cexp_num k) (candle_cv_lc_z x) =
          candle_cv_lc_z (candle_lc_zscale k x)`,
  REWRITE_TAC[candle_cv_lc_zscale_def; candle_cv_lc_z_def;
              candle_lc_zscale_def; cexp_fst_def; cexp_snd_def;
              cexp_mul_def]);;

let candle_cv_lc_vec_add_correct = prove
 (`!xs ys. candle_cv_lc_vec_add (candle_cv_lc_vec xs)
                                  (candle_cv_lc_vec ys) =
            candle_cv_lc_vec (candle_lc_vec_add xs ys)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_lc_vec_add_def;
                candle_lc_vec_add_def];
    GEN_TAC THEN
    MP_TAC (ISPEC `ys:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_lc_vec_add_def;
                    candle_lc_vec_add_def; candle_cv_lc_zadd_correct]]);;

let candle_cv_lc_vec_scale_correct = prove
 (`!k xs. candle_cv_lc_vec_scale (Cexp_num k) (candle_cv_lc_vec xs) =
          candle_cv_lc_vec (candle_lc_vec_scale k xs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_lc_vec_scale_def;
                  candle_lc_vec_scale_def; candle_cv_lc_zscale_correct]);;

let candle_cv_lc_accumulate_correct = prove
 (`!acc lcrow.
     candle_cv_lc_accumulate (candle_cv_lc_acc acc)
                             (candle_cv_lc_row lcrow) =
     candle_cv_lc_acc (candle_lc_accumulate acc lcrow)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_lc_accumulate_def; candle_cv_lc_acc_def;
              candle_cv_lc_row_def; candle_lc_accumulate_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_lc_vec_scale_correct;
              candle_cv_lc_vec_add_correct;
              candle_cv_lc_zscale_correct;
              candle_cv_lc_zadd_correct]);;

let candle_cv_lc_fold_correct = prove
 (`!rows acc.
     candle_cv_lc_fold (candle_cv_lc_acc acc) (candle_cv_lc_rows rows) =
     candle_cv_lc_acc (candle_lc_fold acc rows)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_lc_rows_def; candle_cv_lc_fold_def;
                  candle_lc_fold_def; candle_cv_lc_accumulate_correct]);;

end;;
