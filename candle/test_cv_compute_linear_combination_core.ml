needs "candle/compute.ml";;

(* Model the late Flyspeck namespace, where Multivariate/vectors.ml already
   owns the logical constant [rows].  Prototype binders must remain variables
   rather than being captured by an unrelated constant with this name. *)
let candle_cv_lc_test_rows_collision_def = new_definition
 `rows (n:num) = n`;;

needs "candle/cv_compute_linear_combination_core.ml";;
needs "candle/cv_compute_linear_combination.ml";;
needs "candle/cv_compute_linear_combination_sound.ml";;
needs "candle/cv_compute_linear_combination_bulk.ml";;
needs "candle/cv_compute_linear_combination_realize.ml";;

let candle_cv_lc_test_lin_f_def = new_definition
 `candle_cv_lc_test_lin_f terms =
    ITLIST (\tm x. (FST tm) * (SND tm) + x) terms (&0)`;;

needs "candle/cv_compute_linear_combination_reify.ml";;
needs "candle/cv_compute_linear_combination_adapter.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination;;
open Candle_cv_linear_combination_sound;;
open Candle_cv_linear_combination_bulk;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_linear_combination_reify;;
open Candle_cv_linear_combination_adapter;;

let candle_cv_lc_test_rows =
 `[(3,([(2,0);(0,1)],(5,0)));
   (2,([(0,3);(4,0)],(0,7)));
   (5,([(1,1)],(2,9)))]:
   (num#((num#num)list#(num#num)))list`;;

let candle_cv_lc_test_acc =
 `([(0,0);(0,0)],(0,0)):(num#num)list#(num#num)`;;

let candle_cv_lc_test_acc_rep =
  REWRITE_CONV[candle_cv_lc_acc_def; candle_cv_lc_vec_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_acc`,candle_cv_lc_test_acc));;

let candle_cv_lc_test_rows_rep =
  REWRITE_CONV[candle_cv_lc_rows_def; candle_cv_lc_row_def;
               candle_cv_lc_acc_def; candle_cv_lc_vec_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_rows`,candle_cv_lc_test_rows));;

let candle_cv_lc_test_tm =
  mk_comb
    (mk_comb (`candle_cv_lc_fold`,rand (concl candle_cv_lc_test_acc_rep)),
     rand (concl candle_cv_lc_test_rows_rep));;

let candle_cv_lc_test_compute =
  compute candle_cv_lc_compute_eqs candle_cv_lc_test_tm;;

let candle_cv_lc_test_expected =
 `Cexp_pair
   (Cexp_pair (Cexp_pair (Cexp_num 11) (Cexp_num 11))
    (Cexp_pair (Cexp_pair (Cexp_num 8) (Cexp_num 3)) (Cexp_num 0)))
   (Cexp_pair (Cexp_num 25) (Cexp_num 59))`;;

if hyp candle_cv_lc_test_compute <> [] then
  failwith "linear-combination compute theorem has assumptions";;
if not (aconv (rand (concl candle_cv_lc_test_compute))
              candle_cv_lc_test_expected) then
  failwith "linear-combination compute result mismatch";;

let candle_cv_lc_test_correct =
  SPECL [candle_cv_lc_test_rows;candle_cv_lc_test_acc]
        candle_cv_lc_fold_correct;;

if hyp candle_cv_lc_test_correct <> [] then
  failwith "linear-combination representation theorem has assumptions";;

let candle_cv_lc_test_ordinary =
  candle_cv_lc_fold_conv candle_cv_lc_test_acc candle_cv_lc_test_rows;;

let candle_cv_lc_test_ordinary_expected =
 `candle_lc_fold
    ([(0,0);(0,0)],(0,0))
    [(3,([(2,0);(0,1)],(5,0)));
     (2,([(0,3);(4,0)],(0,7)));
     (5,([(1,1)],(2,9)))] =
   ([(11,11);(8,3)],(25,59))`;;

if hyp candle_cv_lc_test_ordinary <> [] then
  failwith "ordinary linear-combination theorem has assumptions";;
if not (aconv (concl candle_cv_lc_test_ordinary)
              candle_cv_lc_test_ordinary_expected) then
  failwith "ordinary linear-combination theorem interface mismatch";;

if hyp candle_lc_real_accumulate_sound <> [] ||
   hyp candle_lc_real_fold_sound <> [] ||
   hyp candle_lc_real_fold_from_zero <> []
then failwith "linear-combination soundness theorem has assumptions";;

let candle_cv_lc_bulk_left = ASSUME `x:real <= &3`;;
let candle_cv_lc_bulk_right = ASSUME `y:real <= &4`;;
let candle_cv_lc_bulk_test =
  candle_lc_bulk_inequality
    [(candle_cv_lc_bulk_left,`2`);(candle_cv_lc_bulk_right,`3`)];;
let candle_cv_lc_bulk_expected =
 `FST
    (candle_lc_real_fold (&0,&0)
      [(2,(x:real,&3));(3,(y:real,&4))]) <=
  SND
    (candle_lc_real_fold (&0,&0)
      [(2,(x:real,&3));(3,(y:real,&4))])`;;

if not (aconv (concl candle_cv_lc_bulk_test) candle_cv_lc_bulk_expected) then
  failwith "bulk linear-combination conclusion mismatch";;
if not (set_eq (hyp candle_cv_lc_bulk_test) [`x:real <= &3`; `y:real <= &4`])
then failwith "bulk linear-combination hypotheses mismatch";;

if hyp candle_lc_zreal_add <> [] ||
   hyp candle_lc_zreal_scale <> [] ||
   hyp candle_lc_vec_real_add <> [] ||
   hyp candle_lc_vec_real_scale <> [] ||
   hyp candle_lc_accumulate_real <> [] ||
   hyp candle_lc_fold_real <> []
then failwith "linear-combination realization theorem has assumptions";;

let candle_cv_lc_real_test =
  SPECL [candle_cv_lc_test_rows; `[x:real;y]`; candle_cv_lc_test_acc]
        candle_lc_fold_real;;

if hyp candle_cv_lc_real_test <> [] then
  failwith "linear-combination fold realization has assumptions";;

let candle_cv_lc_test_variables = [`x:real`; `y:real`; `z:real`];;
let candle_cv_lc_test_lhs =
 `candle_cv_lc_test_lin_f [(&2,x:real); (-- &3,z:real)]`;;
let candle_cv_lc_test_coefficients,candle_cv_lc_test_reification =
  candle_lc_reify_lin_f_with
    Term.(<) `candle_cv_lc_test_lin_f` candle_cv_lc_test_lin_f_def
    dest_realintconst [] candle_cv_lc_test_variables
    candle_cv_lc_test_lhs;;

if not (aconv candle_cv_lc_test_coefficients
              `[(2,0); (0,0); (0,3)]`) then
  failwith "linear-combination reifier coefficient mismatch";;
if hyp candle_cv_lc_test_reification <> [] ||
   not (aconv (concl candle_cv_lc_test_reification)
         `candle_lc_vec_real [x:real;y;z] [(2,0);(0,0);(0,3)] =
          candle_cv_lc_test_lin_f [(&2,x);(-- &3,z)]`) then
  failwith "linear-combination reifier theorem mismatch";;

let candle_cv_lc_reifier_rejects variables lhs =
  try
    let _ =
      candle_lc_reify_lin_f_with
        Term.(<) `candle_cv_lc_test_lin_f` candle_cv_lc_test_lin_f_def
        dest_realintconst [] variables lhs in
    false
  with Failure _ -> true;;

if not
     (candle_cv_lc_reifier_rejects candle_cv_lc_test_variables
        `candle_cv_lc_test_lin_f [(&1,x:real);(&2,x:real)]`) then
  failwith "linear-combination reifier accepted duplicate variables";;
if not
     (candle_cv_lc_reifier_rejects candle_cv_lc_test_variables
        `candle_cv_lc_test_lin_f [(&1,w:real)]`) then
  failwith "linear-combination reifier accepted an out-of-basis variable";;
if not
     (candle_cv_lc_reifier_rejects [`y:real`; `x:real`; `z:real`]
        candle_cv_lc_test_lhs) then
  failwith "linear-combination reifier accepted an unsorted basis";;

let candle_cv_lc_test_lhs2 =
 `candle_cv_lc_test_lin_f [(&1,y:real)]`;;
let candle_cv_lc_test_ineq1 =
  ASSUME
   `candle_cv_lc_test_lin_f [(&2,x:real);(-- &3,z)] <= &7`;;
let candle_cv_lc_test_ineq2 =
  ASSUME `candle_cv_lc_test_lin_f [(&1,y:real)] <= -- &1`;;
let candle_cv_lc_test_reify_lhs lhs =
  candle_lc_reify_lin_f_with
    Term.(<) `candle_cv_lc_test_lin_f` candle_cv_lc_test_lin_f_def
    dest_realintconst [] candle_cv_lc_test_variables lhs;;
let candle_cv_lc_test_reify_rhs rhs =
  candle_lc_reify_integer_with
    candle_cv_lc_test_lin_f_def dest_realintconst [] rhs;;
let candle_cv_lc_test_result,candle_cv_lc_test_bulk_th =
  candle_lc_bulk_compute_with
    candle_cv_lc_test_variables
    candle_cv_lc_test_reify_lhs candle_cv_lc_test_reify_rhs
    [(candle_cv_lc_test_ineq1,`3`);
     (candle_cv_lc_test_ineq2,`4`)];;

if not (aconv candle_cv_lc_test_result
              `([(6,0);(4,0);(0,9)],(17,0))`) ||
   not (set_eq (hyp candle_cv_lc_test_bulk_th)
          [concl candle_cv_lc_test_ineq1;concl candle_cv_lc_test_ineq2]) ||
   not (aconv (concl candle_cv_lc_test_bulk_th)
         `candle_lc_vec_real [x:real;y;z] [(6,0);(4,0);(0,9)] <=
          candle_lc_zreal (17,0)`) then
  failwith "linear-combination computed adapter mismatch";;

print_endline "CANDLE_CV_LINEAR_COMBINATION_CORE_OK";;
