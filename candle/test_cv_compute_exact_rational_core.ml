needs "candle/compute.ml";;
needs "candle/cv_compute_exact_rational_core.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;

let candle_cv_q_test_x = `((3,1),4):(num#num)#num`;;
let candle_cv_q_test_y = `((2,5),2):(num#num)#num`;;

let candle_cv_q_test_x_rep =
  REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q`,candle_cv_q_test_x));;
let candle_cv_q_test_y_rep =
  REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q`,candle_cv_q_test_y));;

let candle_cv_q_test_compute op =
  compute candle_cv_q_compute_eqs
    (mk_comb
      (mk_comb (op,rand (concl candle_cv_q_test_x_rep)),
       rand (concl candle_cv_q_test_y_rep)));;

let candle_cv_q_test_add = candle_cv_q_test_compute `candle_cv_q_add`;;
let candle_cv_q_test_mul = candle_cv_q_test_compute `candle_cv_q_mul`;;

let candle_cv_q_test_add_expected =
 `Cexp_pair (Cexp_pair (Cexp_num 19) (Cexp_num 28)) (Cexp_num 14)`;;
let candle_cv_q_test_mul_expected =
 `Cexp_pair (Cexp_pair (Cexp_num 11) (Cexp_num 17)) (Cexp_num 14)`;;

if hyp candle_cv_q_test_add <> [] ||
   not (aconv (rand (concl candle_cv_q_test_add))
              candle_cv_q_test_add_expected)
then failwith "exact-rational addition compute mismatch";;
if hyp candle_cv_q_test_mul <> [] ||
   not (aconv (rand (concl candle_cv_q_test_mul))
              candle_cv_q_test_mul_expected)
then failwith "exact-rational multiplication compute mismatch";;

let candle_cv_q_test_neg =
  compute candle_cv_q_compute_eqs
    (mk_comb (`candle_cv_q_neg`,rand (concl candle_cv_q_test_x_rep)));;
if hyp candle_cv_q_test_neg <> [] ||
   not (aconv (rand (concl candle_cv_q_test_neg))
       `Cexp_pair (Cexp_pair (Cexp_num 1) (Cexp_num 3)) (Cexp_num 4)`)
then failwith "exact-rational negation compute mismatch";;

if hyp candle_cv_q_roundtrip <> [] ||
   hyp candle_cv_q_add_correct <> [] ||
   hyp candle_cv_q_mul_correct <> [] ||
   hyp candle_cv_q_neg_correct <> [] ||
   hyp candle_q_real_add <> [] ||
   hyp candle_q_real_mul <> [] ||
   hyp candle_q_real_neg <> [] ||
   hyp candle_q_interval_add_sound <> [] ||
   hyp candle_q_interval_neg_sound <> []
then failwith "exact-rational correctness theorem has assumptions";;

let candle_cv_q_test_add_correct =
  SPECL [candle_cv_q_test_x;candle_cv_q_test_y] candle_cv_q_add_correct;;
let candle_cv_q_test_mul_real =
  SPECL [candle_cv_q_test_x;candle_cv_q_test_y] candle_q_real_mul;;

if not
   (aconv (concl candle_cv_q_test_add_correct)
      `candle_cv_q_add (candle_cv_q ((3,1),4))
                       (candle_cv_q ((2,5),2)) =
       candle_cv_q (candle_q_add ((3,1),4) ((2,5),2))`)
then failwith "exact-rational representation theorem mismatch";;
if not
   (aconv (concl candle_cv_q_test_mul_real)
      `candle_q_real (candle_q_mul ((3,1),4) ((2,5),2)) =
       candle_q_real ((3,1),4) * candle_q_real ((2,5),2)`)
then failwith "exact-rational real theorem mismatch";;

print_endline "CANDLE_CV_EXACT_RATIONAL_CORE_OK";;
