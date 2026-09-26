(* Focused executable checks for the reflected fixed-scale substrate. *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_fixed_scale_compute;;

let candle_cv_fs_test_compute tm =
  candle_q_dim_analytic_jet_compute candle_cv_fs_compute_eqs tm;;

let candle_cv_fs_test_add =
  candle_cv_fs_test_compute
    `candle_cv_fs_add
      (Cexp_pair (Cexp_num 3) (Cexp_num 0))
      (Cexp_pair (Cexp_num 0) (Cexp_num 2))`;;

let candle_cv_fs_test_floor =
  candle_cv_fs_test_compute
    `candle_cv_fs_floor_div
      (Cexp_pair (Cexp_num 0) (Cexp_num 5)) (Cexp_num 2)`;;

let candle_cv_fs_test_ceil =
  candle_cv_fs_test_compute
    `candle_cv_fs_ceil_div
      (Cexp_pair (Cexp_num 0) (Cexp_num 5)) (Cexp_num 2)`;;

let candle_cv_fs_test_mul =
  candle_cv_fs_test_compute
    `candle_cv_fs_raw_interval_mul
      (Cexp_pair
        (Cexp_pair (Cexp_num 0) (Cexp_num 2))
        (Cexp_pair (Cexp_num 3) (Cexp_num 0)))
      (Cexp_pair
        (Cexp_pair (Cexp_num 0) (Cexp_num 4))
        (Cexp_pair (Cexp_num 5) (Cexp_num 0)))`;;

if hyp candle_cv_fs_test_add <> [] ||
   hyp candle_cv_fs_test_floor <> [] ||
   hyp candle_cv_fs_test_ceil <> [] ||
   hyp candle_cv_fs_test_mul <> [] ||
   not
     (aconv (rand (concl candle_cv_fs_test_add))
       `Cexp_pair (Cexp_num 1) (Cexp_num 0)`) ||
   not
     (aconv (rand (concl candle_cv_fs_test_floor))
       `Cexp_pair (Cexp_num 0) (Cexp_num 3)`) ||
   not
     (aconv (rand (concl candle_cv_fs_test_ceil))
       `Cexp_pair (Cexp_num 0) (Cexp_num 2)`) ||
   not
     (aconv (rand (concl candle_cv_fs_test_mul))
       `Cexp_pair
         (Cexp_pair (Cexp_num 0) (Cexp_num 12))
         (Cexp_pair (Cexp_num 15) (Cexp_num 0))`) then
  failwith "reflected fixed-scale focused test failed";;

print_endline "CANDLE_CV_ANALYTIC_EXPR_FIXED_SCALE_COMPUTE_OK";;
