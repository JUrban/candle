(* ========================================================================== *)
(* Ordinary HOL theorem adapters for reflected exact rational arithmetic.    *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_core.ml";;

module Candle_cv_exact_rational = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;

let candle_cv_q_encode_conv tm =
  REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def] tm;;

let candle_cv_q_interval_encode_conv tm =
  REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
               candle_cv_lc_z_def] tm;;

let candle_cv_q_decode_rule th =
  REWRITE_RULE[candle_cv_q_roundtrip;
               candle_cv_q_decode_def;
               candle_cv_lc_z_decode_def;
               candle_cv_lc_num_decode_def] th;;

let candle_cv_q_interval_decode_rule th =
  REWRITE_RULE[candle_cv_q_interval_roundtrip;
               candle_cv_q_interval_decode_def;
               candle_cv_q_decode_def;
               candle_cv_lc_z_decode_def;
               candle_cv_lc_num_decode_def] th;;

let candle_cv_q_binary_conv cv_op correctness_th x_tm y_tm =
  let x_rep_th =
    candle_cv_q_encode_conv (mk_comb (`candle_cv_q`,x_tm)) in
  let y_rep_th =
    candle_cv_q_encode_conv (mk_comb (`candle_cv_q`,y_tm)) in
  let x_cv_tm = rand (concl x_rep_th) and
      y_cv_tm = rand (concl y_rep_th) in
  let compute_tm = mk_comb (mk_comb (cv_op,x_cv_tm),y_cv_tm) in
  let compute_th = compute candle_cv_q_compute_eqs compute_tm in
  let correctness_th = SPECL [x_tm;y_tm] correctness_th in
  let lhs_bridge_th =
    MK_COMB (AP_TERM cv_op x_rep_th,y_rep_th) in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS lhs_bridge_th compute_th) in
  candle_cv_q_decode_rule
    (AP_TERM `candle_cv_q_decode` encoded_result_th);;

let candle_cv_q_unary_conv cv_op correctness_th x_tm =
  let x_rep_th =
    candle_cv_q_encode_conv (mk_comb (`candle_cv_q`,x_tm)) in
  let x_cv_tm = rand (concl x_rep_th) in
  let compute_tm = mk_comb (cv_op,x_cv_tm) in
  let compute_th = compute candle_cv_q_compute_eqs compute_tm in
  let correctness_th = SPEC x_tm correctness_th in
  let lhs_bridge_th = AP_TERM cv_op x_rep_th in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS lhs_bridge_th compute_th) in
  candle_cv_q_decode_rule
    (AP_TERM `candle_cv_q_decode` encoded_result_th);;

let candle_q_add_conv =
  candle_cv_q_binary_conv `candle_cv_q_add` candle_cv_q_add_correct;;

let candle_q_mul_conv =
  candle_cv_q_binary_conv `candle_cv_q_mul` candle_cv_q_mul_correct;;

let candle_q_neg_conv =
  candle_cv_q_unary_conv `candle_cv_q_neg` candle_cv_q_neg_correct;;

let candle_cv_q_interval_binary_conv cv_op correctness_th x_tm y_tm =
  let x_rep_th =
    candle_cv_q_interval_encode_conv
      (mk_comb (`candle_cv_q_interval`,x_tm)) in
  let y_rep_th =
    candle_cv_q_interval_encode_conv
      (mk_comb (`candle_cv_q_interval`,y_tm)) in
  let x_cv_tm = rand (concl x_rep_th) and
      y_cv_tm = rand (concl y_rep_th) in
  let compute_tm = mk_comb (mk_comb (cv_op,x_cv_tm),y_cv_tm) in
  let compute_th = compute candle_cv_q_interval_compute_eqs compute_tm in
  let correctness_th = SPECL [x_tm;y_tm] correctness_th in
  let lhs_bridge_th =
    MK_COMB (AP_TERM cv_op x_rep_th,y_rep_th) in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS lhs_bridge_th compute_th) in
  candle_cv_q_interval_decode_rule
    (AP_TERM `candle_cv_q_interval_decode` encoded_result_th);;

let candle_cv_q_interval_unary_conv cv_op correctness_th x_tm =
  let x_rep_th =
    candle_cv_q_interval_encode_conv
      (mk_comb (`candle_cv_q_interval`,x_tm)) in
  let x_cv_tm = rand (concl x_rep_th) in
  let compute_tm = mk_comb (cv_op,x_cv_tm) in
  let compute_th = compute candle_cv_q_interval_compute_eqs compute_tm in
  let correctness_th = SPEC x_tm correctness_th in
  let lhs_bridge_th = AP_TERM cv_op x_rep_th in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS lhs_bridge_th compute_th) in
  candle_cv_q_interval_decode_rule
    (AP_TERM `candle_cv_q_interval_decode` encoded_result_th);;

let candle_q_interval_add_conv =
  candle_cv_q_interval_binary_conv
    `candle_cv_q_interval_add` candle_cv_q_interval_add_correct;;

let candle_q_interval_neg_conv =
  candle_cv_q_interval_unary_conv
    `candle_cv_q_interval_neg` candle_cv_q_interval_neg_correct;;

end;;
