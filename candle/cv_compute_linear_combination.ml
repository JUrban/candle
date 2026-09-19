(* ========================================================================== *)
(* Ordinary theorem adapter for exact cval linear-combination aggregation.    *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_core.ml";;

module Candle_cv_linear_combination = struct

open Candle_cv_linear_combination_core;;

let candle_cv_lc_acc_encode_conv tm =
  REWRITE_CONV[candle_cv_lc_acc_def; candle_cv_lc_vec_def;
               candle_cv_lc_z_def] tm;;

let candle_cv_lc_rows_encode_conv tm =
  REWRITE_CONV[candle_cv_lc_rows_def; candle_cv_lc_row_def;
               candle_cv_lc_acc_def; candle_cv_lc_vec_def;
               candle_cv_lc_z_def] tm;;

let candle_cv_lc_fold_conv acc_tm rows_tm =
  let acc_rep_th =
    candle_cv_lc_acc_encode_conv (mk_comb (`candle_cv_lc_acc`,acc_tm)) in
  let rows_rep_th =
    candle_cv_lc_rows_encode_conv (mk_comb (`candle_cv_lc_rows`,rows_tm)) in
  let acc_cv_tm = rand (concl acc_rep_th) and
      rows_cv_tm = rand (concl rows_rep_th) in
  let compute_tm = mk_comb (mk_comb (`candle_cv_lc_fold`,acc_cv_tm),rows_cv_tm) in
  let compute_th = compute candle_cv_lc_compute_eqs compute_tm in
  let correctness_th = SPECL [rows_tm;acc_tm] candle_cv_lc_fold_correct in
  let lhs_bridge_th =
    MK_COMB (AP_TERM `candle_cv_lc_fold` acc_rep_th,rows_rep_th) in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS lhs_bridge_th compute_th) in
  let decoded_result_th =
    AP_TERM `candle_cv_lc_acc_decode` encoded_result_th in
  REWRITE_RULE[candle_cv_lc_acc_roundtrip;
               candle_cv_lc_acc_decode_def;
               candle_cv_lc_vec_decode_def;
               candle_cv_lc_z_decode_def;
               candle_cv_lc_num_decode_def] decoded_result_th;;

end;;
