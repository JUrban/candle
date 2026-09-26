needs "candle/cv_compute_analytic_expr_fixed_scale_accept.ml";;

open Candle_cv_analytic_expr_fixed_scale_accept;;

if hyp candle_cv_fs_poly_check_correct <> [] ||
   hyp candle_fs_poly_upper_sound <> [] ||
   hyp candle_fs_poly_numerical_accept_sound <> [] ||
   hyp candle_fs_poly_batch_numerical_accept_mem <> [] ||
   hyp candle_fs_poly_batch_sound <> [] ||
   hyp candle_cv_fs_poly_batch_check_compute <> [] ||
   hyp candle_cv_fs_poly_batch_check_correct <> [] then
  failwith "fixed-scale acceptance theorem has assumptions";;

print_endline "CANDLE_CV_FIXED_SCALE_ACCEPT_OK";;
