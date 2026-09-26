needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;

open Candle_cv_analytic_expr_fixed_scale_invariant;;

if hyp candle_fs_dot_list_real_vector_sum <> [] ||
   hyp candle_fs_weighted_rows_list_real_vector_sum <> [] ||
   hyp candle_fs_complete_m_taylor_error_sound <> [] ||
   hyp candle_fs_complete_m_taylor_partial_error_sound <> [] ||
   hyp candle_fs_gradient_bounds_el <> [] ||
   hyp candle_fs_result_complete_domain <> [] ||
   hyp candle_fs_result_complete_proxy <> [] then
  failwith "fixed-scale invariant structural test has assumptions";;

print_endline "CANDLE_CV_FIXED_SCALE_INVARIANT_OK";;
