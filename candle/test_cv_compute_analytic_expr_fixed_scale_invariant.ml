needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;

open Candle_cv_analytic_expr_fixed_scale_invariant;;

if hyp candle_fs_gradient_bounds_el <> [] ||
   hyp candle_fs_result_complete_domain <> [] ||
   hyp candle_fs_result_complete_proxy <> [] then
  failwith "fixed-scale invariant structural test has assumptions";;

print_endline "CANDLE_CV_FIXED_SCALE_INVARIANT_OK";;
