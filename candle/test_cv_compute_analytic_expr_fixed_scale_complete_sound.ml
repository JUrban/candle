needs "candle/cv_compute_analytic_expr_fixed_scale_complete_sound.ml";;

open Candle_cv_analytic_expr_fixed_scale_complete_sound;;

if hyp candle_fs_gradient_bound_contains_error <> [] ||
   hyp candle_fs_gradient_bound_contains <> [] ||
   hyp candle_fs_value_bound_contains_error <> [] ||
   hyp candle_fs_value_bound_contains <> [] then
  failwith "fixed-scale completion soundness test has assumptions";;

print_endline "CANDLE_CV_FIXED_SCALE_COMPLETE_SOUND_OK";;
