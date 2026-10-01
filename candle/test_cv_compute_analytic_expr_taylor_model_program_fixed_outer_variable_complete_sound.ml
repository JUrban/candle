needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound.ml";;

module Test_cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound;;

let _ =
  if hyp
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_accept <> []
  then failwith "complete reflected checker: soundness assumptions";
  print_endline
    "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPLETE_SOUND_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
