needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_compact_stack_sound.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_dihedral_compact_stack_sound = struct

open Candle_cv_analytic_expr_case10173_historical_dihedral_compact_stack_sound;;

if hyp candle_case10173_hist_jobs_compact_run_sound <> [] ||
   hyp candle_case10173_hist_jobs_compact_sound <> [] then
  failwith "case10173 historical compact topology: open theorem";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_COMPACT_STACK_SOUND_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
