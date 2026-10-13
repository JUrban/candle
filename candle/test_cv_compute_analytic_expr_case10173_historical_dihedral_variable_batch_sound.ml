needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_variable_batch_sound.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_dihedral_variable_batch_sound = struct

open Candle_cv_analytic_expr_case10173_historical_dihedral_variable_batch_sound;;

let _ = candle_cv_case10173_hist_root_records_def;;
let _ = candle_case10173_hist_job_source_contract_def;;
let _ = candle_case10173_hist_jobs_source_contract_append;;
let _ = candle_case10173_hist_jobs_pass_append;;
let _ = candle_cv_case10173_hist_if_accept_elim;;
let _ = candle_case10173_hist_checked_jobs_source_sound;;

let _ = print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_VARIABLE_BATCH_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
