needs "candle/cv_compute_analytic_expr_case10173_historical_source_contract.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_source_contract = struct

open Candle_cv_analytic_expr_case10173_historical_source_contract;;

if hyp candle_case10173_hist_authenticated_source_compile_patch <> [] ||
   hyp candle_case10173_hist_patched_context_valid <> [] ||
   hyp candle_case10173_hist_patched_context_splice <> [] ||
   hyp candle_case10173_hist_authenticated_job_source_contract <> [] ||
   hyp candle_case10173_hist_authenticated_source_sqrt_count <> [] then
  failwith "case10173 historical source contract: open theorem";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_SOURCE_CONTRACT_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
