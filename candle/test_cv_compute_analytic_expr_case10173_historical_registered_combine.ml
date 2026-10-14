needs "candle/cv_compute_analytic_expr_case10173_historical_registered_combine.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_registered_combine = struct

open Candle_cv_analytic_expr_case10173_historical_registered_combine;;

let candle_case10173_hist_registered_split_fixture =
  `Cexp_pair
     (Cexp_pair (Cexp_num 1) (Cexp_num 1))
     (Cexp_pair (Cexp_num 1) (Cexp_num 1))`;;

let candle_case10173_hist_registered_split_leaves =
  candle_case10173_hist_registered_pair_result_leaves
    (REFL candle_case10173_hist_registered_split_fixture);;

if length candle_case10173_hist_registered_split_leaves <> 4 ||
   not
     (List.for_all
       (fun theorem ->
         hyp theorem = [] &&
         aconv (lhand (concl theorem)) `Cexp_num 1` &&
         aconv (rand (concl theorem)) `Cexp_num 1`)
       candle_case10173_hist_registered_split_leaves)
then failwith "case10173 registered combine test: pair split mismatch";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_COMBINE_TEST_OK DEVELOPMENT_NON_RELEASE leaves=4";;

end;;
