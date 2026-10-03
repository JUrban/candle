(* Stable-source fixed-nonlinear proof of 16 genuine action-296 roots. *)

needs "candle/cv_compute_analytic_expr_action296_fixed_nonlinear_variable_forest_prove.ml";;

open Candle_cv_action296_fixed_nonlinear_variable_forest_prove;;

let candle_action296_stratified_16_fixed_nonlinear_variable_leaf =
  Candle_cv_action296_forest_plan.Candle_action296_forest_leaf;;

let candle_action296_stratified_16_fixed_nonlinear_variable_split
    axis left right =
  Candle_cv_action296_forest_plan.Candle_action296_forest_split
    (axis,left,right);;

let candle_action296_stratified_16_fixed_nonlinear_variable_one_split axis =
  candle_action296_stratified_16_fixed_nonlinear_variable_split axis
    candle_action296_stratified_16_fixed_nonlinear_variable_leaf
    candle_action296_stratified_16_fixed_nonlinear_variable_leaf;;

let candle_action296_stratified_16_fixed_nonlinear_variable_roots =
  [(33,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4);
   (99,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (165,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (232,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (298,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (364,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4);
   (431,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4);
   (497,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4);
   (563,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (629,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4);
   (696,
    candle_action296_stratified_16_fixed_nonlinear_variable_split 6
      (candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4)
      candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (762,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 4);
   (828,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (895,candle_action296_stratified_16_fixed_nonlinear_variable_leaf);
   (961,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 1);
   (1027,candle_action296_stratified_16_fixed_nonlinear_variable_one_split 1)];;

let candle_action296_stratified_16_fixed_nonlinear_variable_result =
  candle_action296_fixed_nonlinear_variable_forest_prove
    "stratified-16"
    candle_action296_stratified_16_fixed_nonlinear_variable_roots
    26
    (Some "46bb3598d5d6de465bbb33c34a563f68");;

print_endline
  ("CANDLE_CV_ACTION296_STRATIFIED_16_FIXED_NONLINEAR_VARIABLE_RESULT" ^
   " original_roots=" ^
   string_of_int
     candle_action296_stratified_16_fixed_nonlinear_variable_result.
       fixed_nonlinear_variable_forest_result_original_roots ^
   " final_cells=" ^
   string_of_int
     candle_action296_stratified_16_fixed_nonlinear_variable_result.
       fixed_nonlinear_variable_forest_result_final_cells ^
   " source_preparations=0 computes=1 theorem_digest=" ^
   candle_action296_stratified_16_fixed_nonlinear_variable_result.
     fixed_nonlinear_variable_forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_STRATIFIED_16_FIXED_NONLINEAR_VARIABLE_OK DEVELOPMENT_NON_RELEASE";;
