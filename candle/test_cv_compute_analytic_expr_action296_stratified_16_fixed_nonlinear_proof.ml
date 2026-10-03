(* ========================================================================== *)
(* Fixed-nonlinear proof of 16 stratified genuine action-296 roots.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_fixed_nonlinear_forest_prove.ml";;

open Candle_cv_action296_fixed_nonlinear_forest_prove;;

let candle_action296_stratified_16_fixed_nonlinear_leaf =
  Candle_cv_action296_forest_plan.Candle_action296_forest_leaf;;

let candle_action296_stratified_16_fixed_nonlinear_split axis left right =
  Candle_cv_action296_forest_plan.Candle_action296_forest_split
    (axis,left,right);;

let candle_action296_stratified_16_fixed_nonlinear_one_split axis =
  candle_action296_stratified_16_fixed_nonlinear_split axis
    candle_action296_stratified_16_fixed_nonlinear_leaf
    candle_action296_stratified_16_fixed_nonlinear_leaf;;

let candle_action296_stratified_16_fixed_nonlinear_roots =
  [(33,candle_action296_stratified_16_fixed_nonlinear_one_split 4);
   (99,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (165,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (232,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (298,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (364,candle_action296_stratified_16_fixed_nonlinear_one_split 4);
   (431,candle_action296_stratified_16_fixed_nonlinear_one_split 4);
   (497,candle_action296_stratified_16_fixed_nonlinear_one_split 4);
   (563,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (629,candle_action296_stratified_16_fixed_nonlinear_one_split 4);
   (696,
    candle_action296_stratified_16_fixed_nonlinear_split 6
      (candle_action296_stratified_16_fixed_nonlinear_one_split 4)
      candle_action296_stratified_16_fixed_nonlinear_leaf);
   (762,candle_action296_stratified_16_fixed_nonlinear_one_split 4);
   (828,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (895,candle_action296_stratified_16_fixed_nonlinear_leaf);
   (961,candle_action296_stratified_16_fixed_nonlinear_one_split 1);
   (1027,candle_action296_stratified_16_fixed_nonlinear_one_split 1)];;

let candle_action296_stratified_16_fixed_nonlinear_result =
  candle_action296_fixed_nonlinear_forest_prove_sequential
    "stratified-16"
    candle_action296_stratified_16_fixed_nonlinear_roots
    26
    (Some "46bb3598d5d6de465bbb33c34a563f68");;

print_endline
  ("CANDLE_CV_ACTION296_STRATIFIED_16_FIXED_NONLINEAR_RESULT" ^
   " original_roots=" ^
   string_of_int
     candle_action296_stratified_16_fixed_nonlinear_result.
       fixed_nonlinear_forest_result_original_roots ^
   " final_cells=" ^
   string_of_int
     candle_action296_stratified_16_fixed_nonlinear_result.
       fixed_nonlinear_forest_result_final_cells ^
   " source_preparations=16 computes=26 theorem_digest=" ^
   candle_action296_stratified_16_fixed_nonlinear_result.
     fixed_nonlinear_forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_STRATIFIED_16_FIXED_NONLINEAR_OK DEVELOPMENT_NON_RELEASE";;
