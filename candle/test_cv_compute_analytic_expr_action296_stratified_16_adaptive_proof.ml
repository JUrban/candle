(* ========================================================================== *)
(* Proof-producing adaptive forest over 16 stratified action-296 NL leaves. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file contains only untrusted split-plan  *)
(* data and a pinned expected result.  The generic adapter rechecks every    *)
(* selected final cell and reconstructs the exact original Flyspeck roots.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_adaptive_forest_prove.ml";;

open Candle_cv_action296_adaptive_forest_prove;;

let candle_action296_stratified_16_leaf =
  Candle_action296_forest_leaf;;

let candle_action296_stratified_16_split axis left right =
  Candle_action296_forest_split (axis,left,right);;

let candle_action296_stratified_16_one_split axis =
  candle_action296_stratified_16_split axis
    candle_action296_stratified_16_leaf
    candle_action296_stratified_16_leaf;;

let candle_action296_stratified_16_roots =
  [(33,candle_action296_stratified_16_one_split 4);
   (99,candle_action296_stratified_16_leaf);
   (165,candle_action296_stratified_16_leaf);
   (232,candle_action296_stratified_16_leaf);
   (298,candle_action296_stratified_16_leaf);
   (364,candle_action296_stratified_16_one_split 4);
   (431,candle_action296_stratified_16_one_split 4);
   (497,candle_action296_stratified_16_one_split 4);
   (563,candle_action296_stratified_16_leaf);
   (629,candle_action296_stratified_16_one_split 4);
   (696,
    candle_action296_stratified_16_split 6
      (candle_action296_stratified_16_one_split 4)
      candle_action296_stratified_16_leaf);
   (762,candle_action296_stratified_16_one_split 4);
   (828,candle_action296_stratified_16_leaf);
   (895,candle_action296_stratified_16_leaf);
   (961,candle_action296_stratified_16_one_split 1);
   (1027,candle_action296_stratified_16_one_split 1)];;

let candle_action296_stratified_16_result =
  candle_action296_adaptive_forest_prove_sequential
    "stratified-16"
    candle_action296_stratified_16_roots
    26
    (Some "46bb3598d5d6de465bbb33c34a563f68");;

print_endline
  ("CANDLE_CV_ACTION296_STRATIFIED_16_ADAPTIVE_PROOF_RESULT" ^
   " original_leaves=" ^
   string_of_int
     candle_action296_stratified_16_result.forest_result_original_roots ^
   " final_cells=" ^
   string_of_int
     candle_action296_stratified_16_result.forest_result_final_cells ^
   " source_preparations=16 computes=16 theorem_digest=" ^
   candle_action296_stratified_16_result.forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_STRATIFIED_16_ADAPTIVE_PROOF_OK DEVELOPMENT_NON_RELEASE";;
