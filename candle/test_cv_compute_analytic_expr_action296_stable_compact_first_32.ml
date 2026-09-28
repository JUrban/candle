(* Focused authentic first-32 test for the stable compact-tree adapter. *)

needs "candle/cv_compute_analytic_expr_action296_stable_compact_grouped_forest_prove.ml";;

open Candle_cv_action296_stable_compact_grouped_forest_prove;;
open Candle_cv_action296_stable_grouped_forest_prove;;

let rec candle_action296_stable_compact_take count items =
  if count <= 0 then [] else
  match items with
  | [] -> failwith "action296 stable compact first 32: short input"
  | head :: tail ->
      head :: candle_action296_stable_compact_take (count - 1) tail;;

let candle_action296_stable_compact_first_32_roots =
  candle_action296_stable_compact_take
    32 candle_action296_generated_roots;;

let candle_action296_stable_compact_first_32_sizes =
  candle_action296_stable_compact_take
    18 candle_action296_generated_group_sizes;;

if List.fold_left (+) 0
     candle_action296_stable_compact_first_32_sizes <> 32 then
  failwith "action296 stable compact first 32: schedule drift";;

let candle_action296_stable_compact_first_32_result =
  candle_action296_stable_compact_grouped_forest_prove_sizes
    "generated-stable-compact-first-32"
    candle_action296_stable_compact_first_32_sizes
    candle_action296_stable_compact_first_32_roots
    49 (Some "7f5df8d12a23b58b73fee9e254b83753");;

let candle_action296_stable_compact_first_32_forest =
  candle_action296_stable_compact_first_32_result.
    stable_group_forest_result;;

print_endline
  ("CANDLE_CV_ACTION296_STABLE_COMPACT_FIRST_32_RESULT" ^
   " original_leaves=" ^
     string_of_int
       candle_action296_stable_compact_first_32_forest.
         forest_result_original_roots ^
   " final_cells=" ^
     string_of_int
       candle_action296_stable_compact_first_32_forest.
         forest_result_final_cells ^
   " batches=" ^
     string_of_int
       candle_action296_stable_compact_first_32_result.
         stable_group_attempts_total ^
   " theorem_digest=" ^
     candle_action296_stable_compact_first_32_forest.
       forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_STABLE_COMPACT_FIRST_32_OK DEVELOPMENT_NON_RELEASE";;
