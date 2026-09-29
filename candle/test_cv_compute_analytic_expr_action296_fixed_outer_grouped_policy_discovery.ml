(* ========================================================================== *)
(* Adaptive fixed-outer grouping for a generated action-296 forest policy.   *)
(*                                                                            *)
(* Failed coarse groups are retried at exact smaller group boundaries.  The  *)
(* returned forest is fully proved; its successful sizes are also emitted as *)
(* untrusted scheduling data for independent replay.                          *)
(* ========================================================================== *)

open Candle_cv_action296_stable_grouped_forest_prove;;
open Candle_cv_action296_fixed_outer_grouped_forest_prove;;

let candle_action296_fixed_outer_grouped_result_ref :
    candle_action296_stable_group_result option ref = ref None;;

let _ =
  candle_action296_fixed_outer_grouped_result_ref :=
    Some
      (candle_action296_fixed_outer_grouped_forest_prove
        "generated-fixed-outer-grouped-policy-discovery" 4
        candle_action296_generated_roots
        candle_action296_generated_final_cells
        candle_action296_generated_expected_digest);;

let candle_action296_fixed_outer_grouped_result () =
  match !candle_action296_fixed_outer_grouped_result_ref with
  | Some result -> result
  | None ->
      failwith
        "action296 fixed outer grouping: missing adaptive generated result";;

let _ =
  let result = candle_action296_fixed_outer_grouped_result () in
  let forest = result.stable_group_forest_result in
  print_endline
    ("CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_DISCOVERY_RESULT" ^
     " original_leaves=" ^
     string_of_int forest.forest_result_original_roots ^
     " final_cells=" ^ string_of_int forest.forest_result_final_cells ^
     " attempts=" ^ string_of_int result.stable_group_attempts_total ^
     " successful_groups=" ^
     string_of_int (length result.stable_group_successful_sizes) ^
     " group_sizes=" ^
     String.concat ","
       (map string_of_int result.stable_group_successful_sizes) ^
     " theorem_digest=" ^ forest.forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_DISCOVERY_OK DEVELOPMENT_NON_RELEASE";;
