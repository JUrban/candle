(* ========================================================================== *)
(* Dynamic bounded-group discovery for a generated action-296 policy.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A failed coarse group is retried through      *)
(* smaller exact groups.  The emitted successful sizes are untrusted plan     *)
(* data for a later independent digest-pinned replay.                         *)
(* ========================================================================== *)

open Candle_cv_action296_bounded_grouped_forest_prove;;

let candle_action296_bounded_grouped_discovery_ref :
    candle_action296_bounded_group_result option ref = ref None;;

let _ =
  candle_action296_bounded_grouped_discovery_ref :=
    Some
      (candle_action296_bounded_grouped_forest_prove
        "bounded-generated-policy-discovery" 4
        candle_action296_generated_roots
        candle_action296_generated_final_cells
        candle_action296_generated_expected_digest);;

let candle_action296_bounded_grouped_discovery () =
  match !candle_action296_bounded_grouped_discovery_ref with
  | Some result -> result
  | None -> failwith "action296 bounded grouping: missing discovery result";;

let _ =
  let result = candle_action296_bounded_grouped_discovery () in
  let forest = result.bounded_group_forest_result in
  print_endline
    ("CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_RESULT" ^
     " original_leaves=" ^
     string_of_int forest.forest_result_original_roots ^
     " final_cells=" ^ string_of_int forest.forest_result_final_cells ^
     " attempts=" ^ string_of_int result.bounded_group_attempts_total ^
     " successful_groups=" ^
     string_of_int result.bounded_group_successes_total ^
     " group_sizes=" ^
     String.concat ","
       (map string_of_int result.bounded_group_successful_sizes) ^
     " theorem_digest=" ^ forest.forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_OK DEVELOPMENT_NON_RELEASE";;
