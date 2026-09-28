(* Replay a generated action-296 policy through stable-source proof batches. *)

open Candle_cv_action296_stable_grouped_forest_prove;;

let candle_action296_stable_grouped_result_ref :
    candle_action296_stable_group_result option ref = ref None;;

let _ =
  candle_action296_stable_grouped_result_ref :=
    Some
      (candle_action296_stable_grouped_forest_prove_sizes
        "generated-stable-grouped-policy"
        candle_action296_generated_group_sizes
        candle_action296_generated_roots
        candle_action296_generated_final_cells
        candle_action296_generated_expected_digest);;

let candle_action296_stable_grouped_result () =
  match !candle_action296_stable_grouped_result_ref with
  | Some result -> result
  | None -> failwith "action296 stable grouping: missing generated result";;

let _ =
  let result = candle_action296_stable_grouped_result () in
  let forest = result.stable_group_forest_result in
  print_endline
    ("CANDLE_CV_ACTION296_STABLE_GROUPED_POLICY_RESULT" ^
     " original_leaves=" ^
     string_of_int forest.forest_result_original_roots ^
     " final_cells=" ^ string_of_int forest.forest_result_final_cells ^
     " batches=" ^ string_of_int result.stable_group_attempts_total ^
     " stable_programs=1 group_sizes=" ^
     String.concat ","
       (map string_of_int result.stable_group_successful_sizes) ^
     " theorem_digest=" ^ forest.forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_STABLE_GROUPED_POLICY_OK DEVELOPMENT_NON_RELEASE";;
