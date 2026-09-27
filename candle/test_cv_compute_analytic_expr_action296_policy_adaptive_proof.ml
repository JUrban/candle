(* ========================================================================== *)
(* Proof-producing adapter for a generated untrusted action-296 forest plan. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A preceding fragment must define             *)
(* [candle_action296_generated_roots], [_final_cells], and                    *)
(* [_expected_digest].  Every selected cell and original root is rechecked.  *)
(* ========================================================================== *)

open Candle_cv_action296_adaptive_forest_prove;;

let candle_action296_generated_result_ref :
    candle_action296_forest_result option ref = ref None;;

let _ =
  candle_action296_generated_result_ref :=
    Some
      (candle_action296_adaptive_forest_prove_sequential
        "generated-policy"
        candle_action296_generated_roots
        candle_action296_generated_final_cells
        candle_action296_generated_expected_digest);;

let candle_action296_generated_result () =
  match !candle_action296_generated_result_ref with
  | Some result -> result
  | None -> failwith "action296 generated policy: result unavailable";;

let _ =
  let result = candle_action296_generated_result () in
  print_endline
    ("CANDLE_CV_ACTION296_POLICY_ADAPTIVE_PROOF_RESULT" ^
     " original_leaves=" ^
     string_of_int result.forest_result_original_roots ^
     " final_cells=" ^
     string_of_int result.forest_result_final_cells ^
     " theorem_digest=" ^ result.forest_result_digest);;
print_endline
  "CANDLE_CV_ACTION296_POLICY_ADAPTIVE_PROOF_OK DEVELOPMENT_NON_RELEASE";;
