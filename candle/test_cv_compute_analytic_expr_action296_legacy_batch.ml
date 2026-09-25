(* ========================================================================== *)
(* Legacy proofs for the first four genuine action-296 certificate leaves.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the cold recurring-cost baseline for  *)
(* the certified centered Taylor-model batch over the same logical leaves.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;

open Certificate;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;

let candle_action296_legacy_batch_axioms_before = axioms ();;
let candle_action296_legacy_batch_size = 4;;

let candle_action296_legacy_batch_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_legacy_batch_collect remaining domain_th tree =
  if remaining = 0 then 0,[] else
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      remaining - 1,[status,function_index,raw_flag,domain_th]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "action296 legacy batch: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      let after_left,left_leaves =
        candle_action296_legacy_batch_collect remaining left_domain left in
      let after_right,right_leaves =
        candle_action296_legacy_batch_collect after_left right_domain right in
      after_right,left_leaves @ right_leaves
  | P_result_mono _ ->
      failwith "action296 legacy batch: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 legacy batch: unexpected reference node";;

let candle_action296_legacy_batch_remaining,
    candle_action296_legacy_batch_leaves =
  candle_action296_legacy_batch_collect candle_action296_legacy_batch_size
    candle_action296_legacy_batch_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_legacy_batch_remaining <> 0 ||
   length candle_action296_legacy_batch_leaves <>
     candle_action296_legacy_batch_size ||
   not
     (List.for_all
       (fun (_,function_index,raw_flag,_) ->
         function_index = 0 && not raw_flag)
       candle_action296_legacy_batch_leaves) then
  failwith "action296 legacy batch: selected leaves drift";;

let rec candle_action296_legacy_batch_prove index leaves =
  match leaves with
  | [] -> []
  | (status,function_index,raw_flag,domain_th) :: tail ->
      let certificate =
        P_result_pass (status,function_index,raw_flag) in
      print_endline
        ("CANDLE_CV_ACTION296_LEGACY_BATCH_LEAF leaf=" ^
         string_of_int index ^ " event=begin");
      let theorem =
        M_verifier.m_p_verify_disj_raw
          (0,0) candle_action296_plan_dimension 6
          candle_action296_plan_formal_functions certificate domain_th [] in
      let functions,proved_domain =
        M_verifier.dest_m_cell_list_pass (concl theorem) in
      let expected_domain,_,_ =
        M_taylor.dest_m_cell_domain (concl domain_th) in
      if functions <> [candle_action296_plan_prepared.function_term] ||
         not (aconv proved_domain expected_domain) ||
         hyp theorem <> [] then
        failwith "action296 legacy batch: leaf theorem mismatch";
      print_endline
        ("CANDLE_CV_ACTION296_LEGACY_BATCH_LEAF leaf=" ^
         string_of_int index ^ " event=end theorem_md5=" ^
         Digest.to_hex (Digest.string (string_of_thm theorem)));
      theorem :: candle_action296_legacy_batch_prove (index + 1) tail;;

let candle_action296_legacy_batch_theorems =
  candle_action296_legacy_batch_prove 0 candle_action296_legacy_batch_leaves;;

let candle_action296_legacy_batch_axioms_after = axioms ();;

if length candle_action296_legacy_batch_theorems <>
     candle_action296_legacy_batch_size ||
   length candle_action296_legacy_batch_axioms_after <>
     length candle_action296_legacy_batch_axioms_before ||
   not
     (List.for_all
       (fun theorem -> List.mem theorem candle_action296_legacy_batch_axioms_before)
       candle_action296_legacy_batch_axioms_after) then
  failwith "action296 legacy batch: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_LEGACY_BATCH_RESULT leaves=" ^
   string_of_int (length candle_action296_legacy_batch_theorems));
print_endline "CANDLE_CV_ACTION296_LEGACY_BATCH_OK DEVELOPMENT_NON_RELEASE";;
