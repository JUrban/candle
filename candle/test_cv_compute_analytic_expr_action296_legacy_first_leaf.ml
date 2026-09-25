(* ========================================================================== *)
(* Legacy theorem-producing proof of the first genuine action-296 leaf.       *)
(*                                                                            *)
(* This consumes the exact status and logical domain from the authenticated   *)
(* live-verifier plan.  It is the recurring-cost baseline for the reflected   *)
(* split proof of the same original leaf.  Wall time is measured externally  *)
(* because the CakeML runtime does not expose a useful clock in this state.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;

open Certificate;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;

let candle_action296_legacy_first_leaf_axioms_before = axioms ();;

let candle_action296_legacy_first_leaf_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_legacy_first_leaf_find domain_th tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      status,function_index,raw_flag,domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 legacy first leaf: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_legacy_first_leaf_find left_domain left
  | P_result_mono _ ->
      failwith "action296 legacy first leaf: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 legacy first leaf: unexpected reference node";;

let candle_action296_legacy_first_leaf_status,
    candle_action296_legacy_first_leaf_function_index,
    candle_action296_legacy_first_leaf_raw_flag,
    candle_action296_legacy_first_leaf_domain =
  candle_action296_legacy_first_leaf_find
    candle_action296_legacy_first_leaf_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_legacy_first_leaf_function_index <> 0 ||
   candle_action296_legacy_first_leaf_raw_flag then
  failwith "action296 legacy first leaf: selected pass drift";;

let candle_action296_legacy_first_leaf_certificate =
  P_result_pass
    (candle_action296_legacy_first_leaf_status,
     candle_action296_legacy_first_leaf_function_index,
     candle_action296_legacy_first_leaf_raw_flag);;

print_endline "CANDLE_CV_ACTION296_LEGACY_FIRST_LEAF_STAGE event=begin";;
let candle_action296_legacy_first_leaf_theorem =
  M_verifier.m_p_verify_disj_raw
    (0,0) candle_action296_plan_dimension 6
    candle_action296_plan_formal_functions
    candle_action296_legacy_first_leaf_certificate
    candle_action296_legacy_first_leaf_domain [];;
print_endline "CANDLE_CV_ACTION296_LEGACY_FIRST_LEAF_STAGE event=end";;

let candle_action296_legacy_first_leaf_functions,
    candle_action296_legacy_first_leaf_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_legacy_first_leaf_theorem);;
let candle_action296_legacy_first_leaf_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_legacy_first_leaf_domain);;

if candle_action296_legacy_first_leaf_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_legacy_first_leaf_proved_domain
       candle_action296_legacy_first_leaf_expected_domain) ||
   hyp candle_action296_legacy_first_leaf_theorem <> [] then
  failwith "action296 legacy first leaf: final theorem mismatch";;

let candle_action296_legacy_first_leaf_axioms_after = axioms ();;
if length candle_action296_legacy_first_leaf_axioms_after <>
     length candle_action296_legacy_first_leaf_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_legacy_first_leaf_axioms_before)
       candle_action296_legacy_first_leaf_axioms_after) then
  failwith "action296 legacy first leaf: changed global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_LEGACY_FIRST_LEAF_RESULT theorem_md5=" ^
   Digest.to_hex
     (Digest.string
       (string_of_thm candle_action296_legacy_first_leaf_theorem)));
print_endline "CANDLE_CV_ACTION296_LEGACY_FIRST_LEAF_OK";;
