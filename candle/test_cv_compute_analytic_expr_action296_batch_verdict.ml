(* ========================================================================== *)
(* One-verdict proof of the first genuine action-296 nonlinear leaf.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The same two child cells as the established   *)
(* certified proof are checked by one reflected batch computation.  Ordinary *)
(* kernel theorems then perform only the source handoff and Flyspeck glue.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_batch_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_batch_prove;;

let candle_action296_batch_verdict_axioms_before = axioms ();;

let candle_action296_batch_verdict_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_batch_verdict_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 batch verdict: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 batch verdict: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_batch_verdict_find left_domain left
  | P_result_mono _ ->
      failwith "action296 batch verdict: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 batch verdict: unexpected reference node";;

let candle_action296_batch_verdict_parent_domain =
  candle_action296_batch_verdict_find
    candle_action296_batch_verdict_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_batch_verdict_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_batch_verdict_parent_lower,
    candle_action296_batch_verdict_parent_upper =
  candle_action296_batch_verdict_domain_bounds
    candle_action296_batch_verdict_parent_domain;;

let candle_action296_batch_verdict_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_batch_verdict_parent_lower
    candle_action296_batch_verdict_parent_upper;;

let candle_action296_batch_verdict_left_domain,
    candle_action296_batch_verdict_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_batch_verdict_parent_domain;;

let candle_action296_batch_verdict_cell domain_th =
  let lower,upper = candle_action296_batch_verdict_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_six
      candle_action296_batch_verdict_box_prepared lower upper in
  {
    batch_center_variant = center_variant;
    batch_lower = lower;
    batch_upper = upper;
  };;

let candle_action296_batch_verdict_left_cell =
  candle_action296_batch_verdict_cell
    candle_action296_batch_verdict_left_domain;;
let candle_action296_batch_verdict_right_cell =
  candle_action296_batch_verdict_cell
    candle_action296_batch_verdict_right_domain;;

let candle_action296_batch_verdict_profile_events : string list ref = ref [];;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      candle_action296_batch_verdict_profile_events :=
        event :: !candle_action296_batch_verdict_profile_events;
      print_endline
        ("CANDLE_CV_ACTION296_BATCH_VERDICT_STAGE event=" ^ event));;

print_endline "CANDLE_CV_ACTION296_BATCH_VERDICT event=batch-begin";;
let candle_action296_batch_verdict_result =
  candle_q_dim_taylor_model_batch_prove_six
    candle_action296_batch_verdict_box_prepared
    [candle_action296_batch_verdict_left_cell;
     candle_action296_batch_verdict_right_cell];;
print_endline "CANDLE_CV_ACTION296_BATCH_VERDICT event=batch-end";;

let rec candle_action296_batch_verdict_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head &&
      candle_action296_batch_verdict_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_action296_batch_verdict_cell_for lower upper =
  try
    find
      (fun cell ->
        length cell.batch_lower = length lower &&
        length cell.batch_upper = length upper &&
        candle_action296_batch_verdict_aconv_lists
          cell.batch_lower lower &&
        candle_action296_batch_verdict_aconv_lists
          cell.batch_upper upper)
      [candle_action296_batch_verdict_left_cell;
       candle_action296_batch_verdict_right_cell]
  with Not_found ->
    failwith "action296 batch verdict: unknown proved cell";;

let candle_action296_batch_verdict_prove_domain domain_th =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      candle_q_dim_taylor_model_batch_cell_source_six
        candle_action296_batch_verdict_result
        (candle_action296_batch_verdict_cell_for lower upper))
    domain_th;;

print_endline "CANDLE_CV_ACTION296_BATCH_VERDICT event=handoff-begin";;
let candle_action296_batch_verdict_left_theorem =
  candle_action296_batch_verdict_prove_domain
    candle_action296_batch_verdict_left_domain;;
let candle_action296_batch_verdict_right_theorem =
  candle_action296_batch_verdict_prove_domain
    candle_action296_batch_verdict_right_domain;;

let candle_action296_batch_verdict_theorem =
  M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
    (M_verifier.m_glue_cells_list
      candle_action296_plan_dimension 4
      candle_action296_batch_verdict_left_theorem
      candle_action296_batch_verdict_right_theorem);;
print_endline "CANDLE_CV_ACTION296_BATCH_VERDICT event=handoff-end";;

let candle_action296_batch_verdict_functions,
    candle_action296_batch_verdict_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_batch_verdict_theorem);;

let candle_action296_batch_verdict_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_batch_verdict_parent_domain);;

let candle_action296_batch_verdict_theorem_md5 =
  Digest.to_hex
    (Digest.string (string_of_thm candle_action296_batch_verdict_theorem));;

if candle_action296_batch_verdict_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_batch_verdict_proved_domain
       candle_action296_batch_verdict_expected_domain) ||
   hyp candle_action296_batch_verdict_theorem <> [] ||
   candle_action296_batch_verdict_theorem_md5 <>
     "926f44ab8d5f2303064fe5788cead588" then
  failwith "action296 batch verdict: final theorem mismatch";;

let candle_action296_batch_verdict_axioms_after = axioms ();;

if length candle_action296_batch_verdict_axioms_after <>
     length candle_action296_batch_verdict_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_batch_verdict_axioms_before)
       candle_action296_batch_verdict_axioms_after) then
  failwith "action296 batch verdict: changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_BATCH_VERDICT_RESULT cells=2 computes=1" ^
   " theorem_md5=" ^ candle_action296_batch_verdict_theorem_md5 ^
   " profile_events=" ^
   string_of_int (length !candle_action296_batch_verdict_profile_events));;
print_endline
  "CANDLE_CV_ACTION296_BATCH_VERDICT_OK DEVELOPMENT_NON_RELEASE";;
