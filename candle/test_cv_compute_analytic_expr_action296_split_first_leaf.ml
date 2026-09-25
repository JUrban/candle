(* ========================================================================== *)
(* A complete reflected proof of the first genuine action-296 leaf.          *)
(*                                                                            *)
(* The original leaf is bisected along all six coordinates.  All 64 computed *)
(* leaves share one whole-box source program; only their untrusted point-     *)
(* certificate preparation differs.                                          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_split_certificate_prove.ml";;

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_split_certificate_prove;;

let candle_action296_split_leaf_axioms_before = axioms ();;

let candle_action296_split_leaf_variable_sqrt_intervals =
 [`((((47,0),19),((241,0),99)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((2,0),0),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`];;

let candle_action296_split_leaf_box_sqrt_interval tm =
  let rec choose variables intervals =
    match variables,intervals with
    | variable :: variable_tail,interval :: interval_tail ->
        if aconv tm variable then interval
        else choose variable_tail interval_tail
    | [],[] ->
        `((((38,0),0),((80,0),0)):
          ((num#num)#num)#((num#num)#num))`
    | _ -> failwith "action296 split leaf: sqrt interval shape" in
  choose candle_action296_plan_sqrt_variables
    candle_action296_split_leaf_variable_sqrt_intervals;;

let candle_action296_split_leaf_box_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_split_leaf_box_sqrt_interval
    candle_action296_plan_prepared.function_term;;

let candle_action296_split_leaf_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_split_leaf_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 split leaf: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 split leaf: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_split_leaf_find left_domain left
  | P_result_mono _ ->
      failwith "action296 split leaf: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 split leaf: unexpected reference node";;

let candle_action296_split_leaf_original_domain =
  candle_action296_split_leaf_find candle_action296_split_leaf_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_split_leaf_count = ref 0;;
let candle_action296_split_leaf_attempt_count = ref 0;;
let candle_action296_split_leaf_retry_count = ref 0;;

let candle_action296_split_leaf_prove domain_th =
  let attempt_number = !candle_action296_split_leaf_attempt_count + 1 in
  candle_action296_split_leaf_attempt_count := attempt_number;
  print_endline
    ("CANDLE_CV_ACTION296_SPLIT_FIRST_LEAF_STAGE attempt=" ^
     string_of_int attempt_number ^ " event=begin");
  let theorem =
    candle_reflected_nl_source_pass_with
      candle_action296_plan_prepared.function_term
      (fun lower upper ->
        let center_prepared =
          candle_q_dim_analytic_jet_prepare_point_six
            candle_action296_plan_prepared.function_term lower upper in
        candle_q_dim_analytic_split_certificate_prove_box_six
          center_prepared candle_action296_split_leaf_box_prepared
          lower upper)
      domain_th in
  candle_action296_split_leaf_count :=
    !candle_action296_split_leaf_count + 1;
  print_endline
    ("CANDLE_CV_ACTION296_SPLIT_FIRST_LEAF_STAGE attempt=" ^
     string_of_int attempt_number ^ " event=end");
  theorem;;

let candle_action296_split_leaf_rejection_prefix =
  "analytic split-certificate prover: box rejected";;

let candle_action296_split_leaf_is_rejection message =
  let prefix = candle_action296_split_leaf_rejection_prefix in
  String.length message >= String.length prefix &&
  String.sub message 0 (String.length prefix) = prefix;;

let rec candle_action296_split_leaf_adaptive depth domain_th =
  try candle_action296_split_leaf_prove domain_th with Failure message ->
    if depth >= 3 ||
       not (candle_action296_split_leaf_is_rejection message) then
      (print_endline
        ("CANDLE_CV_ACTION296_SPLIT_FIRST_LEAF_FAILURE attempt=" ^
         string_of_int !candle_action296_split_leaf_attempt_count ^
         " message=" ^ message);
       failwith message)
    else
      let retry_number = !candle_action296_split_leaf_retry_count + 1 in
      let axis = List.nth [4;5;6] depth in
      let _ = candle_action296_split_leaf_retry_count := retry_number in
      let _ = print_endline
        ("CANDLE_CV_ACTION296_SPLIT_FIRST_LEAF_RETRY retry=" ^
         string_of_int retry_number ^ " depth=" ^ string_of_int depth ^
         " axis=" ^ string_of_int axis) in
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 axis domain_th in
      let left_theorem =
        candle_action296_split_leaf_adaptive (depth + 1) left_domain in
      let right_theorem =
        candle_action296_split_leaf_adaptive (depth + 1) right_domain in
      M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
        (M_verifier.m_glue_cells_list
          candle_action296_plan_dimension axis left_theorem right_theorem);;

let rec candle_action296_split_leaf_subdivide axes domain_th =
  match axes with
  | [] -> candle_action296_split_leaf_adaptive 0 domain_th
  | axis :: remaining ->
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 axis domain_th in
      let left_theorem =
        candle_action296_split_leaf_subdivide remaining left_domain in
      let right_theorem =
        candle_action296_split_leaf_subdivide remaining right_domain in
      M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
        (M_verifier.m_glue_cells_list
          candle_action296_plan_dimension axis left_theorem right_theorem);;

let candle_action296_split_leaf_theorem =
  candle_action296_split_leaf_subdivide [1;2;3;4;5;6]
    candle_action296_split_leaf_original_domain;;

let candle_action296_split_leaf_functions,
    candle_action296_split_leaf_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_split_leaf_theorem);;
let candle_action296_split_leaf_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_split_leaf_original_domain);;

if !candle_action296_split_leaf_count < 64 ||
   !candle_action296_split_leaf_count > 512 ||
   candle_action296_split_leaf_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_split_leaf_proved_domain
       candle_action296_split_leaf_expected_domain) ||
   hyp candle_action296_split_leaf_theorem <> [] then
  failwith "action296 split leaf: final theorem mismatch";;

let candle_action296_split_leaf_axioms_after = axioms ();;
if length candle_action296_split_leaf_axioms_after <>
     length candle_action296_split_leaf_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_split_leaf_axioms_before)
       candle_action296_split_leaf_axioms_after) then
  failwith "action296 split leaf: changed global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_SPLIT_FIRST_LEAF_RESULT leaves=" ^
   string_of_int !candle_action296_split_leaf_count ^
   " attempts=" ^ string_of_int !candle_action296_split_leaf_attempt_count ^
   " retries=" ^ string_of_int !candle_action296_split_leaf_retry_count ^
   " theorem_md5=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_action296_split_leaf_theorem)));
print_endline "CANDLE_CV_ACTION296_SPLIT_FIRST_LEAF_OK";;
