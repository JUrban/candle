(* ========================================================================== *)
(* First genuine reflected leaf of the authenticated action-296 certificate. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_fixture;;
open Candle_cv_analytic_expr_action296_plan;;

let candle_action296_first_leaf_axioms_before = axioms ();;

let candle_action296_first_leaf_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_find_first_leaf path domain_th tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      rev path,status,function_index,raw_flag,domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 first leaf: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_find_first_leaf
        (split_index :: path) left_domain left
  | P_result_mono _ ->
      failwith "action296 first leaf: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 first leaf: unexpected reference node";;

let candle_action296_first_leaf_path,
    candle_action296_first_leaf_status,
    candle_action296_first_leaf_function_index,
    candle_action296_first_leaf_raw,
    candle_action296_first_leaf_domain =
  candle_action296_find_first_leaf []
    candle_action296_first_leaf_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_first_leaf_raw ||
   candle_action296_first_leaf_function_index <> 0 then
  failwith "action296 first leaf: unexpected pass selection";;

let candle_action296_first_leaf_profile_events : string list ref = ref [];;
let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      candle_action296_first_leaf_profile_events :=
        event :: !candle_action296_first_leaf_profile_events;
      print_endline
        ("CANDLE_CV_ACTION296_ANALYTIC_FIRST_LEAF_STAGE event=" ^ event));;

let candle_action296_first_leaf_theorem =
  try
    candle_reflected_nl_source_pass_with
      candle_action296_analytic_function
      (candle_q_dim_analytic_jet_prove_box_six
        candle_action296_plan_prepared)
      candle_action296_first_leaf_domain
  with Failure message ->
    print_endline
      ("CANDLE_CV_ACTION296_ANALYTIC_FIRST_LEAF_FAILURE message=" ^
       message);
    failwith message;;

let candle_action296_first_leaf_functions,
    candle_action296_first_leaf_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_first_leaf_theorem);;
let candle_action296_first_leaf_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_first_leaf_domain);;

if candle_action296_first_leaf_functions <>
     [candle_action296_analytic_function] ||
   not
     (aconv candle_action296_first_leaf_proved_domain
       candle_action296_first_leaf_expected_domain) ||
   hyp candle_action296_first_leaf_domain <> [] ||
   hyp candle_action296_first_leaf_theorem <> [] then
  failwith "action296 first leaf: theorem interface mismatch";;

let candle_action296_first_leaf_axioms_after = axioms ();;
if length candle_action296_first_leaf_axioms_after <>
     length candle_action296_first_leaf_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_action296_first_leaf_axioms_before)
       candle_action296_first_leaf_axioms_after) then
  failwith "action296 first leaf changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_ANALYTIC_FIRST_LEAF_RESULT path_depth=" ^
   string_of_int (length candle_action296_first_leaf_path) ^
   " precision=" ^
   string_of_int candle_action296_first_leaf_status.pp ^
   " profile_events=" ^
   string_of_int (length !candle_action296_first_leaf_profile_events) ^
   " theorem_md5=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_action296_first_leaf_theorem)));
print_endline "CANDLE_CV_ACTION296_ANALYTIC_FIRST_LEAF_OK";;
