(* ========================================================================== *)
(* First genuinely selected leaf of the first hminus-containing source.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the earlier isolated hminus disjunct,   *)
(* this follows the actual adaptive certificate plan, which selects function  *)
(* 0 throughout Iarg 0.                                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_iarg0_plan_probe.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;

module Test_cv_compute_analytic_expr_hminus_iarg0_function0_first_leaf = struct

open Certificate;;
open Candle_cv_analytic_expr_hminus_iarg0_plan_probe;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_flyspeck_nonlinear_driver;;

let rec first_leaf path domain tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      if raw_flag then
        failwith "hminus Iarg0 function0: unexpected raw leaf";
      rev path,status,function_index,domain
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "hminus Iarg0 function0: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain 6 6 (split_index + 1) domain in
      first_leaf ((split_index + 1) :: path) left_domain left
  | P_result_mono _ ->
      failwith "hminus Iarg0 function0: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "hminus Iarg0 function0: unexpected reference node";;

let leaf_path,leaf_status,leaf_function_index,leaf_domain =
  first_leaf [] root_domain precision_tree;;

if leaf_function_index <> 0 then
  failwith "hminus Iarg0 function0: selected-function drift";;

let leaf_pair,_,_ =
  M_taylor.dest_m_cell_domain (concl leaf_domain);;
let leaf_lower,leaf_upper = dest_pair leaf_pair;;
let normalized_lower,_ = candle_reflected_nl_normalize_vector leaf_lower;;
let normalized_upper,_ = candle_reflected_nl_normalize_vector leaf_upper;;

let _ =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_FUNCTION0_FIRST_LEAF" ^
     " DEVELOPMENT_NON_RELEASE phase=prepare path_length=" ^
     string_of_int (length leaf_path) ^
     " precision=" ^ string_of_int leaf_status.pp);;

let prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    function0 normalized_lower normalized_upper;;
let instruction_count = length (dest_list prepared.program_term);;

let _ =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_FUNCTION0_FIRST_LEAF" ^
     " DEVELOPMENT_NON_RELEASE phase=prepared instructions=" ^
     string_of_int instruction_count);;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_NL_HMINUS_IARG0_FUNCTION0_FIRST_LEAF" ^
         " DEVELOPMENT_NON_RELEASE phase=" ^ event));;

let normalized_theorem =
  candle_q_dim_analytic_jet_prove_box_six
    prepared normalized_lower normalized_upper;;
let source_theorem =
  REWRITE_RULE [GSYM function0_normalization] normalized_theorem;;

let rec aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head && aconv_lists left_tail right_tail
  | _ -> false;;

let pass_theorem =
  candle_reflected_nl_source_pass_with source_function0
    (fun actual_lower actual_upper ->
      if not
          (aconv_lists actual_lower normalized_lower &&
           aconv_lists actual_upper normalized_upper) then
        failwith "hminus Iarg0 function0: handoff box drift";
      source_theorem)
    leaf_domain;;

if hyp normalized_theorem <> [] ||
   hyp source_theorem <> [] ||
   hyp pass_theorem <> [] then
  failwith "hminus Iarg0 function0: theorem has assumptions";;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_FUNCTION0_FIRST_LEAF_OK" ^
   " DEVELOPMENT_NON_RELEASE path_length=" ^
   string_of_int (length leaf_path) ^
   " precision=" ^ string_of_int leaf_status.pp ^
   " instructions=" ^ string_of_int instruction_count);;

end;;
