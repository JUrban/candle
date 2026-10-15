(* ========================================================================== *)
(* First selected hminus-family leaf through normalized split aggregation.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Center and box use the same prepared source;   *)
(* the split prover is selected here for its proved normalized-extended       *)
(* Taylor aggregation, not to change the represented function.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hminus_iarg0_selected_leaf_fixture.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_split_certificate_prove.ml";;

module Test_cv_compute_analytic_expr_hminus_iarg0_function0_first_leaf_split = struct

open Candle_cv_analytic_expr_hminus_iarg0_selected_leaf_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_split_certificate_prove;;
open Candle_cv_flyspeck_nonlinear_driver;;

let marker phase =
  print_endline
    ("CANDLE_NL_HMINUS_IARG0_FUNCTION0_FIRST_LEAF_SPLIT" ^
     " DEVELOPMENT_NON_RELEASE phase=" ^ phase);;

let _ = marker "prepare";;
let prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    function0 normalized_lower normalized_upper;;
let instruction_count = length (dest_list prepared.program_term);;

let rec aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      aconv left_head right_head && aconv_lists left_tail right_tail
  | _ -> false;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    marker;;

let _ = marker "prove";;
let normalized_split_theorem =
  candle_q_dim_analytic_split_certificate_prove_box_six
    prepared prepared normalized_lower normalized_upper;;
let source_split_theorem =
  REWRITE_RULE [GSYM function0_normalization] normalized_split_theorem;;

let split_pass_theorem =
  candle_reflected_nl_source_pass_with source_function0
    (fun actual_lower actual_upper ->
      if not
          (aconv_lists actual_lower normalized_lower &&
           aconv_lists actual_upper normalized_upper) then
        failwith "hminus Iarg0 function0 split: handoff box drift";
      source_split_theorem)
    leaf_domain;;

if hyp normalized_split_theorem <> [] ||
   hyp source_split_theorem <> [] ||
   hyp split_pass_theorem <> [] then
  failwith "hminus Iarg0 function0 split: theorem has assumptions";;

print_endline
  ("CANDLE_NL_HMINUS_IARG0_FUNCTION0_FIRST_LEAF_SPLIT_OK" ^
   " DEVELOPMENT_NON_RELEASE path_length=" ^
   string_of_int (length selected_path) ^
   " precision=3" ^
   " instructions=" ^ string_of_int instruction_count);;

end;;
