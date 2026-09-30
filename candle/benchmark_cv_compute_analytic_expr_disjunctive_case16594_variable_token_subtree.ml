(* ========================================================================== *)
(* Genuine two-cell case-16594 subtree through raw jobs and compact tokens.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Original authenticated leaf 388 is one of the *)
(* 15 leaves that needs one additional axis-1 split.  This benchmark checks  *)
(* both children numerically, authenticates their topology from a leaf/glue  *)
(* token stream, and returns one theorem for the original parent box.         *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree = struct

open Certificate;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let rec candle_disjunctive_case16594_variable_token_nth index items =
  match index,items with
  | 0,head :: _ -> head
  | n,_ :: tail when n > 0 ->
      candle_disjunctive_case16594_variable_token_nth (n - 1) tail
  | _ -> failwith "case16594 variable token subtree: short leaf list";;

let candle_disjunctive_case16594_variable_token_rejected thunk =
  try
    let _ = thunk () in false
  with Failure _ -> true;;

let candle_disjunctive_case16594_variable_token_axioms_before = axioms ();;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-variable-token-subtree" ^
       " phase=" ^ event));;

let candle_disjunctive_case16594_variable_token_parent =
  candle_disjunctive_case16594_variable_token_nth 388
    candle_disjunctive_case16594_engine_state.family_engine_leaves;;

let candle_disjunctive_case16594_variable_token_parent_domain =
  match candle_disjunctive_case16594_variable_token_parent with
  | function_index,domain ->
      if function_index <> 1 then
        failwith "case16594 variable token subtree: parent selection drift";
      domain
  ;;

let candle_disjunctive_case16594_variable_token_left_domain,
    candle_disjunctive_case16594_variable_token_right_domain =
  M_verifier.split_domain 6 6 1
    candle_disjunctive_case16594_variable_token_parent_domain;;

let candle_disjunctive_case16594_variable_token_cells =
  [candle_disjunctive_case16594_variable_raw_cell
     candle_disjunctive_case16594_variable_token_left_domain;
   candle_disjunctive_case16594_variable_raw_cell
     candle_disjunctive_case16594_variable_token_right_domain];;

let candle_disjunctive_case16594_variable_token_raw =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
    candle_disjunctive_case16594_engine_state.family_engine_prepared
    candle_disjunctive_case16594_variable_token_cells;;

let candle_disjunctive_case16594_variable_token_root_boxes =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds
      candle_disjunctive_case16594_variable_token_parent_domain in
  candle_poly_fixture_q_boxes lower upper;;

let candle_disjunctive_case16594_variable_token_left_boxes =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds
      candle_disjunctive_case16594_variable_token_left_domain in
  candle_poly_fixture_q_boxes lower upper;;

let candle_disjunctive_case16594_variable_token_leaf =
  `Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf`;;

let candle_disjunctive_case16594_variable_token_glue axis boxes =
  list_mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_token_glue`,
     [mk_small_numeral axis;boxes]);;

let candle_disjunctive_case16594_variable_token_list tokens =
  mk_list
    (tokens,
     type_of candle_disjunctive_case16594_variable_token_leaf);;

let candle_disjunctive_case16594_variable_token_stream =
  candle_disjunctive_case16594_variable_token_list
    [candle_disjunctive_case16594_variable_token_leaf;
     candle_disjunctive_case16594_variable_token_leaf;
     candle_disjunctive_case16594_variable_token_glue 1
       candle_disjunctive_case16594_variable_token_root_boxes];;

let candle_disjunctive_case16594_variable_token_result =
  candle_q_dim_taylor_model_fixed_outer_variable_token_source_six
    candle_disjunctive_case16594_variable_token_raw
    candle_disjunctive_case16594_variable_token_stream;;

let candle_disjunctive_case16594_variable_token_missing_rejected =
  candle_disjunctive_case16594_variable_token_rejected
    (fun () ->
      candle_q_dim_taylor_model_fixed_outer_variable_token_source_six
        candle_disjunctive_case16594_variable_token_raw
        (candle_disjunctive_case16594_variable_token_list
          [candle_disjunctive_case16594_variable_token_leaf]));;

let candle_disjunctive_case16594_variable_token_axis_rejected =
  candle_disjunctive_case16594_variable_token_rejected
    (fun () ->
      candle_q_dim_taylor_model_fixed_outer_variable_token_source_six
        candle_disjunctive_case16594_variable_token_raw
        (candle_disjunctive_case16594_variable_token_list
          [candle_disjunctive_case16594_variable_token_leaf;
           candle_disjunctive_case16594_variable_token_leaf;
           candle_disjunctive_case16594_variable_token_glue 7
             candle_disjunctive_case16594_variable_token_root_boxes]));;

let candle_disjunctive_case16594_variable_token_box_rejected =
  candle_disjunctive_case16594_variable_token_rejected
    (fun () ->
      candle_q_dim_taylor_model_fixed_outer_variable_token_source_six
        candle_disjunctive_case16594_variable_token_raw
        (candle_disjunctive_case16594_variable_token_list
          [candle_disjunctive_case16594_variable_token_leaf;
           candle_disjunctive_case16594_variable_token_leaf;
           candle_disjunctive_case16594_variable_token_glue 1
             candle_disjunctive_case16594_variable_token_left_boxes]));;

let candle_disjunctive_case16594_variable_token_axioms_after = axioms ();;
let candle_disjunctive_case16594_variable_token_theorem =
  candle_disjunctive_case16594_variable_token_result.
    variable_token_source_theorem;;
let candle_disjunctive_case16594_variable_token_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm
        candle_disjunctive_case16594_variable_token_theorem));;

if hyp candle_disjunctive_case16594_variable_token_theorem <> [] ||
   not candle_disjunctive_case16594_variable_token_missing_rejected ||
   not candle_disjunctive_case16594_variable_token_axis_rejected ||
   not candle_disjunctive_case16594_variable_token_box_rejected ||
   length candle_disjunctive_case16594_variable_token_axioms_after <>
     length candle_disjunctive_case16594_variable_token_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_disjunctive_case16594_variable_token_axioms_before)
       candle_disjunctive_case16594_variable_token_axioms_after) then
  failwith "case16594 variable token subtree: final validation failed";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TOKEN_SUBTREE_RESULT" ^
   " original_leaf=388 numerical_cells=2 leaf_tokens=2 glue_tokens=1" ^
   " combined_root_theorem=1 malformed_rejections=3 theorem_digest=" ^
   candle_disjunctive_case16594_variable_token_digest);;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TOKEN_SUBTREE_OK DEVELOPMENT_NON_RELEASE";;

end;;
