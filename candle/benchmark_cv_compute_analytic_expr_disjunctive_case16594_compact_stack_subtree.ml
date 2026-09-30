(* ========================================================================== *)
(* Genuine case-16594 two-cell subtree through the box-free topology stack.  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stack_subtree = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree;;

let candle_disjunctive_case16594_compact_subtree_leaf =
  `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`;;

let candle_disjunctive_case16594_compact_subtree_glue axis =
  mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
     mk_small_numeral axis);;

let candle_disjunctive_case16594_compact_subtree_tokens values =
  mk_list
    (values,type_of candle_disjunctive_case16594_compact_subtree_leaf);;

let candle_disjunctive_case16594_compact_subtree_rejected thunk =
  try let _ = thunk () in false with Failure _ -> true;;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-compact-stack-subtree" ^
         " phase=" ^ event));
  let stream =
    candle_disjunctive_case16594_compact_subtree_tokens
      [candle_disjunctive_case16594_compact_subtree_leaf;
       candle_disjunctive_case16594_compact_subtree_leaf;
       candle_disjunctive_case16594_compact_subtree_glue 1] in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_source_six
      candle_disjunctive_case16594_variable_token_raw stream in
  let theorem = result.variable_compact_source_theorem in
  let expected = candle_disjunctive_case16594_variable_token_theorem in
  let missing_rejected =
    candle_disjunctive_case16594_compact_subtree_rejected
      (fun () ->
        candle_q_dim_taylor_model_fixed_outer_variable_compact_source_six
          candle_disjunctive_case16594_variable_token_raw
          (candle_disjunctive_case16594_compact_subtree_tokens
            [candle_disjunctive_case16594_compact_subtree_leaf])) in
  let axis_rejected =
    candle_disjunctive_case16594_compact_subtree_rejected
      (fun () ->
        candle_q_dim_taylor_model_fixed_outer_variable_compact_source_six
          candle_disjunctive_case16594_variable_token_raw
          (candle_disjunctive_case16594_compact_subtree_tokens
            [candle_disjunctive_case16594_compact_subtree_leaf;
             candle_disjunctive_case16594_compact_subtree_leaf;
             candle_disjunctive_case16594_compact_subtree_glue 2])) in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  let axioms_after = axioms () in
  if hyp theorem <> [] ||
     not (aconv (concl theorem) (concl expected)) ||
     not
       (aconv result.variable_compact_root_boxes_term
         candle_disjunctive_case16594_variable_token_root_boxes) ||
     not missing_rejected || not axis_rejected ||
     digest <> "d88ef874dd7e0fdf114cb999e0bfcd55" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 compact stack subtree: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_SUBTREE_RESULT" ^
     " original_leaf=388 numerical_cells=2 leaf_tokens=2 glue_tokens=1" ^
     " combined_root_theorem=1 malformed_rejections=2 assumptions=0" ^
     " theorem_digest=" ^ digest);
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_SUBTREE_OK DEVELOPMENT_NON_RELEASE";;

end;;
