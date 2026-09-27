(* ========================================================================== *)
(* One tagged algebraic verdict closes the genuine action-296 parent tree.    *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_action296_tree_verdict.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_tree_prove.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_tree_prove;;

let candle_action296_fixed_algebraic_tree_axioms_before = axioms ();;

let candle_action296_fixed_algebraic_tree_cell cell =
  {
    fixed_algebraic_batch_center_variant = cell.batch_center_variant;
    fixed_algebraic_batch_lower = cell.batch_lower;
    fixed_algebraic_batch_upper = cell.batch_upper;
  };;

let candle_action296_fixed_algebraic_tree_left_cell =
  candle_action296_fixed_algebraic_tree_cell
    candle_action296_tree_verdict_left_cell;;
let candle_action296_fixed_algebraic_tree_right_cell =
  candle_action296_fixed_algebraic_tree_cell
    candle_action296_tree_verdict_right_cell;;

print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_TREE_VERDICT event=batch-begin";;
let candle_action296_fixed_algebraic_tree_result =
  candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
    candle_action296_tree_verdict_box_prepared
    [candle_action296_fixed_algebraic_tree_left_cell;
     candle_action296_fixed_algebraic_tree_right_cell];;
print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_TREE_VERDICT event=batch-end";;

let candle_action296_fixed_algebraic_tree_source =
  candle_q_dim_taylor_model_fixed_algebraic_tree_source_six
    candle_action296_fixed_algebraic_tree_result
    candle_action296_tree_verdict_tree
    candle_action296_tree_verdict_well_formed;;

let candle_action296_fixed_algebraic_tree_theorem =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_tree_verdict_aconv_lists lower
             candle_action296_tree_verdict_parent_lower &&
           candle_action296_tree_verdict_aconv_lists upper
             candle_action296_tree_verdict_parent_upper) then
        failwith
          "action296 fixed algebraic tree verdict: non-root handoff request";
      candle_action296_fixed_algebraic_tree_source)
    candle_action296_tree_verdict_parent_domain;;

let candle_action296_fixed_algebraic_tree_functions,
    candle_action296_fixed_algebraic_tree_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_fixed_algebraic_tree_theorem);;

let candle_action296_fixed_algebraic_tree_theorem_md5 =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_action296_fixed_algebraic_tree_theorem));;

if candle_action296_fixed_algebraic_tree_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_fixed_algebraic_tree_proved_domain
       candle_action296_tree_verdict_expected_domain) ||
   hyp candle_action296_fixed_algebraic_tree_theorem <> [] ||
   candle_action296_fixed_algebraic_tree_theorem_md5 <>
     "926f44ab8d5f2303064fe5788cead588" then
  failwith "action296 fixed algebraic tree verdict: final theorem mismatch";;

let candle_action296_fixed_algebraic_tree_axioms_after = axioms ();;

if length candle_action296_fixed_algebraic_tree_axioms_after <>
     length candle_action296_fixed_algebraic_tree_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_algebraic_tree_axioms_before)
       candle_action296_fixed_algebraic_tree_axioms_after) then
  failwith
    "action296 fixed algebraic tree verdict: changed the global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_TREE_VERDICT_RESULT" ^
   " cells=2 computes=1 root_handoffs=1 theorem_md5=" ^
   candle_action296_fixed_algebraic_tree_theorem_md5);;
print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_TREE_VERDICT_OK DEVELOPMENT_NON_RELEASE";;
