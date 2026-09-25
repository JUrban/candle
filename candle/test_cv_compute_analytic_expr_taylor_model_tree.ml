(* Focused proof/load regression for exact centered Taylor split trees. *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree.ml";;

open Candle_cv_analytic_expr_taylor_model_tree;;

let candle_taylor_model_tree_axioms_before = axioms ();;

let candle_taylor_model_tree_leaf_count = prove
 (`!center_e boxes.
     candle_q_dim_taylor_model_tree_leaf_count
       (Candle_q_dim_taylor_model_tree_leaf center_e boxes) = 1`,
  REWRITE_TAC[candle_q_dim_taylor_model_tree_leaf_count_def]);;

let candle_taylor_model_tree_axioms_after = axioms ();;

if length candle_taylor_model_tree_axioms_after <>
     length candle_taylor_model_tree_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_taylor_model_tree_axioms_before)
       candle_taylor_model_tree_axioms_after) then
  failwith "certified Taylor tree: changed the global axiom set";;

print_endline "CANDLE_CV_TAYLOR_MODEL_TREE_OK DEVELOPMENT_NON_RELEASE";;
