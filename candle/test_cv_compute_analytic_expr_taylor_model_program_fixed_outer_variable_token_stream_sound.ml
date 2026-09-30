(* Focused laws for the compact token stream over authenticated jobs. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound.ml";;

module Test_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound;;

let candle_variable_token_stream_single_leaf = prove
 (`!job.
     candle_q_dim_taylor_model_fixed_outer_variable_token_run
       [Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf]
       [job] [] =
     (T,
      ([],
       [Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
          (FST job) (FST (SND job)) (SND (SND job))]))`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def]);;

let candle_variable_token_stream_two_leaf_glue = prove
 (`!left right axis root_boxes.
     candle_q_dim_taylor_model_fixed_outer_variable_token_run
       [Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf;
        Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf;
        Candle_q_dim_taylor_model_fixed_outer_variable_token_glue
          axis root_boxes]
       [left;right] [] =
     (T,
      ([],
       [Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
          axis root_boxes
          (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
            (FST left) (FST (SND left)) (SND (SND left)))
          (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
            (FST right) (FST (SND right)) (SND (SND right)))]))`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def]);;

let candle_variable_token_stream_missing_job = prove
 (`candle_q_dim_taylor_model_fixed_outer_variable_token_run
      [Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf]
      [] [] = (F,([],[]))`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def]);;

let candle_variable_token_stream_glue_underflow = prove
 (`!axis boxes jobs tokens.
     candle_q_dim_taylor_model_fixed_outer_variable_token_run
       (Candle_q_dim_taylor_model_fixed_outer_variable_token_glue
          axis boxes :: tokens)
       jobs [] = (F,(jobs,[]))`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def]);;

let candle_variable_token_stream_unused_job = prove
 (`!first extra.
     candle_q_dim_taylor_model_fixed_outer_variable_token_run
       [Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf]
       [first;extra] [] =
     (T,
      ([extra],
       [Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
          (FST first) (FST (SND first)) (SND (SND first))]))`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_TOKEN_STREAM_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
