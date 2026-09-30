(* Focused executable laws for the postorder variable-certificate stream. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound.ml";;

module Test_cv_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound;;

let candle_variable_stream_single_leaf = prove
 (`!box_intervals center_intervals boxes.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       [Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          box_intervals center_intervals boxes] [] =
     (T,
      [Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
         box_intervals center_intervals boxes])`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def]);;

let candle_variable_stream_two_leaf_glue = prove
 (`!left_box left_center left_boxes
     right_box right_center right_boxes axis root_boxes.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       [Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          left_box left_center left_boxes;
        Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          right_box right_center right_boxes;
        Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis root_boxes] [] =
     (T,
      [Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
         axis root_boxes
         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
           left_box left_center left_boxes)
         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
           right_box right_center right_boxes)])`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def]);;

let candle_variable_stream_two_leaf_jobs_order = prove
 (`!left_box left_center left_boxes
     right_box right_center right_boxes axis root_boxes.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs
       [Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          left_box left_center left_boxes;
        Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          right_box right_center right_boxes;
        Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis root_boxes] =
     [(left_box,(left_center,left_boxes));
      (right_box,(right_center,right_boxes))]`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs_def]);;

let candle_variable_stream_empty_underflow = prove
 (`!axis boxes commands.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       (Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis boxes :: commands) [] = (F,[])`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def]);;

let candle_variable_stream_singleton_underflow = prove
 (`!axis boxes commands only.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       (Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis boxes :: commands) [only] = (F,[only])`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def]);;

let candle_variable_stream_unclosed_forest = prove
 (`!left_box left_center left_boxes
     right_box right_center right_boxes.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       [Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          left_box left_center left_boxes;
        Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          right_box right_center right_boxes] [] =
     (T,
      [Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
         right_box right_center right_boxes;
       Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
         left_box left_center left_boxes])`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_STREAM_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
