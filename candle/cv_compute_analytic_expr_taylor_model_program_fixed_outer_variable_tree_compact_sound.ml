(* ========================================================================== *)
(* Computed exact-topology bridge for per-job fixed-outer certificate trees. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_correct.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_compact_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;

(* The existing compact checker deliberately ignores the leaf expression.   *)
(* Projecting a variable-certificate tree onto that established topology     *)
(* therefore needs only an arbitrary authenticated source at each leaf.      *)
let candle_q_dim_taylor_model_fixed_outer_variable_tree_project_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_tree_project source_e
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
        box_intervals center_intervals boxes) =
     Candle_q_dim_taylor_model_tree_leaf source_e boxes) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_tree_project source_e
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
        axis boxes left right) =
     Candle_q_dim_taylor_model_tree_node axis boxes
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_project
         source_e left)
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_project
         source_e right))`;;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_project_root = prove
 (`!tree source_e.
     candle_q_dim_taylor_model_tree_root_boxes
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_project
         source_e tree) =
     candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes tree`,
  MATCH_MP_TAC candle_q_dim_taylor_model_fixed_outer_variable_tree_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_tree_project_def;
     candle_q_dim_taylor_model_tree_root_boxes_def;
     candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes_def]);;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_project_exact = prove
 (`!tree source_e tree_dim.
     candle_q_dim_taylor_model_tree_exact_well_formed tree_dim
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_project
         source_e tree) <=>
     candle_q_dim_taylor_model_fixed_outer_variable_tree_exact
       tree_dim tree`,
  MATCH_MP_TAC candle_q_dim_taylor_model_fixed_outer_variable_tree_INDUCT THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_tree_project_def;
       candle_q_dim_taylor_model_tree_exact_well_formed_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_exact_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_tree_project_def;
       candle_q_dim_taylor_model_tree_exact_well_formed_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_exact_def;
       candle_q_dim_taylor_model_tree_root_boxes_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_project_root;
       CONJ_ASSOC]]);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_tree_topology_sound =
  prove
 (`!tree source_e tree_dim.
     candle_cv_q_dim_taylor_model_tree_topology_check
       (Cexp_num tree_dim)
       (candle_cv_q_dim_taylor_model_tree_topology
         (candle_q_dim_taylor_model_fixed_outer_variable_tree_project
           source_e tree)) = Cexp_num 1
     ==> candle_q_dim_taylor_model_fixed_outer_variable_tree_exact
           tree_dim tree`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_check_correct;
     candle_q_dim_taylor_model_fixed_outer_variable_tree_project_exact;
     candle_cv_bool_def] THEN
  ASM_CASES_TAC
    `candle_q_dim_taylor_model_fixed_outer_variable_tree_exact
       tree_dim tree` THEN
  ASM_REWRITE_TAC[injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_tree_compact_sound =
  prove
 (`!source_e (type_witness:real^N) tree.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs tree) /\
     candle_cv_q_dim_taylor_model_tree_topology_check
       (Cexp_num (dimindex (:N)))
       (candle_cv_q_dim_taylor_model_tree_topology
         (candle_q_dim_taylor_model_fixed_outer_variable_tree_project
           source_e tree)) = Cexp_num 1
     ==> m_cell_pass
          (candle_analytic_denote_dim source_e)
          ((candle_q_box_lower_vector
             (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
               tree):real^N),
           (candle_q_box_upper_vector
             (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
               tree):real^N))`,
  MESON_TAC
    [candle_cv_q_dim_taylor_model_fixed_outer_variable_tree_topology_sound;
     candle_q_dim_taylor_model_fixed_outer_variable_tree_sound]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_TREE_COMPACT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
