(* ========================================================================== *)
(* Representation correctness for the compact exact split-tree checker.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_compact_correct = struct

open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_compute;;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF tree-correct begin";;
let candle_cv_q_dim_taylor_model_tree_topology_check_correct = prove
 (`!tree tree_dim.
     candle_cv_q_dim_taylor_model_tree_topology_check (Cexp_num tree_dim)
       (candle_cv_q_dim_taylor_model_tree_topology tree) =
     candle_cv_bool
       (candle_q_dim_taylor_model_tree_exact_well_formed tree_dim tree)`,
  MATCH_MP_TAC candle_q_dim_taylor_model_tree_INDUCT THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_tree_topology_def;
       candle_cv_q_dim_taylor_model_tree_topology_check_def;
       candle_q_dim_taylor_model_tree_exact_well_formed_def;
       candle_cv_interval_list_length_correct;
       candle_cv_num_equal_correct; candle_cv_bool_if_correct;
       candle_cv_bool_def; cexp_if_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC
      [candle_cv_q_dim_taylor_model_tree_topology_def;
       candle_cv_q_dim_taylor_model_tree_topology_check_def;
       candle_q_dim_taylor_model_tree_exact_well_formed_def;
       candle_q_dim_taylor_model_tree_root_boxes_def;
       candle_cv_q_dim_taylor_model_tree_topology_boxes;
       candle_cv_interval_list_length_correct;
       candle_cv_q_boxes_split_exact_from_correct;
       candle_cv_bool_and_correct; candle_cv_num_equal_correct;
       candle_cv_num_less_correct; cexp_add_def; cexp_fst_def] THEN
    REWRITE_TAC[ARITH_RULE `axis < tree_dim + 1 <=> axis <= tree_dim`;
                ARITH_RULE `0 < axis <=> 1 <= axis`; CONJ_ASSOC]]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF tree-correct end";;

(* Preserve the original module-qualified theorem name after moving this
   executable equation into the compute-only support layer. *)
let candle_cv_q_boxes_split_exact_from_compute =
  Candle_cv_analytic_expr_taylor_model_tree_compact_compute.
    candle_cv_q_boxes_split_exact_from_compute;;

let candle_cv_q_dim_taylor_model_tree_topology_check_pair_compute = prove
 (`!tree_dim boxes axis children.
     candle_cv_q_dim_taylor_model_tree_topology_check tree_dim
       (Cexp_pair boxes (Cexp_pair axis children)) =
     Cexp_if (Cexp_ispair children)
       (candle_cv_bool_and
         (Cexp_eq (candle_cv_list_length boxes) tree_dim)
         (candle_cv_bool_and
           (Cexp_less (Cexp_num 0) axis)
           (candle_cv_bool_and
             (Cexp_less axis (Cexp_add tree_dim (Cexp_num 1)))
             (candle_cv_bool_and
               (candle_cv_q_boxes_split_exact_from
                 (Cexp_num 1) axis boxes
                 (Cexp_fst (Cexp_fst children))
                 (Cexp_fst (Cexp_snd children)))
               (candle_cv_bool_and
                 (candle_cv_q_dim_taylor_model_tree_topology_check
                   tree_dim (Cexp_fst children))
                 (candle_cv_q_dim_taylor_model_tree_topology_check
                   tree_dim (Cexp_snd children)))))))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `children:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_check_def;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_tree_topology_check_payload_compute = prove
 (`!tree_dim boxes payload.
     candle_cv_q_dim_taylor_model_tree_topology_check tree_dim
       (Cexp_pair boxes payload) =
     Cexp_if (Cexp_ispair payload)
       (Cexp_if (Cexp_ispair (Cexp_snd payload))
         (candle_cv_bool_and
           (Cexp_eq (candle_cv_list_length boxes) tree_dim)
           (candle_cv_bool_and
             (Cexp_less (Cexp_num 0) (Cexp_fst payload))
             (candle_cv_bool_and
               (Cexp_less (Cexp_fst payload)
                 (Cexp_add tree_dim (Cexp_num 1)))
               (candle_cv_bool_and
                 (candle_cv_q_boxes_split_exact_from
                   (Cexp_num 1) (Cexp_fst payload) boxes
                   (Cexp_fst (Cexp_fst (Cexp_snd payload)))
                   (Cexp_fst (Cexp_snd (Cexp_snd payload))))
                 (candle_cv_bool_and
                   (candle_cv_q_dim_taylor_model_tree_topology_check
                     tree_dim (Cexp_fst (Cexp_snd payload)))
                   (candle_cv_q_dim_taylor_model_tree_topology_check
                     tree_dim (Cexp_snd (Cexp_snd payload))))))))
         (Cexp_num 0))
       (Cexp_if (Cexp_eq payload (Cexp_num 0))
         (Cexp_eq (candle_cv_list_length boxes) tree_dim)
         (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `payload:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_check_def;
     candle_cv_q_dim_taylor_model_tree_topology_check_pair_compute;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_tree_topology_check_compute = prove
 (`!tree_dim encoded.
     candle_cv_q_dim_taylor_model_tree_topology_check tree_dim encoded =
     Cexp_if (Cexp_ispair encoded)
       (Cexp_if (Cexp_ispair (Cexp_snd encoded))
         (Cexp_if (Cexp_ispair (Cexp_snd (Cexp_snd encoded)))
           (candle_cv_bool_and
             (Cexp_eq (candle_cv_list_length (Cexp_fst encoded)) tree_dim)
             (candle_cv_bool_and
               (Cexp_less (Cexp_num 0) (Cexp_fst (Cexp_snd encoded)))
               (candle_cv_bool_and
                 (Cexp_less (Cexp_fst (Cexp_snd encoded))
                   (Cexp_add tree_dim (Cexp_num 1)))
                 (candle_cv_bool_and
                   (candle_cv_q_boxes_split_exact_from
                     (Cexp_num 1) (Cexp_fst (Cexp_snd encoded))
                     (Cexp_fst encoded)
                     (Cexp_fst
                       (Cexp_fst (Cexp_snd (Cexp_snd encoded))))
                     (Cexp_fst
                       (Cexp_snd (Cexp_snd (Cexp_snd encoded)))))
                   (candle_cv_bool_and
                     (candle_cv_q_dim_taylor_model_tree_topology_check
                       tree_dim
                       (Cexp_fst (Cexp_snd (Cexp_snd encoded))))
                     (candle_cv_q_dim_taylor_model_tree_topology_check
                       tree_dim
                       (Cexp_snd (Cexp_snd (Cexp_snd encoded)))))))))
           (Cexp_num 0))
         (Cexp_if (Cexp_eq (Cexp_snd encoded) (Cexp_num 0))
           (Cexp_eq
             (candle_cv_list_length (Cexp_fst encoded)) tree_dim)
           (Cexp_num 0)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_check_def;
     candle_cv_q_dim_taylor_model_tree_topology_check_payload_compute;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_tree_compact_compute_eqs =
  union candle_cv_q_dim_taylor_model_certified_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_boxes_split_exact_from_compute;
       candle_cv_q_dim_taylor_model_tree_topology_check_compute]);;

end;;
