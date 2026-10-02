(* ========================================================================== *)
(* Compute-only exact split checker shared by compact Taylor topologies.      *)
(*                                                                            *)
(* The logical tree types and their soundness proofs deliberately live in    *)
(* later modules.  This unit is sufficient for executing a compact token     *)
(* stream before those proof layers are loaded.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_cval_list.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_compact_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_cval_list;;

let candle_cv_q_boxes_split_exact_from_def = define
 `(candle_cv_q_boxes_split_exact_from current axis (Cexp_num n) left right =
     Cexp_if (Cexp_eq (Cexp_num n) (Cexp_num 0))
       (candle_cv_bool_and
         (Cexp_eq left (Cexp_num 0))
         (Cexp_eq right (Cexp_num 0)))
       (Cexp_num 0)) /\
  (candle_cv_q_boxes_split_exact_from current axis
      (Cexp_pair root_value remaining_values) left right =
     Cexp_if (Cexp_ispair left)
       (Cexp_if (Cexp_ispair right)
         (candle_cv_bool_and
           (Cexp_if (Cexp_eq current axis)
             (candle_cv_bool_and
               (Cexp_eq (Cexp_fst (Cexp_fst left)) (Cexp_fst root_value))
               (candle_cv_bool_and
                 (Cexp_eq (Cexp_snd (Cexp_fst right))
                   (Cexp_snd root_value))
                 (Cexp_eq (Cexp_snd (Cexp_fst left))
                   (Cexp_fst (Cexp_fst right)))))
             (candle_cv_bool_and
               (Cexp_eq (Cexp_fst left) root_value)
               (Cexp_eq (Cexp_fst right) root_value)))
           (candle_cv_q_boxes_split_exact_from
             (Cexp_add current (Cexp_num 1)) axis remaining_values
             (Cexp_snd left) (Cexp_snd right)))
         (Cexp_num 0))
       (Cexp_num 0))`;;

(* [define] exposes the two constructor clauses as one conjunction.  The
   compute evaluator requires a single equation, so package the same clauses
   behind a shape-dispatch theorem in this compute-only layer. *)
let candle_cv_q_boxes_split_exact_from_compute = prove
 (`!current axis roots left right.
     candle_cv_q_boxes_split_exact_from current axis roots left right =
     Cexp_if (Cexp_ispair roots)
       (Cexp_if (Cexp_ispair left)
         (Cexp_if (Cexp_ispair right)
           (candle_cv_bool_and
             (Cexp_if (Cexp_eq current axis)
               (candle_cv_bool_and
                 (Cexp_eq (Cexp_fst (Cexp_fst left))
                   (Cexp_fst (Cexp_fst roots)))
                 (candle_cv_bool_and
                   (Cexp_eq (Cexp_snd (Cexp_fst right))
                     (Cexp_snd (Cexp_fst roots)))
                   (Cexp_eq (Cexp_snd (Cexp_fst left))
                     (Cexp_fst (Cexp_fst right)))))
               (candle_cv_bool_and
                 (Cexp_eq (Cexp_fst left) (Cexp_fst roots))
                 (Cexp_eq (Cexp_fst right) (Cexp_fst roots))))
             (candle_cv_q_boxes_split_exact_from
               (Cexp_add current (Cexp_num 1)) axis
               (Cexp_snd roots) (Cexp_snd left) (Cexp_snd right)))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_if (Cexp_eq roots (Cexp_num 0))
         (candle_cv_bool_and
           (Cexp_eq left (Cexp_num 0))
           (Cexp_eq right (Cexp_num 0)))
         (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `roots:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `left:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `right:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_boxes_split_exact_from_def;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

print_endline
  "CANDLE_CV_TAYLOR_MODEL_TREE_COMPACT_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
