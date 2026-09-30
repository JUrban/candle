(* ========================================================================== *)
(* Reflected box-free topology stream for raw variable Taylor jobs.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This executable layer keeps jobs, token        *)
(* topology, and the active root stack as cval data.  Its initial use is a    *)
(* bounded performance discriminator; a result earns proof credit only after  *)
(* it is connected to the logical compact runner by a general soundness       *)
(* theorem.                                                                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_whole_box_dim_taylor;;

(* Join the encoded interval lists for two sibling boxes.  The parent lower
   endpoint comes from the left child and its upper endpoint from the right.
   A shape mismatch returns the empty-list encoding and is rejected by the
   dimension and exact-split guards in the runner. *)
let candle_cv_q_boxes_compact_join_def = define
 `(candle_cv_q_boxes_compact_join (Cexp_num n) right = Cexp_num 0) /\
  (candle_cv_q_boxes_compact_join
      (Cexp_pair left lefts) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_boxes_compact_join
      (Cexp_pair left lefts) (Cexp_pair right rights) =
     Cexp_pair (Cexp_pair (Cexp_fst left) (Cexp_snd right))
       (candle_cv_q_boxes_compact_join lefts rights))`;;

let candle_cv_q_boxes_compact_join_compute = prove
 (`!left right.
     candle_cv_q_boxes_compact_join left right =
     Cexp_if (Cexp_ispair left)
       (Cexp_if (Cexp_ispair right)
         (Cexp_pair
           (Cexp_pair (Cexp_fst (Cexp_fst left))
             (Cexp_snd (Cexp_fst right)))
           (candle_cv_q_boxes_compact_join
             (Cexp_snd left) (Cexp_snd right)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `left:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `right:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_boxes_compact_join_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

(* One nonrecursive transition returns
     (accepted,(next jobs,next top-first stack)).
   Numeric tokens are leaves (only zero is canonical); pair tokens are glue
   records (axis,zero). *)
let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def =
  new_definition
   `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition
        tree_dim token jobs stack =
      Cexp_if (Cexp_ispair token)
        (let axis = Cexp_fst token in
         let marker = Cexp_snd token in
         let right = Cexp_fst stack in
         let after_right = Cexp_snd stack in
         let left = Cexp_fst after_right in
         let remaining_stack = Cexp_snd after_right in
         let parent = candle_cv_q_boxes_compact_join left right in
         Cexp_pair
           (candle_cv_bool_and
             (Cexp_eq marker (Cexp_num 0))
             (candle_cv_bool_and
               (Cexp_ispair stack)
               (candle_cv_bool_and
                 (Cexp_ispair after_right)
                 (candle_cv_bool_and
                   (Cexp_eq (candle_cv_list_length parent) tree_dim)
                   (candle_cv_bool_and
                     (Cexp_less (Cexp_num 0) axis)
                     (candle_cv_bool_and
                       (Cexp_less axis (Cexp_add tree_dim (Cexp_num 1)))
                       (candle_cv_q_boxes_split_exact_from
                         (Cexp_num 1) axis parent left right)))))))
           (Cexp_pair jobs (Cexp_pair parent remaining_stack)))
        (let boxes = Cexp_snd (Cexp_snd (Cexp_fst jobs)) in
         Cexp_pair
           (candle_cv_bool_and
             (Cexp_eq token (Cexp_num 0))
             (candle_cv_bool_and
               (Cexp_ispair jobs)
               (Cexp_eq (candle_cv_list_length boxes) tree_dim)))
           (Cexp_pair (Cexp_snd jobs) (Cexp_pair boxes stack)))`;;

(* Token encoding:
     Cexp_num 0                  leaf
     Cexp_pair (Cexp_num axis) (Cexp_num 0)  glue at [axis]
   A stream and every stack are cval cons lists.  The result is
     (success,(unconsumed raw jobs,top-first encoded root-box stack)).
   Nonzero numeric token-list terminators, nonzero leaf tags, malformed glue
   tags, malformed jobs/stacks, bad dimensions, and inexact splits reject. *)
let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def = define
 `(candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim (Cexp_num n) jobs stack =
     Cexp_if (Cexp_eq (Cexp_num n) (Cexp_num 0))
       (Cexp_pair (Cexp_num 1) (Cexp_pair jobs stack))
       (Cexp_pair (Cexp_num 0) (Cexp_pair jobs stack))) /\
  (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim (Cexp_pair token tokens) jobs stack =
     let transition =
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition
         tree_dim token jobs stack in
     Cexp_if
       (Cexp_fst transition)
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens
           (Cexp_fst (Cexp_snd transition))
           (Cexp_snd (Cexp_snd transition)))
       (Cexp_pair (Cexp_num 0) (Cexp_pair jobs stack)))`;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_compute =
  prove
   (`!tree_dim tokens jobs stack.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens jobs stack =
       Cexp_if (Cexp_ispair tokens)
         (let transition =
            candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition
              tree_dim (Cexp_fst tokens) jobs stack in
          Cexp_if
            (Cexp_fst transition)
            (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
              tree_dim (Cexp_snd tokens)
                (Cexp_fst (Cexp_snd transition))
                (Cexp_snd (Cexp_snd transition)))
            (Cexp_pair (Cexp_num 0) (Cexp_pair jobs stack)))
         (Cexp_if (Cexp_eq tokens (Cexp_num 0))
           (Cexp_pair (Cexp_num 1) (Cexp_pair jobs stack))
           (Cexp_pair (Cexp_num 0) (Cexp_pair jobs stack)))`,
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `tokens:cval` (cases "cval")) THEN
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
       cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
       LET_DEF;LET_END_DEF]);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    [SPEC_ALL candle_cv_bool_and_def;
     SPEC_ALL candle_cv_list_length_compute;
     SPEC_ALL candle_cv_q_boxes_split_exact_from_compute;
     SPEC_ALL candle_cv_q_boxes_compact_join_compute;
     SPEC_ALL
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
     SPEC_ALL
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_compute];;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPACT_STREAM_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
