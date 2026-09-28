(* ========================================================================== *)
(* Compact checked topology for exact centered-Taylor split trees.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Tree topology and exact rational boxes are    *)
(* ordinary data.  The executable checker below accepts only a dimension-    *)
(* correct binary tree whose child boxes exactly partition each parent box.  *)
(* A later proof adapter can combine its one computed verdict with the       *)
(* existing general Taylor-tree soundness theorem.                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_compact = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_tree;;

(* This relation is deliberately stronger than equality of represented real
   endpoints: it requires exact equality of the rational certificate data.
   That makes a changed endpoint representation fail closed. *)
let candle_q_boxes_split_exact_from_def = define
 `(candle_q_boxes_split_exact_from current axis
      ([]:(((num#num)#num)#((num#num)#num))list) [] [] <=> T) /\
  (candle_q_boxes_split_exact_from current axis
      [] (CONS left lefts) rights <=> F) /\
  (candle_q_boxes_split_exact_from current axis
      [] [] (CONS right rights) <=> F) /\
  (candle_q_boxes_split_exact_from current axis
      (CONS root_box root_boxes) [] rights <=> F) /\
  (candle_q_boxes_split_exact_from current axis
      (CONS root_box root_boxes) (CONS left lefts) [] <=> F) /\
  (candle_q_boxes_split_exact_from current axis
      (CONS root_box root_boxes) (CONS left lefts) (CONS right rights) <=>
     (if current = axis then
        FST left = FST root_box /\
        SND right = SND root_box /\
        SND left = FST right
      else left = root_box /\ right = root_box) /\
     candle_q_boxes_split_exact_from (SUC current) axis
       root_boxes lefts rights)`;;

let candle_q_dim_taylor_model_tree_exact_well_formed_def = define
 `(candle_q_dim_taylor_model_tree_exact_well_formed tree_dim
      (Candle_q_dim_taylor_model_tree_leaf center_e boxes) <=>
     LENGTH boxes = tree_dim) /\
  (candle_q_dim_taylor_model_tree_exact_well_formed tree_dim
      (Candle_q_dim_taylor_model_tree_node axis boxes left right) <=>
     LENGTH boxes = tree_dim /\
     1 <= axis /\ axis <= tree_dim /\
     candle_q_boxes_split_exact_from 1 axis boxes
       (candle_q_dim_taylor_model_tree_root_boxes left)
       (candle_q_dim_taylor_model_tree_root_boxes right) /\
     candle_q_dim_taylor_model_tree_exact_well_formed tree_dim left /\
     candle_q_dim_taylor_model_tree_exact_well_formed tree_dim right)`;;

(* A topology-only encoding.  Leaves carry their exact box list and a zero
   tag.  Nodes carry their exact box list, split coordinate, and two encoded
   children.  Center expressions are checked by the numerical job checker and
   intentionally do not occur in the topology representation. *)
let candle_cv_q_dim_taylor_model_tree_topology_def = define
 `(candle_cv_q_dim_taylor_model_tree_topology
      (Candle_q_dim_taylor_model_tree_leaf center_e boxes) =
     Cexp_pair (candle_cv_q_interval_list boxes) (Cexp_num 0)) /\
  (candle_cv_q_dim_taylor_model_tree_topology
      (Candle_q_dim_taylor_model_tree_node axis boxes left right) =
     Cexp_pair (candle_cv_q_interval_list boxes)
       (Cexp_pair (Cexp_num axis)
         (Cexp_pair
           (candle_cv_q_dim_taylor_model_tree_topology left)
           (candle_cv_q_dim_taylor_model_tree_topology right))))`;;

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

(* Nested constructor patterns make both recursive calls structurally smaller
   than the input tree, while malformed cval shapes are rejected. *)
let candle_cv_q_dim_taylor_model_tree_topology_check_def = define
 `(candle_cv_q_dim_taylor_model_tree_topology_check tree_dim
      (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_tree_topology_check tree_dim
      (Cexp_pair boxes (Cexp_num tag)) =
     Cexp_if (Cexp_eq (Cexp_num tag) (Cexp_num 0))
       (Cexp_eq (candle_cv_list_length boxes) tree_dim)
       (Cexp_num 0)) /\
  (candle_cv_q_dim_taylor_model_tree_topology_check tree_dim
      (Cexp_pair boxes (Cexp_pair axis (Cexp_num malformed))) =
     Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_tree_topology_check tree_dim
      (Cexp_pair boxes (Cexp_pair axis (Cexp_pair left right))) =
     candle_cv_bool_and
       (Cexp_eq (candle_cv_list_length boxes) tree_dim)
       (candle_cv_bool_and
         (Cexp_less (Cexp_num 0) axis)
         (candle_cv_bool_and
           (Cexp_less axis (Cexp_add tree_dim (Cexp_num 1)))
           (candle_cv_bool_and
             (candle_cv_q_boxes_split_exact_from
               (Cexp_num 1) axis boxes
               (Cexp_fst left) (Cexp_fst right))
             (candle_cv_bool_and
               (candle_cv_q_dim_taylor_model_tree_topology_check
                 tree_dim left)
               (candle_cv_q_dim_taylor_model_tree_topology_check
                 tree_dim right))))))`;;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF interval-injective begin";;
let candle_cv_q_injective = prove
 (`!left right. candle_cv_q left = candle_cv_q right <=> left = right`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM `candle_cv_q_decode`) THEN
    REWRITE_TAC[candle_cv_q_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_q_interval_injective = prove
 (`!left right.
     candle_cv_q_interval left = candle_cv_q_interval right <=> left = right`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN
      (MP_TAC o AP_TERM `candle_cv_q_interval_decode`) THEN
    REWRITE_TAC[candle_cv_q_interval_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_num_equal_correct = prove
 (`!left right.
     Cexp_eq (Cexp_num left) (Cexp_num right) =
     candle_cv_bool (left = right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_eq_def;candle_cv_bool_def;injectivity "cval"]);;

let candle_cv_num_less_correct = prove
 (`!left right.
     Cexp_less (Cexp_num left) (Cexp_num right) =
     candle_cv_bool (left < right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_less_def;candle_cv_bool_def]);;

let candle_cv_q_equal_correct = prove
 (`!left right.
     Cexp_eq (candle_cv_q left) (candle_cv_q right) =
     candle_cv_bool (left = right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_eq_def;candle_cv_bool_def;candle_cv_q_injective]);;

let candle_cv_q_interval_equal_correct = prove
 (`!left right.
     Cexp_eq (candle_cv_q_interval left) (candle_cv_q_interval right) =
     candle_cv_bool (left = right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [cexp_eq_def;candle_cv_bool_def;candle_cv_q_interval_injective]);;

let candle_cv_bool_if_correct = prove
 (`!guard consequent alternative.
     Cexp_if (candle_cv_bool guard)
       (candle_cv_bool consequent) (candle_cv_bool alternative) =
     candle_cv_bool (if guard then consequent else alternative)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `guard:bool` THEN
  REWRITE_TAC[candle_cv_bool_def;cexp_if_def]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF interval-injective end";;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-correct begin";;
let candle_cv_q_boxes_split_exact_from_correct = prove
 (`!roots current axis lefts rights.
     candle_cv_q_boxes_split_exact_from (Cexp_num current) (Cexp_num axis)
       (candle_cv_q_interval_list roots)
       (candle_cv_q_interval_list lefts)
       (candle_cv_q_interval_list rights) =
     candle_cv_bool
       (candle_q_boxes_split_exact_from current axis roots lefts rights)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `lefts:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    STRUCT_CASES_TAC
      (ISPEC
        `rights:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    REWRITE_TAC
      [candle_q_boxes_split_exact_from_def;
       candle_cv_q_boxes_split_exact_from_def;
       candle_cv_q_interval_list_def; candle_cv_bool_def;
       candle_cv_bool_and_def; cexp_eq_def; cexp_if_def;
       distinctness "cval"; injectivity "cval"] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MAP_EVERY X_GEN_TAC
      [`root_box:(((num#num)#num)#((num#num)#num))`;
       `root_boxes:(((num#num)#num)#((num#num)#num))list`] THEN
    DISCH_THEN (LABEL_TAC "root_boxes_ih") THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `lefts:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    STRUCT_CASES_TAC
      (ISPEC
        `rights:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    ASM_REWRITE_TAC
      [candle_q_boxes_split_exact_from_def;
       candle_cv_q_boxes_split_exact_from_def;
       candle_cv_q_interval_list_def;
       candle_cv_bool_and_correct; candle_cv_bool_if_correct;
       candle_cv_num_equal_correct; candle_cv_q_equal_correct;
       candle_cv_q_interval_equal_correct;
       cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_add_def;
       cexp_if_def;
       distinctness "cval"; injectivity "cval";
       ARITH_RULE `current + 1 = SUC current`] THEN
    ASM_CASES_TAC `(current:num) = axis` THEN
    ASM_REWRITE_TAC
      [candle_cv_q_interval_equal_correct; candle_cv_q_interval_def;
       cexp_fst_def; cexp_snd_def; candle_cv_q_equal_correct;
       candle_cv_bool_and_correct; candle_cv_bool_if_correct;
       cexp_if_def; injectivity "cval"; FST; SND] THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_correct; candle_cv_bool_if_correct] THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_correct; candle_cv_bool_if_correct] THEN
    REWRITE_TAC[candle_cv_bool_def]]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-correct end";;

let candle_cv_q_dim_taylor_model_tree_topology_boxes = prove
 (`!tree.
     Cexp_fst (candle_cv_q_dim_taylor_model_tree_topology tree) =
     candle_cv_q_interval_list
       (candle_q_dim_taylor_model_tree_root_boxes tree)`,
  MATCH_MP_TAC candle_q_dim_taylor_model_tree_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_def;
     candle_q_dim_taylor_model_tree_root_boxes_def; cexp_fst_def]);;

let candle_cv_q_dim_taylor_model_tree_compact_compute_eqs =
  union candle_cv_q_dim_taylor_model_certified_compute_eqs
    [SPEC_ALL candle_cv_q_dim_taylor_model_tree_topology_def;
     SPEC_ALL candle_cv_q_boxes_split_exact_from_def;
     SPEC_ALL candle_cv_q_dim_taylor_model_tree_topology_check_def];;

end;;
