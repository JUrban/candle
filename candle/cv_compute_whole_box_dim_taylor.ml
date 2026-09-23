(* ========================================================================== *)
(* Dimension-parametric reflected whole-box Taylor arithmetic.               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the executable baseline for a value    *)
(* program, a gradient program list, and a Hessian program matrix.  All       *)
(* numerical interval evaluation and Taylor summation occur behind one        *)
(* Kernel.compute call.  A later shared-jet implementation may eliminate      *)
(* repeated source traversal without changing this mathematical boundary.     *)
(* ========================================================================== *)

needs "candle/cv_compute_whole_box_taylor.ml";;

module Candle_cv_whole_box_dim_taylor = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;

(* Ordinary exact-data algorithm. *)

let candle_q_program_interval_list_def = define
 `(candle_q_program_interval_list env [] =
     ([]:(((num#num)#num)#((num#num)#num))list)) /\
  (candle_q_program_interval_list env (CONS h t) =
     CONS (candle_q_program_interval env h)
       (candle_q_program_interval_list env t))`;;

let candle_q_program_interval_matrix_def = define
 `(candle_q_program_interval_matrix env [] =
     ([]:((((num#num)#num)#((num#num)#num))list)list)) /\
  (candle_q_program_interval_matrix env (CONS h t) =
     CONS (candle_q_program_interval_list env h)
       (candle_q_program_interval_matrix env t))`;;

let candle_q_center_environment_list_def = define
 `(candle_q_center_environment_list [] =
     ([]:(((num#num)#num)#((num#num)#num))list)) /\
  (candle_q_center_environment_list (CONS h t) =
     CONS (candle_q_point_interval (candle_q_midpoint h))
       (candle_q_center_environment_list t))`;;

let candle_q_radius_list_def = define
 `(candle_q_radius_list [] = ([]:((num#num)#num)list)) /\
  (candle_q_radius_list (CONS h t) =
     CONS (candle_q_radius h) (candle_q_radius_list t))`;;

let candle_q_dot_abs_upper_def = define
 `(candle_q_dot_abs_upper [] ys = candle_q_zero) /\
  (candle_q_dot_abs_upper (CONS x xs) [] = candle_q_zero) /\
  (candle_q_dot_abs_upper (CONS x xs) (CONS y ys) =
     candle_q_add
       (candle_q_mul x (candle_q_abs_upper y))
       (candle_q_dot_abs_upper xs ys))`;;

let candle_q_weighted_rows_abs_upper_def = define
 `(candle_q_weighted_rows_abs_upper radii [] row_lists = candle_q_zero) /\
  (candle_q_weighted_rows_abs_upper radii (CONS w ws) [] =
     candle_q_zero) /\
  (candle_q_weighted_rows_abs_upper radii (CONS w ws)
     (CONS interval_row row_tail) =
     candle_q_add
       (candle_q_mul w (candle_q_dot_abs_upper radii interval_row))
       (candle_q_weighted_rows_abs_upper radii ws row_tail))`;;

let candle_q_dim_taylor_upper_def = new_definition
 `candle_q_dim_taylor_upper radii f gradient hessian =
    candle_q_add (SND f)
      (candle_q_add
        (candle_q_dot_abs_upper radii gradient)
        (candle_q_mul candle_q_half
          (candle_q_weighted_rows_abs_upper radii radii hessian)))`;;

let candle_q_dim_whole_box_upper_def = new_definition
 `candle_q_dim_whole_box_upper pf pds pdds boxes =
    candle_q_dim_taylor_upper
      (candle_q_radius_list boxes)
      (candle_q_program_interval
        (candle_q_center_environment_list boxes) pf)
      (candle_q_program_interval_list
        (candle_q_center_environment_list boxes) pds)
      (candle_q_program_interval_matrix boxes pdds)`;;

let candle_q_box_valid_list_def = define
 `(candle_q_box_valid_list [] <=> T) /\
  (candle_q_box_valid_list (CONS h t) <=>
     candle_q_le (FST h) (SND h) /\ candle_q_box_valid_list t)`;;

let candle_q_rows_width_def = define
 `(candle_q_rows_width n
     ([]:((candle_q_instruction list)list)list) <=> T) /\
  (candle_q_rows_width n (CONS h t) <=>
     LENGTH h = n /\ candle_q_rows_width n t)`;;

let candle_q_dim_inputs_valid_def = new_definition
 `candle_q_dim_inputs_valid
    (pds:(candle_q_instruction list)list)
    (pdds:((candle_q_instruction list)list)list)
    (boxes:(((num#num)#num)#((num#num)#num))list) <=>
    LENGTH pds = LENGTH boxes /\
    LENGTH pdds = LENGTH boxes /\
    candle_q_rows_width (LENGTH boxes) pdds`;;

let candle_q_dim_whole_box_accept_def = new_definition
 `candle_q_dim_whole_box_accept pf pds pdds boxes <=>
    candle_q_dim_inputs_valid pds pdds boxes /\
    candle_q_box_valid_list boxes /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_whole_box_upper pf pds pdds boxes))`;;

(* cval encodings for program vectors/matrices and exact-rational vectors. *)

let candle_cv_q_instruction_lists_def = define
 `(candle_cv_q_instruction_lists [] = Cexp_num 0) /\
  (candle_cv_q_instruction_lists (CONS h t) =
     Cexp_pair (candle_cv_q_instruction_list h)
       (candle_cv_q_instruction_lists t))`;;

let candle_cv_q_instruction_matrix_def = define
 `(candle_cv_q_instruction_matrix [] = Cexp_num 0) /\
  (candle_cv_q_instruction_matrix (CONS h t) =
     Cexp_pair (candle_cv_q_instruction_lists h)
       (candle_cv_q_instruction_matrix t))`;;

let candle_cv_q_list_def = define
 `(candle_cv_q_list [] = Cexp_num 0) /\
  (candle_cv_q_list (CONS h t) =
     Cexp_pair (candle_cv_q h) (candle_cv_q_list t))`;;

let candle_cv_q_interval_matrix_def = define
 `(candle_cv_q_interval_matrix [] = Cexp_num 0) /\
  (candle_cv_q_interval_matrix (CONS h t) =
     Cexp_pair (candle_cv_q_interval_list h)
       (candle_cv_q_interval_matrix t))`;;

(* cval implementation.  Non-pair tails are the fail-closed empty-list case. *)

let candle_cv_q_center_environment_list_def = define
 `(candle_cv_q_center_environment_list (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_center_environment_list (Cexp_pair h t) =
     Cexp_pair
       (candle_cv_q_point_interval (candle_cv_q_midpoint h))
       (candle_cv_q_center_environment_list t))`;;

let candle_cv_q_radius_list_def = define
 `(candle_cv_q_radius_list (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_radius_list (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_radius h)
       (candle_cv_q_radius_list t))`;;

let candle_cv_q_program_interval_list_def = define
 `(candle_cv_q_program_interval_list env (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_program_interval_list env (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_program_interval env h)
       (candle_cv_q_program_interval_list env t))`;;

let candle_cv_q_program_interval_matrix_def = define
 `(candle_cv_q_program_interval_matrix env (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_program_interval_matrix env (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_program_interval_list env h)
       (candle_cv_q_program_interval_matrix env t))`;;

let candle_cv_q_dot_abs_upper_def = define
 `(candle_cv_q_dot_abs_upper (Cexp_num n) ys = candle_cv_q_zero) /\
  (candle_cv_q_dot_abs_upper (Cexp_pair x xs) (Cexp_num n) =
     candle_cv_q_zero) /\
  (candle_cv_q_dot_abs_upper (Cexp_pair x xs) (Cexp_pair y ys) =
     candle_cv_q_add
       (candle_cv_q_mul x (candle_cv_q_abs_upper y))
       (candle_cv_q_dot_abs_upper xs ys))`;;

let candle_cv_q_weighted_rows_abs_upper_def = define
 `(candle_cv_q_weighted_rows_abs_upper radii (Cexp_num n) row_lists =
     candle_cv_q_zero) /\
  (candle_cv_q_weighted_rows_abs_upper
     radii (Cexp_pair w ws) (Cexp_num n) = candle_cv_q_zero) /\
  (candle_cv_q_weighted_rows_abs_upper
     radii (Cexp_pair w ws) (Cexp_pair interval_row row_tail) =
     candle_cv_q_add
       (candle_cv_q_mul w
         (candle_cv_q_dot_abs_upper radii interval_row))
       (candle_cv_q_weighted_rows_abs_upper radii ws row_tail))`;;

let candle_cv_q_dim_taylor_upper_def = new_definition
 `candle_cv_q_dim_taylor_upper radii f gradient hessian =
    candle_cv_q_add (Cexp_snd f)
      (candle_cv_q_add
        (candle_cv_q_dot_abs_upper radii gradient)
        (candle_cv_q_mul candle_cv_q_half
          (candle_cv_q_weighted_rows_abs_upper
            radii radii hessian)))`;;

let candle_cv_q_dim_whole_box_upper_def = new_definition
 `candle_cv_q_dim_whole_box_upper pf pds pdds boxes =
    candle_cv_q_dim_taylor_upper
      (candle_cv_q_radius_list boxes)
      (candle_cv_q_program_interval
        (candle_cv_q_center_environment_list boxes) pf)
      (candle_cv_q_program_interval_list
        (candle_cv_q_center_environment_list boxes) pds)
      (candle_cv_q_program_interval_matrix boxes pdds)`;;

let candle_cv_list_length_def = define
 `(candle_cv_list_length (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_list_length (Cexp_pair h t) =
     Cexp_add (Cexp_num 1) (candle_cv_list_length t))`;;

let candle_cv_q_box_valid_list_def = define
 `(candle_cv_q_box_valid_list (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_q_box_valid_list (Cexp_pair h t) =
     Cexp_if
       (candle_cv_q_le (Cexp_fst h) (Cexp_snd h))
       (candle_cv_q_box_valid_list t) (Cexp_num 0))`;;

let candle_cv_q_rows_width_def = define
 `(candle_cv_q_rows_width n (Cexp_num z) = Cexp_num 1) /\
  (candle_cv_q_rows_width n (Cexp_pair h t) =
     Cexp_if (Cexp_eq (candle_cv_list_length h) n)
       (candle_cv_q_rows_width n t) (Cexp_num 0))`;;

let candle_cv_q_dim_inputs_valid_def = new_definition
 `candle_cv_q_dim_inputs_valid pds pdds boxes =
    Cexp_if
      (Cexp_eq (candle_cv_list_length pds)
        (candle_cv_list_length boxes))
      (Cexp_if
        (Cexp_eq (candle_cv_list_length pdds)
          (candle_cv_list_length boxes))
        (candle_cv_q_rows_width (candle_cv_list_length boxes) pdds)
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_q_dim_whole_box_finish_def = new_definition
 `candle_cv_q_dim_whole_box_finish inputs_valid box_valid upper =
    Cexp_pair
      (Cexp_if inputs_valid
        (Cexp_if box_valid
          (Cexp_if (candle_cv_q_le candle_cv_q_zero upper)
            (Cexp_num 0) (Cexp_num 1))
          (Cexp_num 0))
        (Cexp_num 0))
      upper`;;

let candle_cv_q_dim_whole_box_check_def = new_definition
 `candle_cv_q_dim_whole_box_check pf pds pdds boxes =
    candle_cv_q_dim_whole_box_finish
      (candle_cv_q_dim_inputs_valid pds pdds boxes)
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_whole_box_upper pf pds pdds boxes)`;;

let candle_cv_q_center_environment_list_compute = prove
 (`!boxes.
     candle_cv_q_center_environment_list boxes =
     Cexp_if (Cexp_ispair boxes)
       (Cexp_pair
         (candle_cv_q_point_interval
           (candle_cv_q_midpoint (Cexp_fst boxes)))
         (candle_cv_q_center_environment_list (Cexp_snd boxes)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `boxes:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_center_environment_list_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_radius_list_compute = prove
 (`!boxes.
     candle_cv_q_radius_list boxes =
     Cexp_if (Cexp_ispair boxes)
       (Cexp_pair (candle_cv_q_radius (Cexp_fst boxes))
         (candle_cv_q_radius_list (Cexp_snd boxes)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `boxes:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_radius_list_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_program_interval_list_compute = prove
 (`!env programs.
     candle_cv_q_program_interval_list env programs =
     Cexp_if (Cexp_ispair programs)
       (Cexp_pair
         (candle_cv_q_program_interval env (Cexp_fst programs))
         (candle_cv_q_program_interval_list env (Cexp_snd programs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `programs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_program_interval_list_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_program_interval_matrix_compute = prove
 (`!env program_matrix.
     candle_cv_q_program_interval_matrix env program_matrix =
     Cexp_if (Cexp_ispair program_matrix)
       (Cexp_pair
         (candle_cv_q_program_interval_list env (Cexp_fst program_matrix))
         (candle_cv_q_program_interval_matrix
           env (Cexp_snd program_matrix)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program_matrix:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_program_interval_matrix_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dot_abs_upper_compute = prove
 (`!xs ys.
     candle_cv_q_dot_abs_upper xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (candle_cv_q_add
           (candle_cv_q_mul (Cexp_fst xs)
             (candle_cv_q_abs_upper (Cexp_fst ys)))
           (candle_cv_q_dot_abs_upper (Cexp_snd xs) (Cexp_snd ys)))
         candle_cv_q_zero)
       candle_cv_q_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dot_abs_upper_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_weighted_rows_abs_upper_compute = prove
 (`!radii weights row_lists.
     candle_cv_q_weighted_rows_abs_upper radii weights row_lists =
     Cexp_if (Cexp_ispair weights)
       (Cexp_if (Cexp_ispair row_lists)
         (candle_cv_q_add
           (candle_cv_q_mul (Cexp_fst weights)
             (candle_cv_q_dot_abs_upper radii (Cexp_fst row_lists)))
           (candle_cv_q_weighted_rows_abs_upper
             radii (Cexp_snd weights) (Cexp_snd row_lists)))
         candle_cv_q_zero)
       candle_cv_q_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `weights:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_weighted_rows_abs_upper_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_list_length_compute = prove
 (`!items.
     candle_cv_list_length items =
     Cexp_if (Cexp_ispair items)
       (Cexp_add (Cexp_num 1)
         (candle_cv_list_length (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_list_length_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_q_box_valid_list_compute = prove
 (`!boxes.
     candle_cv_q_box_valid_list boxes =
     Cexp_if (Cexp_ispair boxes)
       (Cexp_if
         (candle_cv_q_le
           (Cexp_fst (Cexp_fst boxes))
           (Cexp_snd (Cexp_fst boxes)))
         (candle_cv_q_box_valid_list (Cexp_snd boxes))
         (Cexp_num 0))
       (Cexp_num 1)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `boxes:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_box_valid_list_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_rows_width_compute = prove
 (`!n row_lists.
     candle_cv_q_rows_width n row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_if
         (Cexp_eq
           (candle_cv_list_length (Cexp_fst row_lists)) n)
         (candle_cv_q_rows_width n (Cexp_snd row_lists))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_rows_width_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_whole_box_compute_eqs =
  candle_cv_q_interval_program_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_zero_compute;
    candle_cv_q_half_compute;
    candle_cv_q_midpoint_def;
    candle_cv_q_radius_def;
    candle_cv_q_point_interval_def;
    candle_cv_q_abs_upper_def;
    candle_cv_q_program_interval_compute;
    candle_cv_q_center_environment_list_compute;
    candle_cv_q_radius_list_compute;
    candle_cv_q_program_interval_list_compute;
    candle_cv_q_program_interval_matrix_compute;
    candle_cv_q_dot_abs_upper_compute;
    candle_cv_q_weighted_rows_abs_upper_compute;
    candle_cv_list_length_compute;
    candle_cv_q_box_valid_list_compute;
    candle_cv_q_rows_width_compute;
    candle_cv_q_dim_inputs_valid_def;
    candle_cv_q_dim_whole_box_finish_def;
    candle_cv_q_dim_taylor_upper_def;
    candle_cv_q_dim_whole_box_upper_def;
    candle_cv_q_dim_whole_box_check_def];;

(* Representation theorems. *)

let candle_cv_q_center_environment_list_correct = prove
 (`!boxes.
     candle_cv_q_center_environment_list
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_interval_list
       (candle_q_center_environment_list boxes)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_center_environment_list_def;
                  candle_cv_q_interval_list_def;
                  candle_q_center_environment_list_def;
                  candle_cv_q_midpoint_correct;
                  candle_cv_q_point_interval_correct]);;

let candle_cv_q_radius_list_correct = prove
 (`!boxes.
     candle_cv_q_radius_list (candle_cv_q_interval_list boxes) =
     candle_cv_q_list (candle_q_radius_list boxes)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_radius_list_def;
                  candle_cv_q_interval_list_def; candle_cv_q_list_def;
                  candle_q_radius_list_def; candle_cv_q_radius_correct]);;

let candle_cv_q_program_interval_list_correct = prove
 (`!programs env.
     candle_cv_q_program_interval_list
       (candle_cv_q_interval_list env)
       (candle_cv_q_instruction_lists programs) =
     candle_cv_q_interval_list
       (candle_q_program_interval_list env programs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_program_interval_list_def;
                  candle_cv_q_instruction_lists_def;
                  candle_cv_q_interval_list_def;
                  candle_q_program_interval_list_def;
                  candle_cv_q_program_interval_correct]);;

let candle_cv_q_program_interval_matrix_correct = prove
 (`!program_matrix env.
     candle_cv_q_program_interval_matrix
       (candle_cv_q_interval_list env)
       (candle_cv_q_instruction_matrix program_matrix) =
     candle_cv_q_interval_matrix
       (candle_q_program_interval_matrix env program_matrix)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_program_interval_matrix_def;
                  candle_cv_q_instruction_matrix_def;
                  candle_cv_q_interval_matrix_def;
                  candle_q_program_interval_matrix_def;
                  candle_cv_q_program_interval_list_correct]);;

let candle_cv_q_dot_abs_upper_correct = prove
 (`!xs ys.
     candle_cv_q_dot_abs_upper
       (candle_cv_q_list xs) (candle_cv_q_interval_list ys) =
     candle_cv_q (candle_q_dot_abs_upper xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_list_def; candle_cv_q_dot_abs_upper_def;
                candle_q_dot_abs_upper_def; candle_cv_q_zero_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_list_def;
                    candle_cv_q_interval_list_def;
                    candle_cv_q_dot_abs_upper_def;
                    candle_q_dot_abs_upper_def;
                    candle_cv_q_zero_def;
                    candle_cv_q_abs_upper_correct;
                    candle_cv_q_mul_correct; candle_cv_q_add_correct]]);;

let candle_cv_q_weighted_rows_abs_upper_correct = prove
 (`!radii weights row_lists.
     candle_cv_q_weighted_rows_abs_upper
       (candle_cv_q_list radii) (candle_cv_q_list weights)
       (candle_cv_q_interval_matrix row_lists) =
     candle_cv_q
       (candle_q_weighted_rows_abs_upper radii weights row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_list_def;
                candle_cv_q_weighted_rows_abs_upper_def;
                candle_q_weighted_rows_abs_upper_def;
                candle_cv_q_zero_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_list_def;
                    candle_cv_q_interval_matrix_def;
                    candle_cv_q_weighted_rows_abs_upper_def;
                    candle_q_weighted_rows_abs_upper_def;
                    candle_cv_q_zero_def;
                    candle_cv_q_dot_abs_upper_correct;
                    candle_cv_q_mul_correct; candle_cv_q_add_correct]]);;

let candle_cv_q_dim_taylor_upper_correct = prove
 (`!radii f gradient hessian.
     candle_cv_q_dim_taylor_upper
       (candle_cv_q_list radii) (candle_cv_q_interval f)
       (candle_cv_q_interval_list gradient)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q
       (candle_q_dim_taylor_upper radii f gradient hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_upper_def;
              candle_q_dim_taylor_upper_def;
              candle_cv_q_interval_snd_correct;
              candle_cv_q_half_def;
              candle_cv_q_dot_abs_upper_correct;
              candle_cv_q_weighted_rows_abs_upper_correct;
              candle_cv_q_mul_correct; candle_cv_q_add_correct]);;

let candle_cv_q_dim_whole_box_upper_correct = prove
 (`!pf pds pdds boxes.
     candle_cv_q_dim_whole_box_upper
       (candle_cv_q_instruction_list pf)
       (candle_cv_q_instruction_lists pds)
       (candle_cv_q_instruction_matrix pdds)
       (candle_cv_q_interval_list boxes) =
     candle_cv_q
       (candle_q_dim_whole_box_upper pf pds pdds boxes)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_whole_box_upper_def;
              candle_q_dim_whole_box_upper_def;
              candle_cv_q_radius_list_correct;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_program_interval_correct;
              candle_cv_q_program_interval_list_correct;
              candle_cv_q_program_interval_matrix_correct;
              candle_cv_q_dim_taylor_upper_correct]);;

let candle_cv_list_length_correct = prove
 (`!items. candle_cv_list_length (candle_cv_q_list items) =
           Cexp_num (LENGTH items)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_list_def; candle_cv_list_length_def; LENGTH];
    ASM_REWRITE_TAC[candle_cv_q_list_def; candle_cv_list_length_def;
                    LENGTH; cexp_add_def] THEN
    AP_TERM_TAC THEN ARITH_TAC]);;

let candle_cv_instruction_lists_length_correct = prove
 (`!programs.
     candle_cv_list_length (candle_cv_q_instruction_lists programs) =
     Cexp_num (LENGTH programs)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_instruction_lists_def;
                candle_cv_list_length_def; LENGTH];
    ASM_REWRITE_TAC[candle_cv_q_instruction_lists_def;
                    candle_cv_list_length_def; LENGTH; cexp_add_def;
                    ARITH_RULE `1 + n = SUC n`]]);;

let candle_cv_instruction_matrix_length_correct = prove
 (`!program_matrix.
     candle_cv_list_length
       (candle_cv_q_instruction_matrix program_matrix) =
     Cexp_num (LENGTH program_matrix)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_instruction_matrix_def;
                candle_cv_list_length_def; LENGTH];
    ASM_REWRITE_TAC[candle_cv_q_instruction_matrix_def;
                    candle_cv_list_length_def; LENGTH; cexp_add_def;
                    ARITH_RULE `1 + n = SUC n`]]);;

let candle_cv_interval_list_length_correct = prove
 (`!boxes.
     candle_cv_list_length (candle_cv_q_interval_list boxes) =
     Cexp_num (LENGTH boxes)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_interval_list_def;
                candle_cv_list_length_def; LENGTH];
    ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                    candle_cv_list_length_def; LENGTH; cexp_add_def;
                    ARITH_RULE `1 + n = SUC n`]]);;

let candle_cv_q_interval_valid_correct = prove
 (`!i.
     candle_cv_q_le
       (Cexp_fst (candle_cv_q_interval i))
       (Cexp_snd (candle_cv_q_interval i)) =
     Cexp_num (if candle_q_le (FST i) (SND i) then SUC 0 else 0)`,
  REWRITE_TAC[candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct]);;

let candle_cv_q_box_valid_list_correct = prove
 (`!boxes.
     candle_cv_q_box_valid_list (candle_cv_q_interval_list boxes) =
     Cexp_num (if candle_q_box_valid_list boxes then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                  candle_cv_q_box_valid_list_def;
                  candle_q_box_valid_list_def;
                  candle_cv_q_interval_valid_correct] THEN
  ASM_CASES_TAC `candle_q_le (FST h) (SND h)` THEN
  ASM_REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_rows_width_correct = prove
 (`!n (program_matrix:((candle_q_instruction list)list)list).
     candle_cv_q_rows_width (Cexp_num n)
       (candle_cv_q_instruction_matrix program_matrix) =
     Cexp_num (if candle_q_rows_width n program_matrix
               then SUC 0 else 0)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_instruction_matrix_def;
                candle_cv_q_rows_width_def; candle_q_rows_width_def] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[candle_cv_q_instruction_matrix_def;
                    candle_cv_q_rows_width_def; candle_q_rows_width_def;
                    candle_cv_instruction_lists_length_correct;
                    cexp_eq_def; injectivity "cval"] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let candle_cv_q_dim_inputs_valid_correct = prove
 (`!pds pdds boxes.
     candle_cv_q_dim_inputs_valid
       (candle_cv_q_instruction_lists pds)
       (candle_cv_q_instruction_matrix pdds)
       (candle_cv_q_interval_list boxes) =
     Cexp_num
       (if candle_q_dim_inputs_valid pds pdds boxes
        then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_inputs_valid_def;
              candle_q_dim_inputs_valid_def;
              candle_cv_instruction_lists_length_correct;
              candle_cv_instruction_matrix_length_correct;
              candle_cv_interval_list_length_correct;
              candle_cv_q_rows_width_correct;
              cexp_eq_def; injectivity "cval"] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_whole_box_finish_correct = prove
 (`!inputs_valid box_valid upper.
     candle_cv_q_dim_whole_box_finish
       (Cexp_num (if inputs_valid then SUC 0 else 0))
       (Cexp_num (if box_valid then SUC 0 else 0))
       (candle_cv_q upper) =
     Cexp_pair
       (Cexp_num
         (if inputs_valid /\ box_valid /\
             ~(candle_q_le candle_q_zero upper)
          then SUC 0 else 0))
       (candle_cv_q upper)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_whole_box_finish_def;
              candle_cv_q_zero_def; candle_cv_q_le_correct] THEN
  ASM_CASES_TAC `inputs_valid:bool` THEN
  ASM_CASES_TAC `box_valid:bool` THEN
  ASM_CASES_TAC `candle_q_le candle_q_zero upper` THEN
  ASM_REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_whole_box_check_correct = prove
 (`!pf pds pdds boxes.
     candle_cv_q_dim_whole_box_check
       (candle_cv_q_instruction_list pf)
       (candle_cv_q_instruction_lists pds)
       (candle_cv_q_instruction_matrix pdds)
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_whole_box_accept pf pds pdds boxes
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_whole_box_upper pf pds pdds boxes))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_whole_box_check_def;
              candle_cv_q_dim_inputs_valid_correct;
              candle_cv_q_box_valid_list_correct;
              candle_cv_q_dim_whole_box_upper_correct;
              candle_cv_q_dim_whole_box_finish_correct;
              candle_q_dim_whole_box_accept_def; CONJ_ASSOC]);;

end;;
