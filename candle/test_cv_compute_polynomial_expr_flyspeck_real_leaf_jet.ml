(* ========================================================================== *)
(* Complete shared-jet check of the same genuine captured Flyspeck NL leaf.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the 43-program comparison, this path   *)
(* compiles the authenticated source once, evaluates a first jet at the box  *)
(* center and one shared second-order jet over the box, then applies the      *)
(* language-wide analytic soundness theorem.                                 *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"] @
  !load_path;;

needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_sound.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_check;;
open Candle_cv_polynomial_expr_dim_jet_sound;;

module Candle_cv_real_flyspeck_leaf_jet_test = struct

let candle_real_jet_program_encode_conv program =
  REWRITE_CONV
    [candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_instruction_list`,program));;

let candle_real_jet_boxes_encode_conv boxes =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;

let candle_real_jet_vector = `p:real^6`;;
let candle_real_jet_real_lt = `(<):real->real->bool`;;
let candle_real_jet_real_zero = `&0:real`;;

let candle_real_jet_scalar_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_real_jet_scalar_source =
  `&1 * &10 +
   (x1 * x4 * (--x1 + x2 + x3 - x4 + x5 + #4.0) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + #4.0) +
    x3 * #4.0 * (x1 + x2 - x3 + x4 + x5 - #4.0) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * #4.0 -
    x4 * x5 * #4.0) * -- &1`;;

let candle_real_jet_lower =
  [`&4`; `&4`; `&4`; `&90601 / &10000`; `&4`; `&4`];;

let candle_real_jet_upper =
  [`&3134400153601 / &640000000000`;
   `&3312128000001 / &640000000000`;
   `&3312128000001 / &640000000000`;
   `&3207537920001 / &320000000000`;
   `&1280000000001 / &320000000000`;
   `&3312128000001 / &640000000000`];;

let candle_real_jet_source,
    candle_real_jet_boxes,
    candle_real_jet_expression,
    candle_real_jet_reified_valid,
    candle_real_jet_reified_source,
    candle_real_jet_reified_program,
    candle_real_jet_reified_run =
  candle_poly_prepare_scalar_fixture
    candle_real_jet_vector
    candle_real_jet_scalar_variables
    candle_real_jet_scalar_source
    candle_real_jet_lower
    candle_real_jet_upper;;

let candle_real_jet_expected_source = candle_real_jet_source;;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET phase=source-reify event=end instructions=" ^
     string_of_int (length (dest_list candle_real_jet_reified_program)));;

let candle_real_jet_compile_th =
  REWRITE_CONV [candle_poly_compile_def; APPEND]
    (mk_comb (`candle_poly_compile`,candle_real_jet_expression));;

if not
    (aconv (rand (concl candle_real_jet_compile_th))
           candle_real_jet_reified_program) then
  failwith "shared-jet compiler/reifier program mismatch";;

let candle_real_jet_program_rep =
  candle_real_jet_program_encode_conv candle_real_jet_reified_program;;

let candle_real_jet_boxes_rep =
  candle_real_jet_boxes_encode_conv candle_real_jet_boxes;;

let candle_real_jet_compute_tm =
  list_mk_comb
    (`candle_cv_q_dim_poly_jet_whole_box_check`,
     [rand (concl candle_real_jet_program_rep);
      rand (concl candle_real_jet_boxes_rep)]);;

let candle_real_jet_compute_ground phase equations tm =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET phase=" ^ phase ^ " event=begin");
  let th = compute equations tm in
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET phase=" ^ phase ^ " event=end");
  if hyp th <> [] then
    failwith ("shared-jet compute assumptions in " ^ phase);
  th;;

(* Evaluate the same shared-jet checker in explicit stages.  This keeps each
   cval term shallow, exposes the reusable center/box computations, and avoids
   requiring Kernel.compute to translate one deeply nested monolithic rhs. *)
let candle_real_jet_program_rep_tm =
  rand (concl candle_real_jet_program_rep);;

let candle_real_jet_boxes_rep_tm =
  rand (concl candle_real_jet_boxes_rep);;

let candle_real_jet_center_environment_th =
  candle_real_jet_compute_ground "center-environment"
    candle_cv_q_dim_first_jet_compute_eqs
    (mk_comb
      (`candle_cv_q_center_environment_list`,candle_real_jet_boxes_rep_tm));;

let candle_real_jet_center_environment =
  rand (concl candle_real_jet_center_environment_th);;

let candle_real_jet_center_th =
  candle_real_jet_compute_ground "center-first-jet"
    candle_cv_q_dim_first_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_first_jet_program`,
       [candle_real_jet_center_environment;
        candle_real_jet_program_rep_tm]));;

let candle_real_jet_center = rand (concl candle_real_jet_center_th);;

let candle_real_jet_box_th =
  candle_real_jet_compute_ground "box-second-jet"
    candle_cv_q_dim_first_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_jet_program`,
       [candle_real_jet_boxes_rep_tm;candle_real_jet_program_rep_tm]));;

let candle_real_jet_box = rand (concl candle_real_jet_box_th);;

let candle_real_jet_upper_th =
  candle_real_jet_compute_ground "taylor-handoff"
    (candle_cv_q_dim_first_jet_compute_eqs @
     [SPEC_ALL candle_cv_q_jet_upper_pair_def])
    (list_mk_comb
      (`candle_cv_q_jet_upper_pair`,
       [candle_real_jet_boxes_rep_tm;
        candle_real_jet_center;candle_real_jet_box]));;

let candle_real_jet_upper = rand (concl candle_real_jet_upper_th);;

let candle_real_jet_valid_th =
  candle_real_jet_compute_ground "box-valid"
    candle_cv_q_dim_first_jet_compute_eqs
    (mk_comb
      (`candle_cv_q_box_valid_list`,candle_real_jet_boxes_rep_tm));;

let candle_real_jet_valid = rand (concl candle_real_jet_valid_th);;

let candle_real_jet_finish_th =
  candle_real_jet_compute_ground "finish"
    candle_cv_q_dim_first_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_whole_box_finish`,
       [`Cexp_num 1`;candle_real_jet_valid;candle_real_jet_upper]));;

let candle_real_jet_finish = rand (concl candle_real_jet_finish_th);;

let candle_real_jet_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "shared-jet final result is not a pair";;

let candle_real_jet_verdict,candle_real_jet_final_upper =
  candle_real_jet_dest_pair candle_real_jet_finish;;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET_RESULT verdict=" ^
     (if aconv candle_real_jet_verdict `Cexp_num 1`
      then "accept" else "reject") ^
     " upper_term_chars=" ^
     string_of_int (String.length (string_of_term candle_real_jet_final_upper)));;

let candle_real_jet_expansion_th =
  REWRITE_CONV
    [candle_cv_q_dim_poly_jet_whole_box_check_def;
     candle_cv_q_dim_poly_jet_whole_box_upper_def]
    candle_real_jet_compute_tm;;

let candle_real_jet_evaluation_th =
  REWRITE_CONV
    [candle_real_jet_center_environment_th;
     candle_real_jet_center_th;
     candle_real_jet_box_th;
     candle_real_jet_upper_th;
     candle_real_jet_valid_th;
     candle_real_jet_finish_th]
    (rand (concl candle_real_jet_expansion_th));;

let candle_real_jet_compute_th =
  TRANS candle_real_jet_expansion_th candle_real_jet_evaluation_th;;

let candle_real_jet_correctness =
  SPECL
    [candle_real_jet_expression;candle_real_jet_boxes]
    candle_cv_q_dim_poly_jet_whole_box_check_correct;;

let candle_real_jet_abstract_compute_th =
  let th =
    PURE_REWRITE_RULE
      [SYM candle_real_jet_program_rep;
       SYM candle_real_jet_boxes_rep]
      candle_real_jet_compute_th in
  PURE_REWRITE_RULE [SYM candle_real_jet_compile_th] th;;

if not
    (aconv (lhand (concl candle_real_jet_abstract_compute_th))
           (lhand (concl candle_real_jet_correctness))) then
  failwith "shared-jet abstract/concrete checker lhs mismatch";;

let candle_real_jet_accept_encoding_th =
  TRANS (SYM candle_real_jet_abstract_compute_th)
    candle_real_jet_correctness;;

let candle_real_jet_numerical_goal =
  list_mk_comb
    (`candle_q_dim_poly_jet_whole_box_numerical_accept`,
     [candle_real_jet_expression;candle_real_jet_boxes]);;

let candle_real_jet_suc_one = SYM ONE;;

let candle_real_jet_abstract_verdict_th =
  PURE_REWRITE_RULE [candle_real_jet_suc_one]
    (REWRITE_RULE [cexp_fst_def]
      (AP_TERM `Cexp_fst` candle_real_jet_accept_encoding_th));;

let candle_real_jet_computed_verdict_th =
  REWRITE_RULE [cexp_fst_def]
    (AP_TERM `Cexp_fst` candle_real_jet_finish_th);;

if not
    (aconv (lhand (concl candle_real_jet_computed_verdict_th))
           (lhand (concl candle_real_jet_abstract_verdict_th))) then
  begin
    print_endline
      ("CANDLE_CV_REAL_FLYSPECK_JET computed_lhs=" ^
       string_of_term (lhand (concl candle_real_jet_computed_verdict_th)));
    print_endline
      ("CANDLE_CV_REAL_FLYSPECK_JET abstract_lhs=" ^
       string_of_term (lhand (concl candle_real_jet_abstract_verdict_th)));
    failwith "shared-jet computed/abstract verdict lhs mismatch"
  end;;

let candle_real_jet_verdict_th =
  TRANS (SYM candle_real_jet_computed_verdict_th)
    candle_real_jet_abstract_verdict_th;;

let candle_real_jet_flag_num_th =
  REWRITE_RULE [injectivity "cval"] candle_real_jet_verdict_th;;

let candle_real_jet_expected_flag =
  mk_eq
    (`1`,
     mk_cond (candle_real_jet_numerical_goal,`1`,`0`));;

let candle_real_jet_flag_num_th =
  if aconv (concl candle_real_jet_flag_num_th)
       candle_real_jet_expected_flag then
    candle_real_jet_flag_num_th
  else if aconv (concl candle_real_jet_flag_num_th)
            (mk_eq
              (rand candle_real_jet_expected_flag,
               lhand candle_real_jet_expected_flag)) then
    SYM candle_real_jet_flag_num_th
  else begin
    print_endline
      ("CANDLE_CV_REAL_FLYSPECK_JET flag_actual=" ^
       string_of_term (concl candle_real_jet_flag_num_th));
    print_endline
      ("CANDLE_CV_REAL_FLYSPECK_JET flag_expected=" ^
       string_of_term candle_real_jet_expected_flag);
    failwith "shared-jet numerical flag theorem mismatch"
  end;;

let candle_real_jet_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_real_jet_numerical_th =
  MATCH_MP
    (SPEC candle_real_jet_numerical_goal candle_real_jet_flag_accept)
    candle_real_jet_flag_num_th;;

let candle_real_jet_length_six = prove
 (mk_eq
   (mk_comb
     (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
      candle_real_jet_boxes),
    `6`),
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_real_jet_dim_six = DIMINDEX_CONV `dimindex (:6)`;;

let candle_real_jet_vector_th =
  MATCH_MP
    (SPECL
      [candle_real_jet_expression;candle_real_jet_boxes]
      (REWRITE_RULE
        [candle_real_jet_dim_six]
        (INST_TYPE
          [`:6`,`:N`]
          candle_q_dim_poly_jet_whole_box_accept_sound)))
    (CONJ candle_real_jet_reified_valid
      (CONJ candle_real_jet_length_six candle_real_jet_numerical_th));;

let candle_real_jet_original_source_th =
  REWRITE_RULE [candle_real_jet_reified_source]
    candle_real_jet_vector_th;;

let candle_real_jet_bound_variable,
    candle_real_jet_bound_premise,
    candle_real_jet_bound_source,
    candle_real_jet_bound_zero =
  let p,body = dest_forall (concl candle_real_jet_original_source_th) in
  let premise,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source = dest_comb partial in
  if not (aconv relation candle_real_jet_real_lt) then
    failwith "shared-jet final theorem is not a strict real bound";
  p,premise,source,zero;;

if hyp candle_real_jet_compute_th <> [] ||
   hyp candle_real_jet_reified_source <> [] ||
   hyp candle_real_jet_reified_run <> [] ||
   hyp candle_real_jet_numerical_th <> [] ||
   hyp candle_real_jet_vector_th <> [] ||
   hyp candle_real_jet_original_source_th <> [] ||
   not (aconv candle_real_jet_bound_variable candle_real_jet_vector) ||
   not (aconv candle_real_jet_bound_source candle_real_jet_expected_source) ||
   not (aconv candle_real_jet_bound_zero candle_real_jet_real_zero) then
  failwith "shared-jet real Flyspeck leaf theorem mismatch";;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET_STATS programs=1 theorem_md5=" ^
     Digest.to_hex
       (Digest.string (string_of_thm candle_real_jet_original_source_th)));;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_JET_OK";;

end;;
