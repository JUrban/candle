(* ========================================================================== *)
(* Complete analytic shared-jet check of a genuine captured Flyspeck NL leaf. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The authenticated polynomial source remains   *)
(* one compact leaf of one analytic program.  The program is evaluated once  *)
(* at the center and once over the whole box; no separately differentiated   *)
(* source programs are constructed.                                          *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_jet_check.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_jet_check;;

module Candle_cv_analytic_flyspeck_real_leaf_test = struct

let candle_real_analytic_axioms_before = axioms ();;
let _ = print_endline
  "CANDLE_CV_ANALYTIC_REAL_FLYSPECK phase=preparation event=begin";;

let candle_real_analytic_vector = `p:real^6`;;
let candle_real_analytic_real_lt = `(<):real->real->bool`;;
let candle_real_analytic_real_zero = `&0:real`;;

let candle_real_analytic_scalar_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_real_analytic_scalar_source =
  `&1 * &10 +
   (x1 * x4 * (--x1 + x2 + x3 - x4 + x5 + #4.0) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + #4.0) +
    x3 * #4.0 * (x1 + x2 - x3 + x4 + x5 - #4.0) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * #4.0 -
    x4 * x5 * #4.0) * -- &1`;;

let candle_real_analytic_lower =
  [`&4`; `&4`; `&4`; `&90601 / &10000`; `&4`; `&4`];;

let candle_real_analytic_upper =
  [`&3134400153601 / &640000000000`;
   `&3312128000001 / &640000000000`;
   `&3312128000001 / &640000000000`;
   `&3207537920001 / &320000000000`;
   `&1280000000001 / &320000000000`;
   `&3312128000001 / &640000000000`];;

let candle_real_analytic_source,
    candle_real_analytic_boxes,
    candle_real_analytic_polynomial,
    candle_real_analytic_reified_valid,
    candle_real_analytic_reified_source,
    candle_real_analytic_reified_program,
    candle_real_analytic_reified_run =
  candle_poly_prepare_scalar_fixture
    candle_real_analytic_vector
    candle_real_analytic_scalar_variables
    candle_real_analytic_scalar_source
    candle_real_analytic_lower
    candle_real_analytic_upper;;

let candle_real_analytic_expression =
  mk_comb (`Candle_analytic_poly`,candle_real_analytic_polynomial);;

let candle_real_analytic_compile_th =
  REWRITE_CONV
    [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
    (mk_comb (`candle_analytic_compile`,candle_real_analytic_expression));;

let candle_real_analytic_program =
  rand (concl candle_real_analytic_compile_th);;

let candle_real_analytic_program_rep =
  REWRITE_CONV
    [candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb
      (`candle_cv_analytic_instruction_list`,
       candle_real_analytic_program));;

let candle_real_analytic_boxes_rep =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,candle_real_analytic_boxes));;

let candle_real_analytic_program_rep_tm =
  rand (concl candle_real_analytic_program_rep);;

let candle_real_analytic_boxes_rep_tm =
  rand (concl candle_real_analytic_boxes_rep);;

let candle_real_analytic_compute_tm =
  list_mk_comb
    (`candle_cv_q_dim_analytic_jet_whole_box_check`,
     [candle_real_analytic_program_rep_tm;
      candle_real_analytic_boxes_rep_tm]);;

let _ =
  print_endline
    ("CANDLE_CV_ANALYTIC_REAL_FLYSPECK_PREP programs=1 " ^
     "analytic_instructions=" ^
     string_of_int (length (dest_list candle_real_analytic_program)) ^
     " polynomial_instructions=" ^
     string_of_int (length (dest_list candle_real_analytic_reified_program)));;
let _ = print_endline
  "CANDLE_CV_ANALYTIC_REAL_FLYSPECK phase=preparation event=end";;

let candle_real_analytic_compute_ground phase equations tm =
  print_endline
    ("CANDLE_CV_ANALYTIC_REAL_FLYSPECK phase=" ^ phase ^ " event=begin");
  let th = Kernel.compute (COMPUTE_INIT_THMS,equations) tm in
  print_endline
    ("CANDLE_CV_ANALYTIC_REAL_FLYSPECK phase=" ^ phase ^ " event=end");
  if hyp th <> [] then
    failwith ("analytic real-leaf compute assumptions in " ^ phase);
  th;;

(* Keep the expensive results explicit.  This both exposes their individual
   costs and lets theorem reconstruction reuse them without a second
   evaluation hidden inside the monolithic checker term. *)
let candle_real_analytic_center_environment_th =
  candle_real_analytic_compute_ground "center-environment"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (mk_comb
      (`candle_cv_q_center_environment_list`,
       candle_real_analytic_boxes_rep_tm));;

let candle_real_analytic_center_environment =
  rand (concl candle_real_analytic_center_environment_th);;

let candle_real_analytic_center_th =
  candle_real_analytic_compute_ground "center-full-jet"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [candle_real_analytic_center_environment;
        candle_real_analytic_program_rep_tm]));;

let candle_real_analytic_center =
  rand (concl candle_real_analytic_center_th);;

let candle_real_analytic_box_th =
  candle_real_analytic_compute_ground "box-full-jet"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [candle_real_analytic_boxes_rep_tm;
        candle_real_analytic_program_rep_tm]));;

let candle_real_analytic_box = rand (concl candle_real_analytic_box_th);;

let candle_real_analytic_domain_th =
  candle_real_analytic_compute_ground "domain-combine"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_bool_and`,
       [mk_comb
         (`candle_cv_q_dim_analytic_result_domain`,
          candle_real_analytic_center);
        mk_comb
         (`candle_cv_q_dim_analytic_result_domain`,
          candle_real_analytic_box)]));;

let candle_real_analytic_domain =
  rand (concl candle_real_analytic_domain_th);;

let candle_real_analytic_upper_th =
  candle_real_analytic_compute_ground "taylor-upper"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_analytic_jet_upper_pair`,
       [candle_real_analytic_boxes_rep_tm;
        candle_real_analytic_center;
        candle_real_analytic_box]));;

let candle_real_analytic_upper =
  rand (concl candle_real_analytic_upper_th);;

let candle_real_analytic_valid_th =
  candle_real_analytic_compute_ground "box-valid"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (mk_comb
      (`candle_cv_q_box_valid_list`,candle_real_analytic_boxes_rep_tm));;

let candle_real_analytic_valid =
  rand (concl candle_real_analytic_valid_th);;

let candle_real_analytic_finish_th =
  candle_real_analytic_compute_ground "finish"
    candle_cv_q_dim_analytic_jet_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_whole_box_finish`,
       [candle_real_analytic_domain;
        candle_real_analytic_valid;
        candle_real_analytic_upper]));;

let candle_real_analytic_finish =
  rand (concl candle_real_analytic_finish_th);;

let candle_real_analytic_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "analytic real-leaf final result is not a pair";;

let candle_real_analytic_verdict,candle_real_analytic_final_upper =
  candle_real_analytic_dest_pair candle_real_analytic_finish;;

if not (aconv candle_real_analytic_verdict `Cexp_num 1`) then
  failwith "analytic real-leaf numerical check rejected";;

let _ =
  print_endline
    ("CANDLE_CV_ANALYTIC_REAL_FLYSPECK_COMPUTE verdict=accept " ^
     "upper_term_chars=" ^
     string_of_int
       (String.length (string_of_term candle_real_analytic_final_upper)));;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_REAL_FLYSPECK phase=theorem-handoff event=begin";;

let candle_real_analytic_expansion_th =
  REWRITE_CONV
    [candle_cv_q_dim_analytic_jet_whole_box_check_def;
     candle_cv_q_dim_analytic_jet_finish_def]
    candle_real_analytic_compute_tm;;

let candle_real_analytic_evaluation_th =
  REWRITE_CONV
    [candle_real_analytic_center_environment_th;
     candle_real_analytic_center_th;
     candle_real_analytic_box_th;
     candle_real_analytic_domain_th;
     candle_real_analytic_upper_th;
     candle_real_analytic_valid_th;
     candle_real_analytic_finish_th]
    (rand (concl candle_real_analytic_expansion_th));;

let candle_real_analytic_compute_th =
  TRANS candle_real_analytic_expansion_th
    candle_real_analytic_evaluation_th;;

let candle_real_analytic_abstract_compute_th =
  let th =
    PURE_REWRITE_RULE
      [SYM candle_real_analytic_program_rep;
       SYM candle_real_analytic_boxes_rep]
      candle_real_analytic_compute_th in
  PURE_REWRITE_RULE [SYM candle_real_analytic_compile_th] th;;

let candle_real_analytic_correctness =
  SPECL
    [candle_real_analytic_expression;candle_real_analytic_boxes]
    candle_cv_q_dim_analytic_jet_whole_box_check_correct;;

if not
    (aconv (lhand (concl candle_real_analytic_abstract_compute_th))
           (lhand (concl candle_real_analytic_correctness))) then
  failwith "analytic real-leaf abstract/concrete checker lhs mismatch";;

let candle_real_analytic_accept_encoding =
  TRANS (SYM candle_real_analytic_abstract_compute_th)
    candle_real_analytic_correctness;;

let candle_real_analytic_numerical_goal =
  list_mk_comb
    (`candle_q_dim_analytic_jet_whole_box_numerical_accept`,
     [candle_real_analytic_expression;candle_real_analytic_boxes]);;

let candle_real_analytic_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_real_analytic_flag_th =
  let th =
    REWRITE_RULE[cexp_fst_def; injectivity "cval"; SYM ONE]
      (AP_TERM `Cexp_fst` candle_real_analytic_accept_encoding) in
  let expected =
    mk_eq
      (`1`,mk_cond (candle_real_analytic_numerical_goal,`1`,`0`)) in
  if aconv (concl th) expected then th
  else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then SYM th
  else failwith "analytic real-leaf numerical flag mismatch";;

let candle_real_analytic_numerical_th =
  MATCH_MP
    (SPEC candle_real_analytic_numerical_goal
      candle_real_analytic_flag_accept)
    candle_real_analytic_flag_th;;

let candle_real_analytic_valid_dim = prove
 (list_mk_comb
   (`candle_analytic_valid_dim`,
    [`6`;candle_real_analytic_expression]),
  REWRITE_TAC[candle_analytic_valid_dim_def] THEN
  ACCEPT_TAC candle_real_analytic_reified_valid);;

let candle_real_analytic_length_six = prove
 (mk_eq
   (mk_comb
     (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
      candle_real_analytic_boxes),
    `6`),
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_real_analytic_dim_six = DIMINDEX_CONV `dimindex (:6)`;;

let candle_real_analytic_vector_th =
  MATCH_MP
    (SPECL
      [candle_real_analytic_expression;candle_real_analytic_boxes]
      (REWRITE_RULE
        [candle_real_analytic_dim_six]
        (INST_TYPE
          [`:6`,`:N`]
          candle_q_dim_analytic_jet_whole_box_accept_sound)))
    (CONJ candle_real_analytic_valid_dim
      (CONJ candle_real_analytic_length_six
        candle_real_analytic_numerical_th));;

let candle_real_analytic_poly_bridge =
  MATCH_MP
    (ISPEC candle_real_analytic_polynomial
      (REWRITE_RULE
        [candle_real_analytic_dim_six]
        (INST_TYPE [`:6`,`:N`] candle_analytic_denote_dim_poly)))
    candle_real_analytic_reified_valid;;

let candle_real_analytic_original_source_th =
  REWRITE_RULE
    [candle_real_analytic_poly_bridge;
     candle_real_analytic_reified_source]
    candle_real_analytic_vector_th;;

let candle_real_analytic_bound_variable,
    candle_real_analytic_bound_source,
    candle_real_analytic_bound_zero =
  let p,body = dest_forall (concl candle_real_analytic_original_source_th) in
  let _,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source = dest_comb partial in
  if not (aconv relation candle_real_analytic_real_lt) then
    failwith "analytic real-leaf final theorem is not a strict real bound";
  p,source,zero;;

let candle_real_analytic_theorem_md5 =
  Digest.to_hex
    (Digest.string (string_of_thm candle_real_analytic_original_source_th));;

if hyp candle_real_analytic_compute_th <> [] ||
   hyp candle_real_analytic_reified_source <> [] ||
   hyp candle_real_analytic_reified_run <> [] ||
   hyp candle_real_analytic_numerical_th <> [] ||
   hyp candle_real_analytic_vector_th <> [] ||
   hyp candle_real_analytic_original_source_th <> [] ||
   not
     (aconv candle_real_analytic_bound_variable
       candle_real_analytic_vector) ||
   not
     (aconv candle_real_analytic_bound_source
       candle_real_analytic_source) ||
   not
     (aconv candle_real_analytic_bound_zero
       candle_real_analytic_real_zero) ||
   candle_real_analytic_theorem_md5 <>
     "eb48d518a0dfdeb62da3b6993dabb38b" then
  failwith "analytic real Flyspeck leaf theorem mismatch";;

let candle_real_analytic_axioms_after = axioms ();;
if length candle_real_analytic_axioms_after <>
     length candle_real_analytic_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_real_analytic_axioms_before)
       candle_real_analytic_axioms_after) then
  failwith "analytic real-leaf changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_REAL_FLYSPECK phase=theorem-handoff event=end";;
let _ =
  print_endline
    ("CANDLE_CV_ANALYTIC_REAL_FLYSPECK_RESULT programs=1 " ^
     "analytic_instructions=1 theorem_md5=" ^
     candle_real_analytic_theorem_md5);;
let _ = print_endline "CANDLE_CV_ANALYTIC_REAL_FLYSPECK_OK";;

end;;
