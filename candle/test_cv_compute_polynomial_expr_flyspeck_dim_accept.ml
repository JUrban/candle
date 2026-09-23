load_path :=
  ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"] @
  !load_path;;

needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_dim_sound.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_reify.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_check;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_flyspeck_reify;;

let candle_poly_dim_accept_interval_type =
  `:((num#num)#num)#((num#num)#num)`;;

let candle_poly_dim_accept_program_encode_conv program =
  REWRITE_CONV
    [candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_instruction_list`,program));;

let candle_poly_dim_accept_boxes_encode_conv boxes =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;

let candle_poly_dim_accept_vector = `p:real^6`;;

let candle_poly_dim_accept_source =
  `(p:real^6)$1 * p$6 + p$3 pow 2 + -- &1`;;

let candle_poly_dim_accept_expression,
    candle_poly_dim_accept_reified_valid,
    candle_poly_dim_accept_reified_source,
    candle_poly_dim_accept_reified_program,
    candle_poly_dim_accept_reified_run =
  candle_poly_reify_vector_expression
    candle_poly_dim_accept_vector candle_poly_dim_accept_source;;

let candle_poly_dim_accept_box =
 `((((0,0),0),((1,0),7)):
   ((num#num)#num)#((num#num)#num))`;;

let candle_poly_dim_accept_boxes =
  mk_list
    (replicate candle_poly_dim_accept_box 6,
     candle_poly_dim_accept_interval_type);;

let rec candle_poly_dim_accept_repeat_conv n conv =
  if n = 0 then ALL_CONV
  else conv THENC candle_poly_dim_accept_repeat_conv (n - 1) conv;;

let candle_poly_dim_accept_diff_conv =
  candle_poly_dim_accept_repeat_conv 16
    (SIMP_CONV[candle_poly_diff2_def; candle_poly_diff_def; ARITH]);;

let candle_poly_dim_accept_compile_conv =
  candle_poly_dim_accept_repeat_conv 16
    (SIMP_CONV[candle_poly_compile_def; APPEND]);;

let candle_poly_dim_accept_diff di =
  rand
    (concl
      (candle_poly_dim_accept_diff_conv
        (list_mk_comb
          (`candle_poly_diff`,
           [mk_small_numeral di;candle_poly_dim_accept_expression]))));;

let candle_poly_dim_accept_diff2 dj di =
  rand
    (concl
      (candle_poly_dim_accept_diff_conv
        (list_mk_comb
          (`candle_poly_diff2`,
           [mk_small_numeral dj;mk_small_numeral di;
            candle_poly_dim_accept_expression]))));;

let candle_poly_dim_accept_compile expression =
  rand
    (concl
      (candle_poly_dim_accept_compile_conv
        (mk_comb (`candle_poly_compile`,expression))));;

let candle_poly_dim_accept_pf =
  candle_poly_dim_accept_compile candle_poly_dim_accept_expression;;

let candle_poly_dim_accept_pds =
  map
    (fun di ->
      candle_poly_dim_accept_compile (candle_poly_dim_accept_diff di))
    (0--5);;

let candle_poly_dim_accept_pdds =
  map
    (fun di ->
      map
        (fun dj ->
          candle_poly_dim_accept_compile
            (candle_poly_dim_accept_diff2 dj di))
        (0--5))
    (0--5);;

let candle_poly_dim_accept_pds_tm =
  mk_list
    (candle_poly_dim_accept_pds,
     `:candle_q_instruction list`);;

let candle_poly_dim_accept_pdds_tm =
  mk_list
    (map
      (fun row -> mk_list (row,`:candle_q_instruction list`))
      candle_poly_dim_accept_pdds,
     `:(candle_q_instruction list)list`);;

let candle_poly_dim_accept_pf_rep =
  candle_poly_dim_accept_program_encode_conv candle_poly_dim_accept_pf;;

let candle_poly_dim_accept_pds_rep =
  REWRITE_CONV
    (candle_cv_q_instruction_lists_def ::
     map candle_poly_dim_accept_program_encode_conv
       candle_poly_dim_accept_pds)
    (mk_comb
      (`candle_cv_q_instruction_lists`,
       candle_poly_dim_accept_pds_tm));;

let candle_poly_dim_accept_pdds_rep =
  REWRITE_CONV
    (candle_cv_q_instruction_matrix_def ::
     candle_cv_q_instruction_lists_def ::
     List.flatten
       (map
         (map candle_poly_dim_accept_program_encode_conv)
         candle_poly_dim_accept_pdds))
    (mk_comb
      (`candle_cv_q_instruction_matrix`,
       candle_poly_dim_accept_pdds_tm));;

let candle_poly_dim_accept_boxes_rep =
  candle_poly_dim_accept_boxes_encode_conv candle_poly_dim_accept_boxes;;

let candle_poly_dim_accept_compute_tm =
  list_mk_comb
    (`candle_cv_q_dim_whole_box_check`,
     [rand (concl candle_poly_dim_accept_pf_rep);
      rand (concl candle_poly_dim_accept_pds_rep);
      rand (concl candle_poly_dim_accept_pdds_rep);
      rand (concl candle_poly_dim_accept_boxes_rep)]);;

let candle_poly_dim_accept_compute_th =
  compute candle_cv_q_dim_whole_box_compute_eqs
    candle_poly_dim_accept_compute_tm;;

let candle_poly_dim_accept_correctness =
  REWRITE_RULE
    [candle_poly_dim_accept_pf_rep;
     candle_poly_dim_accept_pds_rep;
     candle_poly_dim_accept_pdds_rep;
     candle_poly_dim_accept_boxes_rep;
     candle_poly_dim_accept_compute_th]
    (SPECL
      [candle_poly_dim_accept_pf;
       candle_poly_dim_accept_pds_tm;
       candle_poly_dim_accept_pdds_tm;
       candle_poly_dim_accept_boxes]
      candle_cv_q_dim_whole_box_check_correct);;

let candle_poly_dim_accept_numerical_goal =
  list_mk_comb
    (`candle_q_dim_whole_box_accept`,
     [candle_poly_dim_accept_pf;
      candle_poly_dim_accept_pds_tm;
      candle_poly_dim_accept_pdds_tm;
      candle_poly_dim_accept_boxes]);;

let candle_poly_dim_accept_numerical_th = prove
 (candle_poly_dim_accept_numerical_goal,
  MP_TAC candle_poly_dim_accept_correctness THEN
  REWRITE_TAC[injectivity "cval"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_poly_dim_accept_goal =
  list_mk_comb
    (`candle_poly_dim_whole_box_accept`,
     [candle_poly_dim_accept_expression;
      candle_poly_dim_accept_boxes]);;

let candle_poly_dim_accept_length_six =
  prove
   (mk_eq
     (mk_comb
       (`LENGTH:
          (((num#num)#num)#((num#num)#num))list->num`,
        candle_poly_dim_accept_boxes),
      `6`),
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_poly_dim_accept_source_numerical_goal =
  list_mk_comb
    (`candle_q_dim_whole_box_accept`,
     [mk_comb
       (`candle_poly_compile`,candle_poly_dim_accept_expression);
      list_mk_comb
       (`candle_poly_gradient_programs`,
        [`6`;candle_poly_dim_accept_expression]);
      list_mk_comb
       (`candle_poly_hessian_programs`,
        [`6`;candle_poly_dim_accept_expression]);
      candle_poly_dim_accept_boxes]);;

let candle_poly_dim_accept_source_numerical_norm =
  (REWRITE_CONV
    [candle_poly_gradient_programs_def;
     candle_poly_hessian_programs_def] THENC
   DEPTH_CONV LIST_OF_SEQ_CONV THENC
   DEPTH_CONV BETA_CONV THENC
   REPEATC
    (CHANGED_CONV
      (SIMP_CONV
        [o_THM; candle_poly_diff2_def; candle_poly_diff_def;
         candle_poly_compile_def; APPEND; ARITH])) THENC
   NUM_REDUCE_CONV)
    candle_poly_dim_accept_source_numerical_goal;;

if not
    (aconv
      (rand (concl candle_poly_dim_accept_source_numerical_norm))
      candle_poly_dim_accept_numerical_goal) then
  failwith "derived source programs do not match computed programs";;

let candle_poly_dim_accept_source_numerical_th =
  EQ_MP
    (SYM candle_poly_dim_accept_source_numerical_norm)
    candle_poly_dim_accept_numerical_th;;

let candle_poly_dim_accept_valid_th =
  candle_poly_dim_accept_reified_valid;;

let candle_poly_dim_accept_components_th =
  CONJ
    candle_poly_dim_accept_valid_th
    candle_poly_dim_accept_source_numerical_th;;

let candle_poly_dim_accept_goal_rewrite =
  REWRITE_CONV
    [candle_poly_dim_whole_box_accept_def;
     candle_poly_dim_accept_length_six]
    candle_poly_dim_accept_goal;;

let candle_poly_dim_accept_th =
  EQ_MP
    (SYM candle_poly_dim_accept_goal_rewrite)
    candle_poly_dim_accept_components_th;;

let candle_poly_dim_accept_dim_six = DIMINDEX_CONV `dimindex (:6)`;;

let candle_poly_dim_accept_length =
  TRANS candle_poly_dim_accept_length_six
    (SYM candle_poly_dim_accept_dim_six);;

let candle_poly_dim_accept_original_th =
  MATCH_MP
    (SPECL
      [candle_poly_dim_accept_expression;candle_poly_dim_accept_boxes]
      (INST_TYPE
        [`:6`,`:N`]
        candle_poly_dim_whole_box_accept_sound))
    (CONJ candle_poly_dim_accept_length candle_poly_dim_accept_th);;

let candle_poly_dim_accept_original_source_th =
  REWRITE_RULE
    [candle_poly_dim_accept_reified_source]
    candle_poly_dim_accept_original_th;;

if hyp candle_poly_dim_accept_compute_th <> [] ||
   hyp candle_poly_dim_accept_reified_source <> [] ||
   hyp candle_poly_dim_accept_reified_run <> [] ||
   hyp candle_poly_dim_accept_numerical_th <> [] ||
   hyp candle_poly_dim_accept_source_numerical_th <> [] ||
   hyp candle_poly_dim_accept_th <> [] ||
   hyp candle_poly_dim_accept_original_th <> [] ||
   hyp candle_poly_dim_accept_original_source_th <> [] then
  failwith "computed Flyspeck whole-box handoff assumptions mismatch";;

print_endline
  "CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_DIM_ACCEPT_STATS programs=43";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_DIM_ACCEPT_OK";;
