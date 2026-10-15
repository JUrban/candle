(* ========================================================================== *)
(* Genuine Flyspeck [matan] source reification and reflected execution.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source expressions and boxes are obtained *)
(* from the authenticated [prep-TSKAJXY-GXSABWC DIV] target.  The preparation *)
(* selects data only: source equality and execution are checked by HOL.       *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;
needs "candle/cv_compute_analytic_expr_matan_domain_probe.ml";;
needs "candle/cv_compute_analytic_expr_reify.ml";;

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_matan_domain_probe;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;

module Candle_cv_analytic_expr_matan_genuine_reify_test = struct

let candle_matan_genuine_axioms_before = axioms ();;
let candle_matan_genuine_started = Unix.gettimeofday ();;

let candle_matan_genuine_source_id = "prep-TSKAJXY-GXSABWC DIV";;
let candle_matan_genuine_target =
  candle_nl_matan_target candle_matan_genuine_source_id;;
let candle_matan_genuine_variables,
    candle_matan_genuine_bound_terms,
    candle_matan_genuine_formula =
  candle_nl_matan_target_parts candle_matan_genuine_target;;
let candle_matan_genuine_expanded =
  candle_nl_matan_expand candle_matan_genuine_formula;;
let candle_matan_genuine_arguments =
  candle_nl_matan_subterms candle_matan_genuine_expanded;;

if length candle_matan_genuine_variables <> 6 ||
   length candle_matan_genuine_bound_terms <> 6 ||
   length candle_matan_genuine_arguments <> 12 then
  failwith "genuine matan reifier: authenticated source shape drift";;

let candle_matan_genuine_exact_bound tm =
  let expanded = rand (concl (REWRITE_CONV candle_nl_matan_defs tm)) in
  let lower,upper = candle_nl_matan_interval_eval [] expanded in
  if not (Num.eq_num lower upper) then
    failwith "genuine matan reifier: source bound is not exact";
  lower;;

let candle_matan_genuine_boxes =
  mk_list
    (map
      (fun (lower,upper) ->
        mk_pair
          (candle_q_term (candle_matan_genuine_exact_bound lower),
           candle_q_term (candle_matan_genuine_exact_bound upper)))
      candle_matan_genuine_bound_terms,
     candle_q_interval_type);;

let candle_matan_genuine_boxes_encoded =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
        (mk_comb (`candle_cv_q_interval_list`,candle_matan_genuine_boxes))));;

let candle_matan_genuine_no_sqrt tm =
  failwith
    ("genuine matan reifier: unexpected square root in selected argument: " ^
     string_of_term tm);;

let candle_matan_genuine_source_terms =
  map
    (fun index ->
      mk_comb
        (`matan:real->real`,List.nth candle_matan_genuine_arguments index))
    [4;6];;

let candle_matan_genuine_reified =
  map
    (candle_analytic_reify_real_expression
      candle_matan_genuine_no_sqrt candle_matan_genuine_variables)
    candle_matan_genuine_source_terms;;

let candle_matan_genuine_encoding_rewrites =
 [candle_analytic_compile_def; candle_poly_compile_def; APPEND;
  candle_cv_analytic_instruction_list_def;
  candle_cv_analytic_instruction_def;
  candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
  candle_analytic_sqrt_interval_def;
  candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
  FST; SND];;

let candle_matan_genuine_program ast =
  rand
    (concl
      (REWRITE_CONV candle_matan_genuine_encoding_rewrites
        (mk_comb
          (`candle_cv_analytic_instruction_list`,
           mk_comb (`candle_analytic_compile`,ast)))));;

let candle_matan_genuine_compute (ast,source_th) =
  let program = candle_matan_genuine_program ast in
  let result =
    Kernel.compute
      (COMPUTE_INIT_THMS,candle_cv_q_dim_analytic_program_compute_eqs)
      (list_mk_comb
        (`candle_cv_q_dim_analytic_program`,
         [candle_matan_genuine_boxes_encoded;program])) in
  let representation =
    REWRITE_RULE
      (candle_matan_genuine_encoding_rewrites @
       [candle_cv_q_interval_list_def])
      (SPECL [ast;candle_matan_genuine_boxes]
        candle_cv_q_dim_analytic_compile_program_correct) in
  let data = TRANS (SYM representation) result in
  ast,source_th,program,result,representation,data;;

let candle_matan_genuine_results =
  map candle_matan_genuine_compute candle_matan_genuine_reified;;

let candle_matan_genuine_bool_decision = prove
 (`!p. ((if p then 1 else 0) = 1) <=> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_matan_genuine_domain (_,_,_,_,_,data) =
  let decoded =
    REWRITE_RULE
      [candle_cv_q_dim_analytic_result_encode_def;
       candle_cv_q_dim_analytic_result_make_def; candle_cv_bool_def;
       candle_cv_q_dim_jet_encode_def; candle_cv_q_dim_jet_make_def;
       candle_cv_q_interval_matrix_def; candle_cv_q_interval_list_def;
       candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
       candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_def; candle_q_dim_jet_hessian_def;
       ARITH_RULE `SUC 0 = 1`; injectivity "cval"; FST; SND]
      data in
  REWRITE_RULE[candle_matan_genuine_bool_decision] (CONJUNCT1 decoded);;

let candle_matan_genuine_domains =
  map candle_matan_genuine_domain candle_matan_genuine_results;;

let candle_matan_genuine_instruction_counts =
  map
    (fun (_,_,program,_,_,_) ->
      let instructions =
        let rec count tm =
          if aconv tm `Cexp_num 0` then 0
          else
            let operator,tail = dest_comb tm in
            let pair_operator,_ = dest_comb operator in
            if not (aconv pair_operator `Cexp_pair`) then
              failwith "genuine matan reifier: malformed encoded program";
            1 + count tail in
        count program in
      instructions)
    candle_matan_genuine_results;;

if length candle_matan_genuine_instruction_counts <> 2 ||
   not (List.for_all (fun count -> 2 < count)
         candle_matan_genuine_instruction_counts) then
  failwith "genuine matan reifier: instruction-count drift";;

if not
    (List.for_all
      (fun (_,source_th,_,result,representation,data) ->
        hyp source_th = [] && hyp result = [] &&
        hyp representation = [] && hyp data = [])
      candle_matan_genuine_results) ||
   not (List.for_all (fun th -> hyp th = []) candle_matan_genuine_domains) then
  failwith "genuine matan reifier: retained theorem assumptions";;

let candle_matan_genuine_axioms_after = axioms ();;
if length candle_matan_genuine_axioms_after <>
     length candle_matan_genuine_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_matan_genuine_axioms_before)
       candle_matan_genuine_axioms_after) then
  failwith "genuine matan reifier: changed the global axiom set";;

let candle_matan_genuine_seconds =
  Unix.gettimeofday () -. candle_matan_genuine_started;;

let candle_matan_genuine_instruction_count_string =
  String.concat ","
    (map string_of_int candle_matan_genuine_instruction_counts);;

let _ = print_endline
  ("CANDLE_CV_ANALYTIC_EXPR_MATAN_GENUINE_REIFY_RESULT source_id=" ^
   candle_matan_genuine_source_id ^
   " expressions=2 dimensions=6 accepted=2 instructions=" ^
   candle_matan_genuine_instruction_count_string ^ " seconds=" ^
   string_of_float candle_matan_genuine_seconds);;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_MATAN_GENUINE_REIFY_OK";;

end;;
