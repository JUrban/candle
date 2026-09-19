(* ========================================================================== *)
(* Proof-producing compute prototype for the Flyspeck hypermap list layer.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE: load this file only after candle/compute.ml and *)
(* formal_lp/hypermap/computations/list_hypermap_computations.hl.             *)
(*                                                                            *)
(* The ML code below is outside the trusted kernel.  The exported conversion  *)
(* returns an ordinary HOL theorem through three checked links: a proved      *)
(* representation theorem, Kernel.compute, and a proved decoding theorem.     *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_lists_core.ml";;

module Flyspeck_cv_compute = struct

open List_hypermap_computations;;
open Candle_cv_flyspeck_lists_core;;

(* -------------------------------------------------------------------------- *)
(* Correctness against the actual Flyspeck definitions.                       *)
(* -------------------------------------------------------------------------- *)

let candle_cv_list_pairs_aux_correct = prove
 (`!l hd.
     candle_cv_list_pairs_aux (Cexp_num hd) (candle_cv_num_list l) =
     candle_cv_num_pair_list (list_pairs2 l hd)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_num_list_def; candle_cv_list_pairs_aux_def;
                list_pairs2; candle_cv_num_pair_list_def];
    ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC (ISPEC `t:num list` list_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[candle_cv_num_list_def; candle_cv_list_pairs_aux_def;
                  list_pairs2; candle_cv_num_pair_list_def;
                  cexp_if_def; cexp_fst_def; cexp_ispair_def] THEN
  ONCE_REWRITE_TAC[GSYM candle_cv_list_pairs_aux_def] THEN
  ONCE_REWRITE_TAC[GSYM candle_cv_num_list_def] THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_list_pairs_correct = prove
 (`!l:num list.
     candle_cv_list_pairs (candle_cv_num_list l) =
     candle_cv_num_pair_list (list_pairs l)`,
  GEN_TAC THEN
  DISJ_CASES_TAC (ISPEC `l:num list` list_CASES) THENL
   [ASM_REWRITE_TAC[candle_cv_num_list_def; candle_cv_list_pairs_def;
                    candle_cv_num_pair_list_def; list_pairs_eq_list_pairs2;
                    list_pairs2; cexp_if_def; cexp_ispair_def];
    FIRST_X_ASSUM (CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[candle_cv_num_list_def; candle_cv_list_pairs_def;
                list_pairs_eq_list_pairs2; HD; cexp_if_def;
                cexp_fst_def; cexp_ispair_def;
                candle_cv_list_pairs_aux_correct] THEN
    ONCE_REWRITE_TAC[GSYM candle_cv_num_list_def] THEN
    REWRITE_TAC[candle_cv_list_pairs_aux_correct]]);;

let candle_cv_list_of_faces_correct = prove
 (`!l:(num list)list.
     candle_cv_list_of_faces (candle_cv_num_lists l) =
     candle_cv_num_pair_lists (list_of_faces l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_num_lists_def; candle_cv_num_pair_lists_def;
                  candle_cv_list_of_faces_def; list_of_faces; MAP;
                  candle_cv_list_pairs_correct]);;

(* -------------------------------------------------------------------------- *)
(* Conversion with the same theorem interface as eval_list_of_faces.          *)
(* -------------------------------------------------------------------------- *)

let candle_cv_num_lists_conv tm =
  REWRITE_CONV[candle_cv_num_lists_def; candle_cv_num_list_def] tm;;

let candle_cv_list_of_faces_conv tm =
  let input_rep_tm = mk_comb (`candle_cv_num_lists`,tm) in
  let input_rep_th = candle_cv_num_lists_conv input_rep_tm in
  let input_cv_tm = rand (concl input_rep_th) in
  let compute_tm = mk_comb (`candle_cv_list_of_faces`,input_cv_tm) in
  let compute_th = compute candle_cv_list_of_faces_compute_eqs compute_tm in
  let correctness_th = SPEC tm candle_cv_list_of_faces_correct in
  let lhs_bridge_th = AP_TERM `candle_cv_list_of_faces` input_rep_th in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS lhs_bridge_th compute_th) in
  let decoded_result_th =
    AP_TERM `candle_cv_num_pair_lists_decode` encoded_result_th in
  REWRITE_RULE[candle_cv_num_pair_lists_roundtrip;
               candle_cv_num_pair_lists_decode_def;
               candle_cv_num_pair_list_decode_def;
               candle_cv_num_pair_decode_def;
               candle_cv_num_decode_def] decoded_result_th;;

end;;
