(* ========================================================================== *)
(* Genuine case-10173: authenticated root cell to the original Flyspeck goal. *)
(*                                                                            *)
(* This is the final, computation-independent semantic adapter.  The fast or  *)
(* generic checker need only supply the single authenticated root cell fact;  *)
(* the exact source equality and the ordinary Flyspeck normalization then     *)
(* recover the literal [ineqm] theorem.                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_source_bridge.ml";;

module Candle_cv_analytic_expr_case10173_historical_authenticated_original_bridge = struct

open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_source_bridge;;

let candle_case10173_hist_original_sorted_variable_names =
  map (fst o dest_var)
    (M_taylor.dest_vector candle_case10173_analytic_variable_vector);;

let candle_case10173_hist_original_lo,
    candle_case10173_hist_original_hi =
  candle_case10173_analytic_bounds;;

let candle_case10173_hist_original_named_bounds =
  zip candle_case10173_analytic_variable_names
    (zip
      (dest_list candle_case10173_hist_original_lo)
      (dest_list candle_case10173_hist_original_hi));;

let candle_case10173_hist_original_ordered_bounds =
  itlist
    (fun name result ->
      assoc name candle_case10173_hist_original_named_bounds :: result)
    candle_case10173_hist_original_sorted_variable_names [];;

let candle_case10173_hist_original_xx0,
    candle_case10173_hist_original_zz0 =
  unzip candle_case10173_hist_original_ordered_bounds;;

let candle_case10173_hist_original_xx =
  Misc_vars.mk_real_list candle_case10173_hist_original_xx0
and candle_case10173_hist_original_zz =
  Misc_vars.mk_real_list candle_case10173_hist_original_zz0;;

let candle_case10173_hist_original_domain_subset,
    (candle_case10173_hist_original_xx1,
     candle_case10173_hist_original_zz1) =
  M_verifier_main.mk_float_domain 6
    (candle_case10173_hist_original_xx,
     candle_case10173_hist_original_zz);;

let candle_case10173_hist_original_root_domain =
  M_taylor.mk_m_center_domain 6 6
    candle_case10173_hist_original_xx1
    candle_case10173_hist_original_zz1;;

let candle_case10173_hist_original_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_case10173_hist_original_root_domain);;

let candle_case10173_hist_original_domain_def =
  new_definition
    (mk_eq
      (`candle_case10173_hist_original_domain:real^6#real^6`,
       candle_case10173_hist_original_domain));;

let candle_case10173_hist_authenticated_original_cell_goal =
  list_mk_comb
    (`m_cell_pass:(real^6->real)->(real^6#real^6)->bool`,
     [`(candle_analytic_denote_dim
          candle_case10173_hist_authenticated_source):real^6->real`;
      `candle_case10173_hist_original_domain:real^6#real^6`]);;

let candle_case10173_hist_authenticated_original_bridge =
  let authenticated_cell =
    ASSUME candle_case10173_hist_authenticated_original_cell_goal in
  let literal_cell =
    REWRITE_RULE
      [candle_case10173_hist_authenticated_source_function;
       candle_case10173_hist_original_domain_def]
      authenticated_cell in
  let expanded_general =
    M_verifier_main.normalize_result true
      candle_case10173_analytic_variable_vector
      candle_case10173_analytic_standard
      candle_case10173_hist_original_domain_subset literal_cell in
  let converted = SPEC_ALL expanded_general in
  let case_theorem =
    REWRITE_RULE [GSYM candle_case10173_analytic_expansion] converted in
  let theorem =
    (SPEC_ALL o
     REWRITE_RULE [GSYM candle_case10173_analytic_reconstruction])
      case_theorem in
  theorem;;

let candle_case10173_hist_authenticated_original_handoff cell_theorem =
  if hyp cell_theorem <> [] ||
     not
       (aconv
         (concl cell_theorem)
         candle_case10173_hist_authenticated_original_cell_goal) then
    failwith "case10173 authenticated original bridge: root theorem mismatch";
  let theorem =
    MP candle_case10173_hist_authenticated_original_bridge cell_theorem in
  if hyp theorem <> [] ||
     not (aconv (concl theorem) candle_case10173_analytic_target) then
    failwith "case10173 authenticated original bridge: final theorem mismatch";
  theorem;;

if length candle_case10173_hist_original_sorted_variable_names <> 6 ||
   hyp candle_case10173_hist_original_domain_subset <> [] ||
   hyp candle_case10173_hist_original_root_domain <> [] ||
   hyp candle_case10173_hist_authenticated_original_bridge <> [] then
  failwith "case10173 authenticated original bridge: theorem assumptions";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_ORIGINAL_BRIDGE_OK DEVELOPMENT_NON_RELEASE";;

end;;
