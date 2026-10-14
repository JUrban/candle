(* ========================================================================== *)
(* Genuine case-10173: authenticated historical AST to original function.   *)
(*                                                                            *)
(* Reification supplies the general semantic theorem.  This unit proves once *)
(* that its AST is exactly the source AST consumed by the historical checker; *)
(* no per-leaf calculus or source reconstruction is performed.               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_fixture.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_source_contract.ml";;

module Candle_cv_analytic_expr_case10173_historical_authenticated_source_bridge = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_jet_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_dihedral_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_contract;;

let candle_case10173_hist_bridge_vector,_ =
  dest_abs candle_case10173_analytic_function;;

let candle_case10173_hist_bridge_variables =
  Candle_cv_polynomial_expr_flyspeck_reify.candle_poly_vector_components
    candle_case10173_hist_bridge_vector 6;;

let candle_case10173_hist_bridge_variable_sqrts =
  map (fun variable -> mk_comb (`sqrt:real->real`,variable))
    candle_case10173_hist_bridge_variables;;

let candle_case10173_hist_bridge_variable_sqrt_count = ref 0;;
let candle_case10173_hist_bridge_nested_sqrt_count = ref 0;;

let candle_case10173_hist_bridge_sqrt_interval square_root =
  if exists (aconv square_root)
       candle_case10173_hist_bridge_variable_sqrts then begin
    candle_case10173_hist_bridge_variable_sqrt_count :=
      !candle_case10173_hist_bridge_variable_sqrt_count + 1;
    `((((2,0),0),((3,0),0)):
      ((num#num)#num)#((num#num)#num))`
  end else begin
    candle_case10173_hist_bridge_nested_sqrt_count :=
      !candle_case10173_hist_bridge_nested_sqrt_count + 1;
    `((((50,0),0),((100,0),0)):
      ((num#num)#num)#((num#num)#num))`
  end;;

let candle_case10173_hist_bridge_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_case10173_hist_bridge_sqrt_interval
    candle_case10173_analytic_function;;

if !candle_case10173_hist_bridge_variable_sqrt_count <> 6 ||
   !candle_case10173_hist_bridge_nested_sqrt_count <> 1 ||
   length (dest_list candle_case10173_hist_bridge_prepared.program_term) <> 54 ||
   hyp candle_case10173_hist_bridge_prepared.valid_theorem <> [] ||
   hyp candle_case10173_hist_bridge_prepared.source_theorem <> [] then
  failwith "case10173 historical source bridge: reification drift";;

let candle_case10173_hist_authenticated_source_expansion =
  REWRITE_CONV
    [candle_case10173_hist_authenticated_source_def;
     candle_case10173_hist_source_context_def;
     candle_case10173_hist_source_factor_def;
     candle_case10173_hist_context_box_expr_def;
     candle_case10173_hist_source_dihedral_expr_def;
     candle_case10173_hist_source_numerator_expr_def;
     candle_case10173_hist_source_radical_expr_def;
     candle_case10173_hist_source_radical_poly_def;
     candle_case10173_hist_delta_x4_expr_def;
     candle_case10173_hist_delta_x4_poly_def;
     candle_case10173_hist_delta_expr_def;
     candle_case10173_hist_delta_poly_def;
     candle_case10173_hist_four_x0_expr_def;
     candle_case10173_hist_four_x0_poly_def;
     FST;SND]
    `candle_case10173_hist_authenticated_source`;;

if not
    (aconv
      (rand (concl candle_case10173_hist_authenticated_source_expansion))
      candle_case10173_hist_bridge_prepared.expression_term) then
  failwith "case10173 historical source bridge: AST identity mismatch";;

let candle_case10173_hist_authenticated_source_theorem =
  REWRITE_RULE
    [GSYM candle_case10173_hist_authenticated_source_expansion]
    candle_case10173_hist_bridge_prepared.source_theorem;;

let candle_case10173_hist_authenticated_source_function =
  prove
    (mk_eq
      (`(candle_analytic_denote_dim
           candle_case10173_hist_authenticated_source):real^6->real`,
       candle_case10173_analytic_function),
     REWRITE_TAC
       [FUN_EQ_THM;
        candle_case10173_hist_authenticated_source_theorem]);;

if hyp candle_case10173_hist_authenticated_source_expansion <> [] ||
   hyp candle_case10173_hist_authenticated_source_theorem <> [] ||
   hyp candle_case10173_hist_authenticated_source_function <> [] then
  failwith "case10173 historical source bridge: theorem assumptions";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_SOURCE_BRIDGE_OK DEVELOPMENT_NON_RELEASE";;

end;;
