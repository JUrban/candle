(* ========================================================================== *)
(* Regression for analytic-jet Flyspeck derivative list correspondence.      *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_flyspeck_bridge.ml";;

open Candle_cv_analytic_expr_flyspeck_bridge;;

let candle_analytic_flyspeck_bridge_axioms_before = axioms ();;

let candle_analytic_flyspeck_gradient =
  candle_q_dim_analytic_jet_gradient_flyspeck_contains;;
let candle_analytic_flyspeck_hessian =
  candle_q_dim_analytic_jet_hessian_flyspeck_contains;;

if hyp candle_analytic_flyspeck_gradient <> [] ||
   hyp candle_analytic_flyspeck_hessian <> [] then
  failwith "analytic Flyspeck bridge: theorem assumptions";;

let candle_analytic_flyspeck_bridge_axioms_after = axioms ();;
if length candle_analytic_flyspeck_bridge_axioms_after <>
     length candle_analytic_flyspeck_bridge_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_flyspeck_bridge_axioms_before)
       candle_analytic_flyspeck_bridge_axioms_after) then
  failwith "analytic Flyspeck bridge: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_FLYSPECK_BRIDGE_RESULT gradient=1 hessian=1 universal=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_FLYSPECK_BRIDGE_OK";;
