(* ========================================================================== *)
(* Focused regression for analytic shared-jet Taylor accumulation.           *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_taylor_sound.ml";;

open Candle_cv_analytic_expr_taylor_sound;;

let candle_analytic_taylor_axioms_before = axioms ();;

let candle_analytic_taylor_list_bound =
  candle_q_dim_jet_gradient_list_taylor_sum_bound;;
let candle_analytic_taylor_gradient_bound =
  candle_q_dim_analytic_jet_gradient_taylor_sum_bound;;
let candle_analytic_taylor_hessian_list_bound =
  candle_q_dim_jet_hessian_list_taylor_sum_bound;;
let candle_analytic_taylor_hessian_bound =
  candle_q_dim_analytic_jet_hessian_taylor_sum_bound;;
let candle_analytic_taylor_error =
  candle_q_dim_analytic_jet_m_taylor_error_sound;;
let candle_analytic_diff2_domain =
  candle_q_dim_analytic_diff2_domain;;
let candle_analytic_taylor_upper =
  candle_q_dim_analytic_jet_taylor_upper_sound;;

if hyp candle_analytic_taylor_list_bound <> [] ||
   hyp candle_analytic_taylor_gradient_bound <> [] ||
   hyp candle_analytic_taylor_hessian_list_bound <> [] ||
   hyp candle_analytic_taylor_hessian_bound <> [] ||
   hyp candle_analytic_taylor_error <> [] ||
   hyp candle_analytic_diff2_domain <> [] ||
   hyp candle_analytic_taylor_upper <> [] then
  failwith "analytic Taylor accumulation: theorem assumptions";;

let candle_analytic_taylor_axioms_after = axioms ();;
if length candle_analytic_taylor_axioms_after <>
     length candle_analytic_taylor_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_taylor_axioms_before)
       candle_analytic_taylor_axioms_after) then
  failwith "analytic Taylor accumulation: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_TAYLOR_RESULT gradient_list=1 gradient_bound=1 hessian_list=1 hessian_bound=1 taylor_error=1 diff2_domain=1 upper_sound=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_TAYLOR_OK";;
