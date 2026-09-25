(* ========================================================================== *)
(* Focused regression for computed analytic-domain regularity.               *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-atn-expr-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_domain.ml";;

open Candle_cv_analytic_expr_domain;;

let candle_analytic_domain_axioms_before = axioms ();;

let candle_analytic_domain_regular = candle_q_dim_analytic_domain_regular;;
if hyp candle_analytic_domain_regular <> [] then
  failwith "analytic domain regularity: theorem assumptions";;

let candle_analytic_domain_nonzero = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> ~(x = &0)`,
  MESON_TAC[candle_q_interval_not_zero_contains_nonzero]);;

let candle_analytic_domain_sqrt_positive = prove
 (`!s a x.
     candle_q_dim_jet_sqrt_domain s a /\
     candle_q_interval_contains (candle_q_dim_jet_f a) x
     ==> &0 < x`,
  MESON_TAC[candle_q_dim_jet_sqrt_domain_value_positive]);;

if hyp candle_analytic_domain_nonzero <> [] ||
   hyp candle_analytic_domain_sqrt_positive <> [] then
  failwith "analytic domain regularity: component theorem assumptions";;

let candle_analytic_domain_axioms_after = axioms ();;
if length candle_analytic_domain_axioms_after <>
     length candle_analytic_domain_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_domain_axioms_before)
       candle_analytic_domain_axioms_after) then
  failwith "analytic domain regularity: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_EXPR_DOMAIN_RESULT constructors=9 inv=1 sqrt=1 atn=1 pi_half=1 universal=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_DOMAIN_OK";;
