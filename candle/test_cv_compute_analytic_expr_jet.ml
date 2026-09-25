(* ========================================================================== *)
(* Focused universal nested-analytic-jet theorem regression.                 *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-atn-expr-v1"] @ !load_path;;

needs "candle/cv_compute_analytic_expr_jet.ml";;

open Candle_cv_analytic_expr_jet;;

let candle_analytic_expr_jet_axioms_before = axioms ();;

let candle_analytic_expr_jet_nested =
 `Candle_analytic_add Candle_analytic_pi_half
    (Candle_analytic_atn
      (Candle_analytic_sqrt 2 0 0 2 0 0
        (Candle_analytic_add
          (Candle_analytic_inv
            (Candle_analytic_poly
              (Candle_poly_add
                (Candle_poly_const 1 0 0) (Candle_poly_var 0))))
          (Candle_analytic_poly (Candle_poly_const 3 0 0)))))`;;

let candle_analytic_expr_jet_shape =
  SPECL [candle_analytic_expr_jet_nested;
         `[(((((0,0),0),((0,0),0))):
              ((num#num)#num)#((num#num)#num))]`]
    candle_q_dim_analytic_jet_shape;;

if hyp candle_analytic_expr_jet_shape <> [] then
  failwith "nested analytic jet: shape theorem assumptions";;

let candle_analytic_expr_jet_sound = candle_q_dim_analytic_jet_sound;;
if hyp candle_analytic_expr_jet_sound <> [] then
  failwith "nested analytic jet: soundness theorem assumptions";;

let candle_analytic_expr_jet_axioms_after = axioms ();;
if length candle_analytic_expr_jet_axioms_after <>
     length candle_analytic_expr_jet_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_expr_jet_axioms_before)
       candle_analytic_expr_jet_axioms_after) then
  failwith "nested analytic jet: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_ANALYTIC_EXPR_JET_RESULT constructors=9 nested_depth=6 universal_shape=1 universal_sound=1";;
let _ = print_endline "CANDLE_CV_ANALYTIC_EXPR_JET_OK";;
