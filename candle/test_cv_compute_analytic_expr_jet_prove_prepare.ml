(* ========================================================================== *)
(* Authenticated analytic preparation for a six-dimensional source.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

open Candle_cv_analytic_expr_jet_prove;;

let candle_analytic_prepare_axioms_before = axioms ();;

let candle_analytic_prepare_function =
 `\p:real^6. pi * inv (&2) + atn (p$1)`;;

let candle_analytic_prepare_result =
  candle_q_dim_analytic_jet_prepare_six
    candle_analytic_prepare_function;;

let candle_analytic_prepare_expected_expression =
 `Candle_analytic_add Candle_analytic_pi_half
    (Candle_analytic_atn
      (Candle_analytic_poly (Candle_poly_var 0)))`;;

if not
    (aconv candle_analytic_prepare_result.expression_term
      candle_analytic_prepare_expected_expression) ||
   length (dest_list candle_analytic_prepare_result.program_term) <> 4 ||
   hyp candle_analytic_prepare_result.valid_theorem <> [] ||
   hyp candle_analytic_prepare_result.source_theorem <> [] ||
   hyp candle_analytic_prepare_result.compile_theorem <> [] ||
   hyp candle_analytic_prepare_result.program_representation <> [] ||
   not
     (aconv (concl candle_analytic_prepare_result.source_theorem)
       `candle_analytic_denote_dim
          (Candle_analytic_add Candle_analytic_pi_half
            (Candle_analytic_atn
              (Candle_analytic_poly (Candle_poly_var 0))))
          (p:real^6) =
        pi * inv (&2) + atn (p$1)`) then
  failwith "analytic shared-jet preparation mismatch";;

let candle_analytic_prepare_axioms_after = axioms ();;
if length candle_analytic_prepare_axioms_after <>
     length candle_analytic_prepare_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_analytic_prepare_axioms_before)
       candle_analytic_prepare_axioms_after) then
  failwith "analytic shared-jet preparation changed the global axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_JET_PROVE_PREPARE_RESULT source=pi_half_plus_atn dimensions=6 instructions=4 authenticated=1";;
print_endline "CANDLE_CV_ANALYTIC_JET_PROVE_PREPARE_OK";;
