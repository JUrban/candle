needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_invariant;;

let candle_fixed_outer_invariant_axioms_before = axioms ();;

if hyp candle_fs_result_analytic_proxy_target_components <> [] ||
   hyp candle_fs_result_mul_analytic_hessian_contains <> [] ||
   hyp candle_fs_analytic_hessian_flyspeck_contains <> [] then
  failwith "fixed outer invariant: unexpected theorem hypotheses";;

let candle_fixed_outer_invariant_axioms_after = axioms ();;

if length candle_fixed_outer_invariant_axioms_after <>
     length candle_fixed_outer_invariant_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_fixed_outer_invariant_axioms_before)
       candle_fixed_outer_invariant_axioms_after) then
  failwith "fixed outer invariant: axiom set changed";;

print_endline
  "CANDLE_CV_FIXED_OUTER_INVARIANT_OK DEVELOPMENT_NON_RELEASE";;
