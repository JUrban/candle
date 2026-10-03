needs "candle/cv_compute_analytic_expr_taylor_model_program_nonlinear_shared.ml";;

open Candle_cv_analytic_expr_taylor_model_program_nonlinear_shared;;

let candle_cv_nonlinear_shared_axioms_before = axioms ();;

let candle_cv_nonlinear_shared_exact_theorems =
  [candle_cv_q_dim_analytic_first_jet_inv_shared_exact;
   candle_cv_q_dim_jet_inv_with_shared_exact;
   candle_cv_q_dim_jet_inv_shared_exact;
   candle_cv_q_dim_taylor_model_result_inv_shared_exact;
   candle_cv_q_dim_jet_sqrt_with_shared_exact;
   candle_cv_q_dim_taylor_model_result_sqrt_shared_exact;
   candle_cv_q_dim_jet_atn_with_shared_exact;
   candle_cv_q_dim_jet_atn_shared_exact;
   candle_cv_q_dim_taylor_model_result_atn_shared_exact;
   candle_cv_fsa_item_sqrt_shared_exact;
   candle_cv_fsa_item_inv_shared_exact;
   candle_cv_fsa_item_atn_shared_exact;
   candle_cv_fso_program_step_nonlinear_shared_exact];;

let candle_cv_nonlinear_shared_axioms_after = axioms ();;

if not (List.for_all (fun theorem -> hyp theorem = [])
          candle_cv_nonlinear_shared_exact_theorems) ||
   length candle_cv_nonlinear_shared_axioms_after <>
     length candle_cv_nonlinear_shared_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_cv_nonlinear_shared_axioms_before)
       candle_cv_nonlinear_shared_axioms_after)
then failwith "nonlinear shared exact theorem validation failed";;

print_endline
  "CANDLE_CV_NONLINEAR_SHARED_EXACT_OK DEVELOPMENT_NON_RELEASE theorems=13 assumptions=0 axiom_growth=0";;
