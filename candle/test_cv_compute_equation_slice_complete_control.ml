(* Setup/compile discriminator for the complete nonlinear equation bundle. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound.ml";;
needs "candle/cv_compute_equation_slice.ml";;

module Test_cv_compute_equation_slice_complete_control = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound;;
open Candle_cv_compute_equation_slice;;

let candle_cv_compute_slice_control_profile phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=compute-equation-slice-control" ^
     " phase=" ^ phase ^ "-" ^ event);;

let candle_cv_compute_slice_control_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
     [`Cexp_num 0`;`Cexp_num 6`;`Cexp_num 0`;`Cexp_num 0`]);;

let _ =
  let axioms_before = axioms () in
  let raw_equations = candle_cv_fso_variable_raw_compute_eqs in
  let topology_equations =
    candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs in
  let complete_equations =
    candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs in
  let sliced_equations =
    candle_cv_compute_equation_slice
      complete_equations candle_cv_compute_slice_control_call in
  print_endline
    ("CANDLE_CV_COMPUTE_EQUATION_SLICE_COUNTS" ^
     " raw=" ^ string_of_int (length raw_equations) ^
     " topology=" ^ string_of_int (length topology_equations) ^
     " complete=" ^ string_of_int (length complete_equations) ^
     " sliced=" ^ string_of_int (length sliced_equations));
  candle_cv_compute_slice_control_profile "raw-empty-control" "begin";
  let raw_empty =
    Kernel.compute (COMPUTE_INIT_THMS,raw_equations) `Cexp_num 0` in
  candle_cv_compute_slice_control_profile "raw-empty-control" "end";
  candle_cv_compute_slice_control_profile "complete-empty-control" "begin";
  let complete_empty =
    Kernel.compute (COMPUTE_INIT_THMS,complete_equations) `Cexp_num 0` in
  candle_cv_compute_slice_control_profile "complete-empty-control" "end";
  candle_cv_compute_slice_control_profile "complete-empty-call" "begin";
  let complete_call =
    Kernel.compute
      (COMPUTE_INIT_THMS,complete_equations)
      candle_cv_compute_slice_control_call in
  candle_cv_compute_slice_control_profile "complete-empty-call" "end";
  candle_cv_compute_slice_control_profile "sliced-empty-call" "begin";
  let sliced_call =
    Kernel.compute
      (COMPUTE_INIT_THMS,sliced_equations)
      candle_cv_compute_slice_control_call in
  candle_cv_compute_slice_control_profile "sliced-empty-call" "end";
  let axioms_after = axioms () in
  if hyp raw_empty <> [] || hyp complete_empty <> [] ||
     hyp complete_call <> [] || hyp sliced_call <> [] ||
     not (aconv (rand (concl raw_empty)) `Cexp_num 0`) ||
     not (aconv (rand (concl complete_empty)) `Cexp_num 0`) ||
     not (aconv (rand (concl complete_call)) (rand (concl sliced_call))) ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "compute equation slice control: validation failed";
  print_endline
    "CANDLE_CV_COMPUTE_EQUATION_SLICE_CONTROL_OK DEVELOPMENT_NON_RELEASE";;

end;;
