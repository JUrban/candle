(* ========================================================================== *)
(* One genuine composite [matan] checker flag, retained for theorem handoff. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The expensive exact center/box evaluation is  *)
(* performed once before a DMTCP editing checkpoint.  Subsequent proof-only  *)
(* adapters consume the retained theorem without repeating the calculation.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_sound.ml";;
needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_center_prepare.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_compute;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_sound;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_center_prepare;;

module Test_cv_compute_analytic_expr_matan_genuine_root_dual_check_prepare = struct

let axioms_before = axioms ();;

let q_interval lower upper =
  mk_pair
    (candle_q_term (rat_of_term lower),
     candle_q_term (rat_of_term upper));;
let boxes =
  mk_list (map2 q_interval lower upper,candle_q_interval_type);;
let boxes_representation =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;
let boxes_representation_term = rand (concl boxes_representation);;
let center_program_representation_term =
  rand (concl center_program_representation);;
let box_program_representation_term =
  rand (concl tight_program_representation);;

let compute_term =
  mk_comb
    (`Cexp_fst`,
     list_mk_comb
       (`candle_cv_matan_fs_taylor_dual_check`,
        [center_program_representation_term;
         box_program_representation_term;
         boxes_representation_term]));;

let started = Unix.gettimeofday ();;
let compute_theorem =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_matan_fs_taylor_handoff_compute_eqs)
    compute_term;;
let compute_seconds = Unix.gettimeofday () -. started;;

if hyp compute_theorem <> [] ||
   not (aconv (rand (concl compute_theorem)) `Cexp_num 1`) then
  failwith "genuine matan dual check: composite checker rejected";;

let axioms_after = axioms ();;
if length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan dual check: changed the global axiom set";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ROOT_DUAL_CHECK_PREPARE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " center_instructions=" ^ string_of_int center_instruction_count ^
   " box_instructions=" ^ string_of_int tight_instruction_count ^
   " verdict=accept" ^
   " compute_seconds=" ^ string_of_float compute_seconds ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_GENUINE_ROOT_DUAL_CHECK_PREPARE_OK";;

end;;
