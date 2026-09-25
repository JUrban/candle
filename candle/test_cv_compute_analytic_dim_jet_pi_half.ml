(* ========================================================================== *)
(* Focused authenticated pi/2 constant-jet regression.                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_dim_jet_pi_half.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_dim_jet_pi_half;;

let candle_q_dim_jet_pi_half_test_axioms_before = axioms ();;

let candle_q_dim_jet_pi_half_test_boxes =
 `([(((4,0),0),((5,0),0))]:
    (((num#num)#num)#((num#num)#num))list)`;;

let candle_q_dim_jet_pi_half_test_boxes_representation =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
        (mk_comb
          (`candle_cv_q_interval_list`,
           candle_q_dim_jet_pi_half_test_boxes))));;

let candle_q_dim_jet_pi_half_test_started = Unix.gettimeofday ();;

let candle_q_dim_jet_pi_half_test_computed =
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_dim_jet_pi_half_compute_eqs)
    (mk_comb
      (`candle_cv_q_dim_jet_pi_half`,
       candle_q_dim_jet_pi_half_test_boxes_representation));;

let candle_q_dim_jet_pi_half_test_correct =
  REWRITE_RULE
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (SPEC candle_q_dim_jet_pi_half_test_boxes
      candle_cv_q_dim_jet_pi_half_correct);;

let candle_q_dim_jet_pi_half_test_link =
  TRANS (SYM candle_q_dim_jet_pi_half_test_correct)
    candle_q_dim_jet_pi_half_test_computed;;

let candle_q_dim_jet_pi_half_test_sound =
  SPEC candle_q_dim_jet_pi_half_test_boxes
    candle_q_dim_jet_pi_half_components_sound;;

let candle_q_dim_jet_pi_half_test_seconds =
  Unix.gettimeofday () -. candle_q_dim_jet_pi_half_test_started;;

if hyp candle_q_dim_jet_pi_half_test_computed <> [] ||
   hyp candle_q_dim_jet_pi_half_test_link <> [] ||
   hyp candle_q_dim_jet_pi_half_test_sound <> [] then
  failwith "reflected pi/2 jet: proof assumptions";;

let candle_q_dim_jet_pi_half_test_axioms_after = axioms ();;
if length candle_q_dim_jet_pi_half_test_axioms_after <>
     length candle_q_dim_jet_pi_half_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_dim_jet_pi_half_test_axioms_before)
       candle_q_dim_jet_pi_half_test_axioms_after) then
  failwith "reflected pi/2 jet: changed the global axiom set";;

let _ = print_endline
  ("CANDLE_CV_ANALYTIC_DIM_JET_PI_HALF_RESULT dimensions=1 semantic=1 " ^
   "seconds=" ^ string_of_float candle_q_dim_jet_pi_half_test_seconds ^
   " output_md5=" ^
   Digest.to_hex
     (Digest.string (string_of_thm candle_q_dim_jet_pi_half_test_computed)));;
let _ = print_endline "CANDLE_CV_ANALYTIC_DIM_JET_PI_HALF_OK";;
