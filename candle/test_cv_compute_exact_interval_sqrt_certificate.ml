(* ========================================================================== *)
(* Focused reflected square-root interval-certificate regression.            *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_exact_interval_sqrt_certificate.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_linear_combination_realize;;

let candle_q_interval_sqrt_test_axioms_before = axioms ();;

let candle_q_interval_sqrt_input_exact =
  `(((((4,0),0):(num#num)#num),(((9,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_sqrt_output_exact =
  `(((((2,0),0):(num#num)#num),(((3,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_sqrt_input_loose =
  `(((((2,0),0):(num#num)#num),(((4,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_sqrt_output_loose =
  `(((((1,0),0):(num#num)#num),(((2,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_sqrt_output_bad =
  `(((((3,0),1):(num#num)#num),(((2,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_sqrt_input_negative =
  `(((((0,1),0):(num#num)#num),(((4,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_sqrt_compute input output =
  let input_representation =
    REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
                 Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                 FST; SND]
      (mk_comb (`candle_cv_q_interval`,input)) in
  let output_representation =
    REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
                 Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                 FST; SND]
      (mk_comb (`candle_cv_q_interval`,output)) in
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_interval_sqrt_certificate_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_interval_sqrt_certificate`,
       [rand (concl input_representation);
        rand (concl output_representation)]));;

let candle_q_interval_sqrt_exact_computed =
  candle_q_interval_sqrt_compute
    candle_q_interval_sqrt_input_exact candle_q_interval_sqrt_output_exact;;

let candle_q_interval_sqrt_loose_computed =
  candle_q_interval_sqrt_compute
    candle_q_interval_sqrt_input_loose candle_q_interval_sqrt_output_loose;;

let candle_q_interval_sqrt_bad_computed =
  candle_q_interval_sqrt_compute
    candle_q_interval_sqrt_input_loose candle_q_interval_sqrt_output_bad;;

let candle_q_interval_sqrt_negative_computed =
  candle_q_interval_sqrt_compute
    candle_q_interval_sqrt_input_negative candle_q_interval_sqrt_output_loose;;

if not (aconv (rand (concl candle_q_interval_sqrt_exact_computed))
              `Cexp_num 1`) ||
   not (aconv (rand (concl candle_q_interval_sqrt_loose_computed))
              `Cexp_num 1`) ||
   not (aconv (rand (concl candle_q_interval_sqrt_bad_computed))
              `Cexp_num 0`) ||
   not (aconv (rand (concl candle_q_interval_sqrt_negative_computed))
              `Cexp_num 0`) then
  failwith "reflected interval sqrt certificate: computed result mismatch";;

let candle_q_interval_sqrt_exact_sound =
  let certificate =
    prove
      (`candle_q_interval_sqrt_certificate
          (((((4,0),0),((9,0),0)):
             ((num#num)#num)#((num#num)#num)))
          (((((2,0),0),((3,0),0)):
             ((num#num)#num)#((num#num)#num)))`,
       REWRITE_TAC[candle_q_interval_sqrt_certificate_def; candle_q_le_def;
                   candle_q_zero_def; candle_q_mul_def;
                   candle_q_den_def; candle_q_den_product_pred_def;
                   candle_q_zmul_def; FST; SND] THEN
       CONV_TAC NUM_REDUCE_CONV) in
  let contains =
    prove
      (`candle_q_interval_contains
          (((((4,0),0),((9,0),0)):
             ((num#num)#num)#((num#num)#num))) (&6)`,
       REWRITE_TAC[candle_q_interval_contains_def; candle_q_real_def;
                   candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV) in
  MATCH_MP
    (SPECL
      [candle_q_interval_sqrt_input_exact;
       candle_q_interval_sqrt_output_exact; `&6:real`]
      candle_q_interval_sqrt_certificate_sound)
    (CONJ certificate contains);;

if hyp candle_q_interval_sqrt_exact_computed <> [] ||
   hyp candle_q_interval_sqrt_loose_computed <> [] ||
   hyp candle_q_interval_sqrt_bad_computed <> [] ||
   hyp candle_q_interval_sqrt_negative_computed <> [] ||
   hyp candle_q_interval_sqrt_exact_sound <> [] then
  failwith "reflected interval sqrt certificate: proof assumptions";;

let candle_q_interval_sqrt_test_axioms_after = axioms ();;
if length candle_q_interval_sqrt_test_axioms_after <>
     length candle_q_interval_sqrt_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_interval_sqrt_test_axioms_before)
       candle_q_interval_sqrt_test_axioms_after) then
  failwith "reflected interval sqrt certificate: changed the global axiom set";;

let _ =
  print_endline
    "CANDLE_CV_EXACT_INTERVAL_SQRT_CERTIFICATE_RESULT certificates=4 accepted=2 rejected=2 sound=1";;
let _ = print_endline "CANDLE_CV_EXACT_INTERVAL_SQRT_CERTIFICATE_OK";;
