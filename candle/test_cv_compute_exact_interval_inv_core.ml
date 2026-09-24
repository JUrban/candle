(* ========================================================================== *)
(* Focused reflected interval-reciprocal regression.                         *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_exact_rational_inv.ml";;
needs "candle/cv_compute_exact_interval_inv_core.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_linear_combination_realize;;

let candle_q_interval_inv_test_axioms_before = axioms ();;

let candle_q_interval_inv_positive =
  `(((((2,0),0):(num#num)#num),(((4,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_inv_negative =
  `(((((0,4),0):(num#num)#num),(((0,2),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_inv_crossing =
  `(((((0,1),0):(num#num)#num),(((2,0),0):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_inv_positive_expected =
  `(((((1,0),3):(num#num)#num),(((1,0),1):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_inv_negative_expected =
  `(((((0,1),1):(num#num)#num),(((0,1),3):(num#num)#num)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_interval_inv_compute input operation equations =
  let representation =
    REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
                 Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                 FST; SND]
      (mk_comb (`candle_cv_q_interval`,input)) in
  Kernel.compute
    (COMPUTE_INIT_THMS,equations)
    (mk_comb (operation,rand (concl representation)));;

let candle_q_interval_inv_positive_computed =
  candle_q_interval_inv_compute candle_q_interval_inv_positive
    `candle_cv_q_interval_inv` candle_cv_q_interval_inv_compute_eqs;;

let candle_q_interval_inv_negative_computed =
  candle_q_interval_inv_compute candle_q_interval_inv_negative
    `candle_cv_q_interval_inv` candle_cv_q_interval_inv_compute_eqs;;

let candle_q_interval_inv_crossing_domain =
  candle_q_interval_inv_compute candle_q_interval_inv_crossing
    `candle_cv_q_interval_not_zero` candle_cv_q_interval_inv_compute_eqs;;

let candle_q_interval_inv_expected input =
  rand
    (concl
      (REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
                    Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                    FST; SND]
        (mk_comb (`candle_cv_q_interval`,input))));;

if not
    (aconv (rand (concl candle_q_interval_inv_positive_computed))
      (candle_q_interval_inv_expected
        candle_q_interval_inv_positive_expected)) ||
   not
    (aconv (rand (concl candle_q_interval_inv_negative_computed))
      (candle_q_interval_inv_expected
        candle_q_interval_inv_negative_expected)) ||
   not
    (aconv (rand (concl candle_q_interval_inv_crossing_domain))
      `Cexp_num 0`) then
  failwith "reflected interval reciprocal: computed result mismatch";;

let candle_q_interval_inv_positive_sound =
  let domain =
    prove
      (`candle_q_interval_not_zero
          (((((2,0),0),((4,0),0)):
             ((num#num)#num)#((num#num)#num)))`,
       REWRITE_TAC[candle_q_interval_not_zero_def; candle_q_le_def;
                   candle_q_zero_def; candle_q_den_def; FST; SND] THEN
       CONV_TAC NUM_REDUCE_CONV) in
  let contains =
    prove
      (`candle_q_interval_contains
          (((((2,0),0),((4,0),0)):
             ((num#num)#num)#((num#num)#num))) (&3)`,
       REWRITE_TAC[candle_q_interval_contains_def; candle_q_real_def;
                   candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV) in
  MATCH_MP
    (SPECL [candle_q_interval_inv_positive; `&3:real`]
      candle_q_interval_inv_sound)
    (CONJ domain contains);;

let candle_q_interval_inv_negative_sound =
  let domain =
    prove
      (`candle_q_interval_not_zero
          (((((0,4),0),((0,2),0)):
             ((num#num)#num)#((num#num)#num)))`,
       REWRITE_TAC[candle_q_interval_not_zero_def; candle_q_le_def;
                   candle_q_zero_def; candle_q_den_def; FST; SND] THEN
       CONV_TAC NUM_REDUCE_CONV) in
  let contains =
    prove
      (`candle_q_interval_contains
          (((((0,4),0),((0,2),0)):
             ((num#num)#num)#((num#num)#num))) (-- &3)`,
       REWRITE_TAC[candle_q_interval_contains_def; candle_q_real_def;
                   candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
       REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV) in
  MATCH_MP
    (SPECL [candle_q_interval_inv_negative; `-- &3:real`]
      candle_q_interval_inv_sound)
    (CONJ domain contains);;

if hyp candle_q_interval_inv_positive_computed <> [] ||
   hyp candle_q_interval_inv_negative_computed <> [] ||
   hyp candle_q_interval_inv_crossing_domain <> [] ||
   hyp candle_q_interval_inv_positive_sound <> [] ||
   hyp candle_q_interval_inv_negative_sound <> [] then
  failwith "reflected interval reciprocal: proof assumptions";;

let candle_q_interval_inv_test_axioms_after = axioms ();;
if length candle_q_interval_inv_test_axioms_after <>
     length candle_q_interval_inv_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_interval_inv_test_axioms_before)
       candle_q_interval_inv_test_axioms_after) then
  failwith "reflected interval reciprocal: changed the global axiom set";;

let _ =
  print_endline
    "CANDLE_CV_EXACT_INTERVAL_INV_RESULT domains=3 accepted=2 rejected=1 sound=2";;
let _ = print_endline "CANDLE_CV_EXACT_INTERVAL_INV_OK";;
