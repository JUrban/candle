(* ========================================================================== *)
(* Focused reflected reciprocal regression.                                  *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;

needs "candle/cv_compute_exact_rational_inv.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_inv;;

let candle_q_inv_test_axioms_before = axioms ();;

let candle_q_inv_test_cases =
  [(`(((3,0),1):(num#num)#num)`,`(((2,0),2):(num#num)#num)`);
   (`(((0,5),6):(num#num)#num)`,`(((0,7),4):(num#num)#num)`);
   (`(((8,3),6):(num#num)#num)`,`(((7,0),4):(num#num)#num)`);
   (`(((4,4),8):(num#num)#num)`,`(((0,0),0):(num#num)#num)`)];;

let candle_q_inv_test_one (input,expected) =
  let input_representation =
    REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def]
      (mk_comb (`candle_cv_q`,input)) in
  let computed =
    Kernel.compute
      (COMPUTE_INIT_THMS,candle_cv_q_inv_compute_eqs)
      (mk_comb (`candle_cv_q_inv`,rand (concl input_representation))) in
  let expected_representation =
    REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def]
      (mk_comb (`candle_cv_q`,expected)) in
  if hyp computed <> [] ||
     not (aconv (rand (concl computed))
            (rand (concl expected_representation))) then
    failwith "reflected rational reciprocal: computed result mismatch";
  let representation =
    PURE_REWRITE_RULE[SYM input_representation] computed in
  let abstract =
    TRANS representation (SYM expected_representation) in
  if hyp abstract <> [] then
    failwith "reflected rational reciprocal: representation assumptions";
  abstract;;

let candle_q_inv_test_results =
  map candle_q_inv_test_one candle_q_inv_test_cases;;

let candle_q_inv_test_positive_sound =
  let q = `(((8,3),6):(num#num)#num)` in
  let nonzero =
    prove
      (`candle_q_nonzero (((8,3),6):(num#num)#num)`,
       REWRITE_TAC[candle_q_nonzero_def] THEN
       CONV_TAC NUM_REDUCE_CONV) in
  MATCH_MP (SPEC q candle_q_inv_real) nonzero;;

let candle_q_inv_test_negative_sound =
  let q = `(((0,5),6):(num#num)#num)` in
  let nonzero =
    prove
      (`candle_q_nonzero (((0,5),6):(num#num)#num)`,
       REWRITE_TAC[candle_q_nonzero_def] THEN
       CONV_TAC NUM_REDUCE_CONV) in
  MATCH_MP (SPEC q candle_q_inv_real) nonzero;;

if length candle_q_inv_test_results <> 4 ||
   exists (fun th -> hyp th <> []) candle_q_inv_test_results ||
   hyp candle_q_inv_test_positive_sound <> [] ||
   hyp candle_q_inv_test_negative_sound <> [] then
  failwith "reflected rational reciprocal: proof regression";;

let candle_q_inv_test_axioms_after = axioms ();;
if length candle_q_inv_test_axioms_after <>
     length candle_q_inv_test_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_q_inv_test_axioms_before)
       candle_q_inv_test_axioms_after) then
  failwith "reflected rational reciprocal: changed the global axiom set";;

let _ =
  print_endline
    "CANDLE_CV_EXACT_RATIONAL_INV_RESULT cases=4 sound=2 theorem_producing=true";;
let _ = print_endline "CANDLE_CV_EXACT_RATIONAL_INV_OK";;
