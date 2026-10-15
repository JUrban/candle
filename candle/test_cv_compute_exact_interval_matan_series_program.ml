(* ========================================================================== *)
(* Focused reflected regression for the crossing-zero [matan] cval program.  *)
(* ========================================================================== *)

(* Loaded after [cv_compute_exact_interval_matan_series_program.ml] from the
   prepared action-296 checkpoint. *)

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_matan_series;;
open Candle_cv_exact_interval_matan_series_program;;

let candle_matan_program_axioms_before = axioms ();;

let candle_matan_program_input_symmetric =
 `(((((0,1),4):(num#num)#num),(((1,0),4):(num#num)#num)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_matan_program_input_narrow =
 `(((((0,1),9):(num#num)#num),(((1,0),9):(num#num)#num)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_matan_program_input_too_low =
 `(((((0,1),3):(num#num)#num),(((1,0),9):(num#num)#num)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_matan_program_input_too_wide =
 `(((((0,1),4):(num#num)#num),(((1,0),0):(num#num)#num)):
    ((num#num)#num)#((num#num)#num))`;;

let candle_matan_program_representation input =
  REWRITE_CONV
    [candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
     FST; SND]
    (mk_comb (`candle_cv_q_interval`,input));;

let candle_matan_program_flag_accept = prove
 (`!b. Cexp_num (if b then 1 else 0) = Cexp_num 1 ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "cval"] THEN ARITH_TAC);;

let candle_matan_program_domain input representation =
  let computed =
    Kernel.compute
      (COMPUTE_INIT_THMS,candle_cv_q_matan_series_compute_eqs)
      (mk_comb
        (`candle_cv_q_interval_matan_series_domain`,
         rand (concl representation))) in
  let linked =
    TRANS
      (SYM
        (SPEC input candle_cv_q_interval_matan_series_domain_correct))
      (TRANS
        (AP_TERM `candle_cv_q_interval_matan_series_domain`
          representation)
        computed) in
  (computed,MATCH_MP candle_matan_program_flag_accept linked);;

let candle_matan_program_output function_term correctness input representation =
  let computed =
    Kernel.compute
      (COMPUTE_INIT_THMS,candle_cv_q_matan_series_compute_eqs)
      (mk_comb (function_term,rand (concl representation))) in
  let linked =
    TRANS
      (SYM (SPEC input correctness))
      (TRANS (AP_TERM function_term representation) computed) in
  (computed,linked);;

let candle_matan_program_started = Unix.gettimeofday ();;

let candle_matan_program_symmetric_representation =
  candle_matan_program_representation candle_matan_program_input_symmetric;;

let candle_matan_program_narrow_representation =
  candle_matan_program_representation candle_matan_program_input_narrow;;

let (candle_matan_program_symmetric_domain_compute,
     candle_matan_program_symmetric_domain) =
  candle_matan_program_domain candle_matan_program_input_symmetric
    candle_matan_program_symmetric_representation;;

let (candle_matan_program_narrow_domain_compute,
     candle_matan_program_narrow_domain) =
  candle_matan_program_domain candle_matan_program_input_narrow
    candle_matan_program_narrow_representation;;

let candle_matan_program_symmetric_value =
  candle_matan_program_output `candle_cv_q_interval_matan_series`
    candle_cv_q_interval_matan_series_correct
    candle_matan_program_input_symmetric
    candle_matan_program_symmetric_representation;;

let candle_matan_program_symmetric_derivative =
  candle_matan_program_output `candle_cv_q_interval_dmatan_series`
    candle_cv_q_interval_dmatan_series_correct
    candle_matan_program_input_symmetric
    candle_matan_program_symmetric_representation;;

let candle_matan_program_symmetric_second_derivative =
  candle_matan_program_output `candle_cv_q_interval_ddmatan_series`
    candle_cv_q_interval_ddmatan_series_correct
    candle_matan_program_input_symmetric
    candle_matan_program_symmetric_representation;;

let candle_matan_program_narrow_value =
  candle_matan_program_output `candle_cv_q_interval_matan_series`
    candle_cv_q_interval_matan_series_correct
    candle_matan_program_input_narrow
    candle_matan_program_narrow_representation;;

let candle_matan_program_narrow_derivative =
  candle_matan_program_output `candle_cv_q_interval_dmatan_series`
    candle_cv_q_interval_dmatan_series_correct
    candle_matan_program_input_narrow
    candle_matan_program_narrow_representation;;

let candle_matan_program_narrow_second_derivative =
  candle_matan_program_output `candle_cv_q_interval_ddmatan_series`
    candle_cv_q_interval_ddmatan_series_correct
    candle_matan_program_input_narrow
    candle_matan_program_narrow_representation;;

let candle_matan_program_bad_domain input =
  let representation = candle_matan_program_representation input in
  Kernel.compute
    (COMPUTE_INIT_THMS,candle_cv_q_matan_series_compute_eqs)
    (mk_comb
      (`candle_cv_q_interval_matan_series_domain`,
       rand (concl representation)));;

let candle_matan_program_too_low_domain_compute =
  candle_matan_program_bad_domain candle_matan_program_input_too_low;;

let candle_matan_program_too_wide_domain_compute =
  candle_matan_program_bad_domain candle_matan_program_input_too_wide;;

let candle_matan_program_symmetric_sound =
  let x = `x:real` in
  let membership =
    mk_comb
      (mk_comb (`candle_q_interval_contains`,
                candle_matan_program_input_symmetric),x) in
  let value =
    MATCH_MP
      (SPECL [candle_matan_program_input_symmetric;x]
        candle_q_interval_matan_series_sound)
      (CONJ candle_matan_program_symmetric_domain (ASSUME membership)) in
  let derivative =
    MATCH_MP
      (SPECL [candle_matan_program_input_symmetric;x]
        candle_q_interval_dmatan_series_sound)
      (CONJ candle_matan_program_symmetric_domain (ASSUME membership)) in
  let second_derivative =
    MATCH_MP
      (SPECL [candle_matan_program_input_symmetric;x]
        candle_q_interval_ddmatan_series_sound)
      (CONJ candle_matan_program_symmetric_domain (ASSUME membership)) in
  GEN x (DISCH membership
    (CONJ value (CONJ derivative second_derivative)));;

let candle_matan_program_compute_seconds =
  Unix.gettimeofday () -. candle_matan_program_started;;

let candle_matan_program_output_theorems =
  [fst candle_matan_program_symmetric_value;
   snd candle_matan_program_symmetric_value;
   fst candle_matan_program_symmetric_derivative;
   snd candle_matan_program_symmetric_derivative;
   fst candle_matan_program_symmetric_second_derivative;
   snd candle_matan_program_symmetric_second_derivative;
   fst candle_matan_program_narrow_value;
   snd candle_matan_program_narrow_value;
   fst candle_matan_program_narrow_derivative;
   snd candle_matan_program_narrow_derivative;
   fst candle_matan_program_narrow_second_derivative;
   snd candle_matan_program_narrow_second_derivative];;

if exists (fun th -> hyp th <> []) candle_matan_program_output_theorems ||
   hyp candle_matan_program_symmetric_domain <> [] ||
   hyp candle_matan_program_narrow_domain <> [] ||
   hyp candle_matan_program_symmetric_sound <> [] ||
   rand (concl candle_matan_program_symmetric_domain_compute) <>
     `Cexp_num 1` ||
   rand (concl candle_matan_program_narrow_domain_compute) <>
     `Cexp_num 1` ||
   rand (concl candle_matan_program_too_low_domain_compute) <>
     `Cexp_num 0` ||
   rand (concl candle_matan_program_too_wide_domain_compute) <>
     `Cexp_num 0` then
  failwith "reflected matan series: theorem or domain mismatch";;

let candle_matan_program_axioms_after = axioms ();;
if length candle_matan_program_axioms_after <>
     length candle_matan_program_axioms_before ||
   not
     (List.for_all
       (fun th -> List.mem th candle_matan_program_axioms_before)
       candle_matan_program_axioms_after) then
  failwith "reflected matan series: changed the global axiom set";;

let _ =
  print_endline
    ("CANDLE_CV_EXACT_INTERVAL_MATAN_SERIES_PROGRAM_RESULT " ^
     "valid_boxes=2 rejected_boxes=2 computed_packets=6 sound_packets=3 " ^
     "compute_seconds=" ^ string_of_float candle_matan_program_compute_seconds);;

let _ = print_endline "CANDLE_CV_EXACT_INTERVAL_MATAN_SERIES_PROGRAM_OK";;
