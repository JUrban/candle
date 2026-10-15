(* DEVELOPMENT / NON-RELEASE: inspect the exact normalized source terms for
   prep-5202826650 without constructing numerical functions or certificates. *)

open M_verifier_main;;

let candle_cv_matan_probe_component =
  `ineqm [x1; x2; x3; x4; x5; x6]
    (frac_right 3 #0.2547
      [#6.3504,#6.3504; #4.0,#6.3504; #4.0,#6.3504;
       #3.01 * #3.01,#3.915 * #3.915; #4.0,#4.0; #4.0,#4.0])
    (tau_residual_x x1 x2 x3 x4 x5 x6 * -- &1 < &0 \/
     delta_x x1 x2 x3 x4 x5 x6 < &0)`;;

let candle_cv_matan_probe_domain =
  Break_case.ineqm_conv candle_cv_matan_probe_component;;

let candle_cv_matan_probe_encoded = rand (concl candle_cv_matan_probe_domain);;

let candle_cv_matan_probe_formula =
  (REWRITE_CONV
     [TAUT `(P ==> Q) <=> (~P \/ Q)`;
      REAL_ARITH `~(a > b:real) <=> a <= b`;
      REAL_ARITH `~(a < b:real) <=> b <= a`;
      REAL_ARITH `~(a >= b:real) <=> a < b`;
      REAL_ARITH `~(a <= b:real) <=> b < a`]
   THENC
   REWRITE_CONV
     ([Definitions.ineq; IMP_IMP; REAL_MUL_LZERO; REAL_MUL_RZERO] @
      Definitions.flyspeck_defs)
   THENC DEPTH_CONV let_CONV)
    candle_cv_matan_probe_encoded;;

let candle_cv_matan_probe_expanded =
  rand (concl candle_cv_matan_probe_formula);;

let candle_cv_matan_probe_inequality,_,_ =
  M_verifier_main.dest_ineq candle_cv_matan_probe_expanded;;

let candle_cv_matan_probe_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1;real_pow] candle_cv_matan_probe_inequality;;

let candle_cv_matan_probe_relations =
  striplist dest_disj ((lhand o concl) candle_cv_matan_probe_standard);;

let candle_cv_matan_probe_sources =
  map lhand candle_cv_matan_probe_relations;;

if length candle_cv_matan_probe_sources <> 2 ||
   hyp candle_cv_matan_probe_domain <> [] ||
   hyp candle_cv_matan_probe_formula <> [] ||
   hyp candle_cv_matan_probe_standard <> [] then
  failwith "matan source probe contract";;

print_endline
  ("CANDLE_CV_MATAN_PREP520_SOURCE_TERM DEVELOPMENT_NON_RELEASE branch=0 term=" ^
   string_of_term (List.nth candle_cv_matan_probe_sources 0));;
print_endline
  ("CANDLE_CV_MATAN_PREP520_SOURCE_TERM DEVELOPMENT_NON_RELEASE branch=1 term=" ^
   string_of_term (List.nth candle_cv_matan_probe_sources 1));;
print_endline "CANDLE_CV_MATAN_PREP520_SOURCE_TERMS_OK";;
