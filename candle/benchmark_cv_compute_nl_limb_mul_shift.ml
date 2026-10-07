(* ========================================================================== *)
(* Reflected fixed-width limb discriminator for nonlinear arithmetic.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This compares one 68-bit product followed by *)
(* a 23-bit directed-down shift with an equivalent two-limb calculation.     *)
(* The limb inputs are prepared outside the recurring computation, as they   *)
(* would be in an authenticated reusable numerical plan.  Both calls return  *)
(* closed, assumption-free Kernel.compute theorems with exactly equal data.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

open Candle_cv_analytic_expr_jet_prove;;

let candle_cv_nl_limb_shift_def = new_definition
 `candle_cv_nl_limb_shift = Cexp_num 8388608`;;

let candle_cv_nl_limb_base_over_shift_def = new_definition
 `candle_cv_nl_limb_base_over_shift = Cexp_num 128`;;

let candle_cv_nl_limb_base_squared_over_shift_def = new_definition
 `candle_cv_nl_limb_base_squared_over_shift = Cexp_num 137438953472`;;

let candle_cv_nl_big_mul_shift_def = new_definition
 `candle_cv_nl_big_mul_shift x y =
    Cexp_div (Cexp_mul x y) candle_cv_nl_limb_shift`;;

(* A nonnegative input x is encoded as pair(lo,hi), denoting               *)
(* lo + 2^30 * hi. Since 2^23 divides 2^30, only lo_x * lo_y needs a        *)
(* division. All intermediates in this fixture remain below 2^60.           *)

let candle_cv_nl_limb_mul_shift_def = new_definition
 `candle_cv_nl_limb_mul_shift x y =
    Cexp_add
      (Cexp_div
        (Cexp_mul (Cexp_fst x) (Cexp_fst y))
        candle_cv_nl_limb_shift)
      (Cexp_add
        (Cexp_mul
          (Cexp_add
            (Cexp_mul (Cexp_fst x) (Cexp_snd y))
            (Cexp_mul (Cexp_snd x) (Cexp_fst y)))
          candle_cv_nl_limb_base_over_shift)
        (Cexp_mul
          (Cexp_mul (Cexp_snd x) (Cexp_snd y))
          candle_cv_nl_limb_base_squared_over_shift))`;;

let candle_cv_nl_big_mul_shift_repeat_def = define
 `(candle_cv_nl_big_mul_shift_repeat
      (Cexp_num n) x y = Cexp_num 0) /\
  (candle_cv_nl_big_mul_shift_repeat
      (Cexp_pair h t) x y =
    Cexp_add (candle_cv_nl_big_mul_shift x y)
      (candle_cv_nl_big_mul_shift_repeat t x y))`;;

let candle_cv_nl_big_mul_shift_repeat_compute = prove
 (`!encoded_count x y.
     candle_cv_nl_big_mul_shift_repeat encoded_count x y =
     Cexp_if (Cexp_ispair encoded_count)
       (Cexp_add (candle_cv_nl_big_mul_shift x y)
         (candle_cv_nl_big_mul_shift_repeat (Cexp_snd encoded_count) x y))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded_count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nl_big_mul_shift_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_nl_limb_mul_shift_repeat_def = define
 `(candle_cv_nl_limb_mul_shift_repeat
      (Cexp_num n) x y = Cexp_num 0) /\
  (candle_cv_nl_limb_mul_shift_repeat
      (Cexp_pair h t) x y =
    Cexp_add (candle_cv_nl_limb_mul_shift x y)
      (candle_cv_nl_limb_mul_shift_repeat t x y))`;;

let candle_cv_nl_limb_mul_shift_repeat_compute = prove
 (`!encoded_count x y.
     candle_cv_nl_limb_mul_shift_repeat encoded_count x y =
     Cexp_if (Cexp_ispair encoded_count)
       (Cexp_add (candle_cv_nl_limb_mul_shift x y)
         (candle_cv_nl_limb_mul_shift_repeat (Cexp_snd encoded_count) x y))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded_count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nl_limb_mul_shift_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_nl_limb_mul_shift_equations =
  map SPEC_ALL
   [candle_cv_nl_limb_shift_def;
    candle_cv_nl_limb_base_over_shift_def;
    candle_cv_nl_limb_base_squared_over_shift_def;
    candle_cv_nl_big_mul_shift_def;
    candle_cv_nl_limb_mul_shift_def;
    candle_cv_nl_big_mul_shift_repeat_compute;
    candle_cv_nl_limb_mul_shift_repeat_compute];;

let candle_cv_nl_limb_mul_shift_marker lane event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=nl-limb-mul-shift scope=repeat-32768" ^
     " phase=" ^ lane ^ " event=" ^ event);;

let candle_cv_nl_limb_mul_shift_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_cv_nl_limb_mul_shift_count = ref `Cexp_num 0`;;

let _ =
  candle_cv_nl_limb_mul_shift_count :=
    itlist
      (fun _ tail -> candle_cv_nl_limb_mul_shift_pair `Cexp_num 0` tail)
      (1--32768) `Cexp_num 0`;;

(* x = 2^34 - 13 and y = 2^34 - 43.  Their product has 68 bits. *)
let candle_cv_nl_limb_mul_shift_x = `Cexp_num 17179869171` and
    candle_cv_nl_limb_mul_shift_y = `Cexp_num 17179869141`;;

let candle_cv_nl_limb_mul_shift_x_limbs =
  candle_cv_nl_limb_mul_shift_pair
    `Cexp_num 1073741811` `Cexp_num 15` and
    candle_cv_nl_limb_mul_shift_y_limbs =
  candle_cv_nl_limb_mul_shift_pair
    `Cexp_num 1073741781` `Cexp_num 15`;;

let candle_cv_nl_limb_mul_shift_big_call = ref `Cexp_num 0` and
    candle_cv_nl_limb_mul_shift_limb_call = ref `Cexp_num 0`;;

let _ =
  candle_cv_nl_limb_mul_shift_big_call :=
    list_mk_comb
      (`candle_cv_nl_big_mul_shift_repeat`,
       [!candle_cv_nl_limb_mul_shift_count;
        candle_cv_nl_limb_mul_shift_x;
        candle_cv_nl_limb_mul_shift_y]);
  candle_cv_nl_limb_mul_shift_limb_call :=
    list_mk_comb
      (`candle_cv_nl_limb_mul_shift_repeat`,
       [!candle_cv_nl_limb_mul_shift_count;
        candle_cv_nl_limb_mul_shift_x_limbs;
        candle_cv_nl_limb_mul_shift_y_limbs]);;

let candle_cv_nl_limb_mul_shift_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_nl_limb_mul_shift_equations tm;;

let candle_cv_nl_limb_mul_shift_result term = rand (concl term);;

let candle_cv_nl_limb_mul_shift_dummy_result = REFL `Cexp_num 0`;;

let candle_cv_nl_limb_mul_shift_big_result_1 =
      ref candle_cv_nl_limb_mul_shift_dummy_result and
    candle_cv_nl_limb_mul_shift_limb_result_1 =
      ref candle_cv_nl_limb_mul_shift_dummy_result and
    candle_cv_nl_limb_mul_shift_limb_result_2 =
      ref candle_cv_nl_limb_mul_shift_dummy_result and
    candle_cv_nl_limb_mul_shift_big_result_2 =
      ref candle_cv_nl_limb_mul_shift_dummy_result;;

let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-1" "begin";;
let _ = candle_cv_nl_limb_mul_shift_big_result_1 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_big_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-1" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-1" "begin";;
let _ = candle_cv_nl_limb_mul_shift_limb_result_1 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_limb_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-1" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-2" "begin";;
let _ = candle_cv_nl_limb_mul_shift_limb_result_2 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_limb_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-2" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-2" "begin";;
let _ = candle_cv_nl_limb_mul_shift_big_result_2 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_big_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-2" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-3" "begin";;
let _ = candle_cv_nl_limb_mul_shift_big_result_1 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_big_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-3" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-3" "begin";;
let _ = candle_cv_nl_limb_mul_shift_limb_result_1 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_limb_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-3" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-4" "begin";;
let _ = candle_cv_nl_limb_mul_shift_limb_result_2 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_limb_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "two-limb-4" "end";;

let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-4" "begin";;
let _ = candle_cv_nl_limb_mul_shift_big_result_2 :=
  candle_cv_nl_limb_mul_shift_compute
    !candle_cv_nl_limb_mul_shift_big_call;;
let _ = candle_cv_nl_limb_mul_shift_marker "big-natural-4" "end";;

let _ =
  let big_result_1 = !candle_cv_nl_limb_mul_shift_big_result_1 in
  let limb_result_1 = !candle_cv_nl_limb_mul_shift_limb_result_1 in
  let limb_result_2 = !candle_cv_nl_limb_mul_shift_limb_result_2 in
  let big_result_2 = !candle_cv_nl_limb_mul_shift_big_result_2 in
  if hyp big_result_1 <> [] ||
     hyp limb_result_1 <> [] ||
     hyp limb_result_2 <> [] ||
     hyp big_result_2 <> [] ||
     not
       (aconv
         (candle_cv_nl_limb_mul_shift_result big_result_1)
         (candle_cv_nl_limb_mul_shift_result limb_result_1)) ||
     not
       (aconv
         (candle_cv_nl_limb_mul_shift_result big_result_2)
         (candle_cv_nl_limb_mul_shift_result limb_result_2)) then
    failwith "nl limb multiply-shift: theorem or exact-result mismatch"
  else
    print_endline
      "CANDLE_CV_NL_LIMB_MUL_SHIFT_RESULT repeats=32768 product_bits=68 shift=23 exact_match=1 assumptions=0";;

print_endline "CANDLE_CV_NL_LIMB_MUL_SHIFT_OK DEVELOPMENT_NON_RELEASE";;
