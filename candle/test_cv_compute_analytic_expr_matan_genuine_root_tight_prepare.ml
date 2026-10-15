(* ========================================================================== *)
(* Tight reusable square-root data for the genuine Flyspeck [matan] root.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Each enclosure endpoint is an outward-rounded *)
(* exact rational on a fixed 10^-4 grid.  The analytic reifier proves that    *)
(* these untrusted numerical choices denote the unchanged source expression; *)
(* the reflected checker later verifies their domain/enclosure obligations.  *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_prepare.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;

module Test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare = struct

let axioms_before = axioms ();;
let started = Unix.gettimeofday ();;
let scale_int = 10000;;
let scale = Num.num_of_int scale_int;;
let scale_square = Num.mul_num scale scale;;

let scaled_square n =
  let value = Num.num_of_int n in
  Num.div_num (Num.mul_num value value) scale_square;;

let rec floor_scaled_sqrt value low high =
  if high - low <= 1 then low
  else
    let middle = (low + high) / 2 in
    if Num.le_num (scaled_square middle) value then
      floor_scaled_sqrt value middle high
    else floor_scaled_sqrt value low middle;;

let floor_sqrt_scaled value =
  let integer_ceiling = ceil_sqrt_from value 0 in
  floor_scaled_sqrt value 0 ((integer_ceiling + 1) * scale_int);;

let ceil_sqrt_scaled value =
  let lower = floor_sqrt_scaled value in
  if Num.eq_num (scaled_square lower) value then lower else lower + 1;;

let scaled_num n = Num.div_num (Num.num_of_int n) scale;;

let tight_sqrt_interval tm =
  let child = candle_q_dest_unary `sqrt:real->real` tm in
  let child_lower,child_upper =
    candle_nl_matan_interval_eval interval_environment child in
  if Num.lt_num child_lower (Num.num_of_int 0) then
    failwith "genuine matan tight root: negative square-root lower bound";
  let lower_scaled = floor_sqrt_scaled child_lower in
  let upper_scaled = ceil_sqrt_scaled child_upper in
  if not (Num.le_num (scaled_square lower_scaled) child_lower) ||
     not (Num.le_num child_upper (scaled_square upper_scaled)) then
    failwith "genuine matan tight root: enclosure rounding drift";
  mk_pair
    (candle_q_term (scaled_num lower_scaled),
     candle_q_term (scaled_num upper_scaled));;

let tight_expression,tight_source_theorem =
  candle_analytic_reify_real_expression
    tight_sqrt_interval vector_variables source;;
let tight_valid_theorem = prove
 (list_mk_comb (`candle_analytic_valid_dim`,[`6`;tight_expression]),
  REWRITE_TAC[candle_analytic_valid_dim_def; candle_poly_valid_dim_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let tight_compile_theorem =
  REWRITE_CONV
    [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
    (mk_comb (`candle_analytic_compile`,tight_expression));;
let tight_program = rand (concl tight_compile_theorem);;
let tight_program_representation =
  REWRITE_CONV
    [candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_analytic_sqrt_interval_def;
     candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
     FST; SND]
    (mk_comb (`candle_cv_analytic_instruction_list`,tight_program));;
let tight_instruction_count = length (dest_list tight_program);;
let seconds = Unix.gettimeofday () -. started;;

if tight_instruction_count <> instruction_count ||
   hyp tight_valid_theorem <> [] || hyp tight_source_theorem <> [] ||
   hyp tight_compile_theorem <> [] ||
   hyp tight_program_representation <> [] then
  failwith "genuine matan tight root: preparation contract mismatch";;

let axioms_after = axioms ();;
if length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan tight root: changed the global axiom set";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ROOT_TIGHT_PREPARE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " sqrt_scale=" ^ string_of_int scale_int ^
   " instructions=" ^ string_of_int tight_instruction_count ^
   " seconds=" ^ string_of_float seconds ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_GENUINE_ROOT_TIGHT_PREPARE_OK";;

end;;
