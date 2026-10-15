(* ========================================================================== *)
(* Point-tight square-root data for the genuine Flyspeck [matan] root center. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The center and whole-box programs reify the   *)
(* same source expression, but their square-root certificates serve distinct *)
(* environments.  This file prepares the center program on exact midpoint    *)
(* inputs; the existing tight program remains the whole-box program.          *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;

module Test_cv_compute_analytic_expr_matan_genuine_root_center_prepare = struct

let axioms_before = axioms ();;
let started = Unix.gettimeofday ();;
let center_scale_int = 10000;;
let center_scale = Num.num_of_int center_scale_int;;
let center_scale_square = Num.mul_num center_scale center_scale;;

let center_num =
  map2
    (fun lo hi ->
      Num.div_num (Num.add_num lo hi) (Num.num_of_int 2))
    lower_num upper_num;;
let center_interval_environment =
  zip vector_variables (map (fun value -> value,value) center_num);;

let center_scaled_square n =
  let value = Num.num_of_int n in
  Num.div_num (Num.mul_num value value) center_scale_square;;

let rec center_floor_scaled_sqrt value low high =
  if high - low <= 1 then low
  else
    let middle = (low + high) / 2 in
    if Num.le_num (center_scaled_square middle) value then
      center_floor_scaled_sqrt value middle high
    else center_floor_scaled_sqrt value low middle;;

let center_floor_sqrt_scaled value =
  let integer_ceiling = ceil_sqrt_from value 0 in
  center_floor_scaled_sqrt
    value 0 ((integer_ceiling + 1) * center_scale_int);;

let center_ceil_sqrt_scaled value =
  let lower = center_floor_sqrt_scaled value in
  if Num.eq_num (center_scaled_square lower) value then lower else lower + 1;;

let center_scaled_num n =
  Num.div_num (Num.num_of_int n) center_scale;;

let center_sqrt_interval tm =
  let child = candle_q_dest_unary `sqrt:real->real` tm in
  let child_lower,child_upper =
    candle_nl_matan_interval_eval center_interval_environment child in
  if Num.lt_num child_lower (Num.num_of_int 0) then
    failwith "genuine matan center: negative square-root lower bound";
  let lower_scaled = center_floor_sqrt_scaled child_lower in
  let upper_scaled = center_ceil_sqrt_scaled child_upper in
  if not (Num.le_num (center_scaled_square lower_scaled) child_lower) ||
     not (Num.le_num child_upper (center_scaled_square upper_scaled)) then
    failwith "genuine matan center: enclosure rounding drift";
  mk_pair
    (candle_q_term (center_scaled_num lower_scaled),
     candle_q_term (center_scaled_num upper_scaled));;

let center_expression,center_source_theorem =
  candle_analytic_reify_real_expression
    center_sqrt_interval vector_variables source;;
let center_valid_theorem = prove
 (list_mk_comb (`candle_analytic_valid_dim`,[`6`;center_expression]),
  REWRITE_TAC[candle_analytic_valid_dim_def; candle_poly_valid_dim_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let center_compile_theorem =
  REWRITE_CONV
    [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
    (mk_comb (`candle_analytic_compile`,center_expression));;
let center_program = rand (concl center_compile_theorem);;
let center_program_representation =
  REWRITE_CONV
    [candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_analytic_sqrt_interval_def;
     candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
     FST; SND]
    (mk_comb (`candle_cv_analytic_instruction_list`,center_program));;
let center_instruction_count = length (dest_list center_program);;
let seconds = Unix.gettimeofday () -. started;;

if center_instruction_count <> instruction_count ||
   hyp center_valid_theorem <> [] || hyp center_source_theorem <> [] ||
   hyp center_compile_theorem <> [] ||
   hyp center_program_representation <> [] then
  failwith "genuine matan center: preparation contract mismatch";;

let axioms_after = axioms ();;
if length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan center: changed the global axiom set";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ROOT_CENTER_PREPARE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " sqrt_scale=" ^ string_of_int center_scale_int ^
   " instructions=" ^ string_of_int center_instruction_count ^
   " seconds=" ^ string_of_float seconds ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_GENUINE_ROOT_CENTER_PREPARE_OK";;

end;;
