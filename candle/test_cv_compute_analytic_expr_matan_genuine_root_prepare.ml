(* ========================================================================== *)
(* Prepare the complete main branch of a genuine Flyspeck [matan] target.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The source and root box come from the direct  *)
(* authenticated [prep-TSKAJXY-GXSABWC DIV] target.  This bounded test keeps  *)
(* the source-expansion theorem and constructs one shared-jet program; it     *)
(* makes no numerical acceptance claim.                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;
needs "candle/cv_compute_analytic_expr_matan_domain_probe.ml";;
needs "candle/cv_compute_analytic_expr_reify.ml";;

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_analytic_expr_matan_domain_probe;;
open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_analytic_expr_calculus;;

module Test_cv_compute_analytic_expr_matan_genuine_root_prepare = struct

let axioms_before = axioms ();;
let started = Unix.gettimeofday ();;
let source_id = "prep-TSKAJXY-GXSABWC DIV";;

let target = candle_nl_matan_target source_id;;
let variables,bound_terms,formula = candle_nl_matan_target_parts target;;
let expansion_theorem = candle_nl_matan_expand_theorem formula;;
let expanded = rand (concl expansion_theorem);;

let main_relation,escape_relation =
  let operator,arguments = strip_comb expanded in
  if not (aconv operator `(\/):bool->bool->bool`) then
    failwith "genuine matan root: expanded formula is not a disjunction";
  match arguments with
  | [main;escape] -> main,escape
  | _ -> failwith "genuine matan root: disjunction arity";;

let main_source =
  let operator,arguments = strip_comb main_relation in
  if not (aconv operator `(<=):real->real->bool`) then
    failwith "genuine matan root: main branch is not a non-strict bound";
  match arguments with
  | [source;zero] when aconv zero `&0:real` -> source
  | _ -> failwith "genuine matan root: main bound shape";;

let functions,variable_vector =
  candle_direct_exprs_to_vector_fun [main_source];;
let function_term =
  match functions with
  | [function_term] -> function_term
  | _ -> failwith "genuine matan root: function conversion";;
let ordered_variables = M_taylor.dest_vector variable_vector;;

let bound_for variable =
  let rec find variables bounds =
    match variables,bounds with
    | candidate :: remaining_variables,bound :: remaining_bounds ->
        if aconv variable candidate then bound
        else find remaining_variables remaining_bounds
    | [],[] -> failwith "genuine matan root: missing variable bound"
    | _ -> failwith "genuine matan root: variable/bound length drift" in
  find variables bound_terms;;

let exact_bound_num tm =
  let expanded_bound =
    rand (concl (REWRITE_CONV candle_nl_matan_defs tm)) in
  let lower,upper = candle_nl_matan_interval_eval [] expanded_bound in
  if not (Num.eq_num lower upper) then
    failwith "genuine matan root: inexact source bound";
  lower;;

let ordered_bounds = map bound_for ordered_variables;;
let lower_num = map (fun (lower,_) -> exact_bound_num lower) ordered_bounds;;
let upper_num = map (fun (_,upper) -> exact_bound_num upper) ordered_bounds;;
let lower = map term_of_rat lower_num;;
let upper = map term_of_rat upper_num;;

let vector,source = dest_abs function_term;;
let vector_application = mk_icomb (`$`,vector);;
let vector_variables =
  map
    (fun index -> mk_comb (vector_application,mk_small_numeral index))
    (1--6);;
let interval_environment =
  zip vector_variables (zip lower_num upper_num);;

let square_integer n =
  let value = Num.num_of_int n in Num.mul_num value value;;

let rec floor_sqrt_from value n =
  if Num.le_num (square_integer (n + 1)) value then
    floor_sqrt_from value (n + 1)
  else n;;

let rec ceil_sqrt_from value n =
  if Num.le_num value (square_integer n) then n
  else ceil_sqrt_from value (n + 1);;

let sqrt_interval tm =
  let child = candle_q_dest_unary `sqrt:real->real` tm in
  let child_lower,child_upper =
    candle_nl_matan_interval_eval interval_environment child in
  if Num.lt_num child_lower (Num.num_of_int 0) then
    failwith "genuine matan root: negative square-root lower bound";
  let lower_integer = floor_sqrt_from child_lower 0 in
  let upper_integer = ceil_sqrt_from child_upper lower_integer in
  mk_pair
    (candle_q_term (Num.num_of_int lower_integer),
     candle_q_term (Num.num_of_int upper_integer));;

let expression,source_theorem =
  candle_analytic_reify_real_expression
    sqrt_interval vector_variables source;;
let valid_theorem = prove
 (list_mk_comb (`candle_analytic_valid_dim`,[`6`;expression]),
  REWRITE_TAC[candle_analytic_valid_dim_def; candle_poly_valid_dim_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let compile_theorem =
  REWRITE_CONV
    [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
    (mk_comb (`candle_analytic_compile`,expression));;
let program = rand (concl compile_theorem);;
let program_representation =
  REWRITE_CONV
    [candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_analytic_sqrt_interval_def;
     candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
     FST; SND]
    (mk_comb (`candle_cv_analytic_instruction_list`,program));;
let instruction_count = length (dest_list program);;
let matan_count = length (candle_nl_matan_subterms main_source);;
let seconds = Unix.gettimeofday () -. started;;

if length variables <> 6 || length bound_terms <> 6 ||
   length ordered_variables <> 6 || matan_count <> 12 ||
   instruction_count <= 0 || hyp expansion_theorem <> [] ||
   hyp valid_theorem <> [] || hyp source_theorem <> [] ||
   hyp compile_theorem <> [] || hyp program_representation <> [] then
  failwith "genuine matan root: preparation contract mismatch";;

let axioms_after = axioms ();;
if length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan root: changed the global axiom set";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ROOT_PREPARE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " dimensions=6 matan=12 instructions=" ^
   string_of_int instruction_count ^
   " source_chars=" ^ string_of_int (String.length (string_of_term main_source)) ^
   " seconds=" ^ string_of_float seconds ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_GENUINE_ROOT_PREPARE_OK";;

end;;
