(* ========================================================================== *)
(* Prepare both functions of the authenticated disjunctive target.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixture.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_fixture;;

let candle_disjunctive_prepare_axioms_before = axioms ();;
let candle_disjunctive_prepare_sqrt_count = ref 0;;

let candle_disjunctive_prepare_sqrt_interval _ =
  candle_disjunctive_prepare_sqrt_count :=
    !candle_disjunctive_prepare_sqrt_count + 1;
  `((((0,0),0),((4,0),0)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_disjunctive_prepare_constant_probe name tm =
  let _,source =
    Candle_cv_analytic_expr_reify.candle_analytic_reify_real_expression
      candle_disjunctive_prepare_sqrt_interval [] tm in
  if hyp source <> [] || not (aconv (rand (concl source)) tm) then
    failwith ("disjunctive analytic preparation: constant probe " ^ name);
  print_endline ("CANDLE_CV_DISJUNCTIVE_CONSTANT_PROBE_OK name=" ^ name);;

let _ =
  candle_disjunctive_prepare_constant_probe "pi" `pi`;;
let _ =
  candle_disjunctive_prepare_constant_probe "acs-third-radical"
    `sqrt (&1 - (&1 / &3) pow 2)`;;
let _ =
  candle_disjunctive_prepare_constant_probe "acs-third-ratio"
    `(&1 / &3) / sqrt (&1 - (&1 / &3) pow 2)`;;
let _ =
  candle_disjunctive_prepare_constant_probe "acs-third-atn"
    `atn ((&1 / &3) / sqrt (&1 - (&1 / &3) pow 2))`;;
let _ =
  candle_disjunctive_prepare_constant_probe "acs-third-equivalent"
    `pi / &2 - atn ((&1 / &3) / sqrt (&1 - (&1 / &3) pow 2))`;;
let _ =
  candle_disjunctive_prepare_constant_probe "acs-third-compact"
    `acs (&1 / &3)`;;
let _ =
  candle_disjunctive_prepare_constant_probe "acs-third-expanded"
    `acs (&1 * inv (&3))`;;
let _ =
  candle_disjunctive_prepare_constant_probe "const1-expanded"
    `(&3 * acs (&1 * inv (&3)) - pi) * inv pi`;;

let candle_disjunctive_prepare_one function_term =
  let started = Unix.gettimeofday () in
  let prepared =
    candle_q_dim_analytic_jet_prepare_six_with
      candle_disjunctive_prepare_sqrt_interval function_term in
  let seconds = Unix.gettimeofday () -. started in
  let instructions = length (dest_list prepared.program_term) in
  if instructions <= 0 ||
     hyp prepared.valid_theorem <> [] ||
     hyp prepared.source_theorem <> [] ||
     hyp prepared.compile_theorem <> [] ||
     hyp prepared.program_representation <> [] then
    failwith "disjunctive analytic preparation: theorem contract failed";
  prepared,instructions,seconds;;

let candle_disjunctive_prepared =
  map candle_disjunctive_prepare_one
    candle_disjunctive_analytic_functions;;

if length candle_disjunctive_prepared <> 2 then
  failwith "disjunctive analytic preparation: function count drift";;

let candle_disjunctive_prepare_axioms_after = axioms ();;
if length candle_disjunctive_prepare_axioms_after <>
     length candle_disjunctive_prepare_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_disjunctive_prepare_axioms_before)
       candle_disjunctive_prepare_axioms_after) then
  failwith "disjunctive analytic preparation changed the global axiom set";;

let _,candle_disjunctive_prepare_instructions0,
    candle_disjunctive_prepare_seconds0 =
  el 0 candle_disjunctive_prepared;;
let _,candle_disjunctive_prepare_instructions1,
    candle_disjunctive_prepare_seconds1 =
  el 1 candle_disjunctive_prepared;;

if candle_disjunctive_prepare_instructions0 <> 1 ||
   candle_disjunctive_prepare_instructions1 <> 167 ||
   !candle_disjunctive_prepare_sqrt_count <> 17 then
  failwith "disjunctive analytic preparation: metric drift";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_PREPARE_RESULT functions=2 instructions0=" ^
   string_of_int candle_disjunctive_prepare_instructions0 ^
   " instructions1=" ^
   string_of_int candle_disjunctive_prepare_instructions1 ^
   " sqrt_occurrences=" ^
   string_of_int !candle_disjunctive_prepare_sqrt_count ^
   " prepare_seconds0=" ^
   string_of_float candle_disjunctive_prepare_seconds0 ^
   " prepare_seconds1=" ^
   string_of_float candle_disjunctive_prepare_seconds1);;
print_endline
  "CANDLE_CV_DISJUNCTIVE_PREPARE_OK DEVELOPMENT_NON_RELEASE";;
