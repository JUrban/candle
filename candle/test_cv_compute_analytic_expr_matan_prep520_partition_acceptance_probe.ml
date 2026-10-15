(* ========================================================================== *)
(* Reflected acceptance scout for the four genuine prep-5202826650 a pieces. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This deliberately stops before theorem-tree   *)
(* reconstruction.  It runs the complete dual center/box checker on both     *)
(* disjuncts of every authenticated serialized component, identifying the    *)
(* numerical proof branch needed by the proof-producing adapter.             *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_matan_prep520_partition_plan.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_compute.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_compute;;
open Test_cv_compute_analytic_expr_matan_prep520_partition_plan;;

module Test_cv_compute_analytic_expr_matan_prep520_partition_acceptance_probe = struct

let axioms_before = axioms ();;
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

let rec ceil_integer_sqrt_from value n =
  let integer = Num.num_of_int n in
  if Num.le_num value (Num.mul_num integer integer) then n
  else ceil_integer_sqrt_from value (n + 1);;

let floor_sqrt_scaled value =
  let integer_ceiling = ceil_integer_sqrt_from value 0 in
  floor_scaled_sqrt value 0 ((integer_ceiling + 1) * scale_int);;

let ceil_sqrt_scaled value =
  let lower = floor_sqrt_scaled value in
  if Num.eq_num (scaled_square lower) value then lower else lower + 1;;

let scaled_num n = Num.div_num (Num.num_of_int n) scale;;

let make_sqrt_interval environment tm =
  let child = candle_q_dest_unary `sqrt:real->real` tm in
  let child_lower,child_upper =
    candle_nl_matan_interval_eval environment child in
  if Num.lt_num child_lower (Num.num_of_int 0) then
    failwith "prep520 acceptance: negative square-root lower bound";
  let lower_scaled = floor_sqrt_scaled child_lower in
  let upper_scaled = ceil_sqrt_scaled child_upper in
  if not (Num.le_num (scaled_square lower_scaled) child_lower) ||
     not (Num.le_num child_upper (scaled_square upper_scaled)) then
    failwith "prep520 acceptance: square-root rounding drift";
  mk_pair
    (candle_q_term (scaled_num lower_scaled),
     candle_q_term (scaled_num upper_scaled));;

let encode_program expression =
  let compile_theorem =
    REWRITE_CONV
      [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
      (mk_comb (`candle_analytic_compile`,expression)) in
  let program = rand (concl compile_theorem) in
  let representation =
    REWRITE_CONV
      [candle_cv_analytic_instruction_list_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
       candle_analytic_sqrt_interval_def;
       candle_cv_q_interval_def; candle_cv_q_def; candle_cv_lc_z_def;
       FST; SND]
      (mk_comb (`candle_cv_analytic_instruction_list`,program)) in
  if hyp compile_theorem <> [] || hyp representation <> [] then
    failwith "prep520 acceptance: program encoding assumptions";
  rand (concl representation),length (dest_list program);;

let encode_boxes lower upper =
  let boxes =
    mk_list
      (map2
        (fun lo hi -> mk_pair (candle_q_term lo,candle_q_term hi))
        lower upper,
       candle_q_interval_type) in
  let representation =
    REWRITE_CONV
      [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
       candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
      (mk_comb (`candle_cv_q_interval_list`,boxes)) in
  if hyp representation <> [] then
    failwith "prep520 acceptance: box encoding assumptions";
  rand (concl representation);;

let prepare_branch lower upper function_term =
  let vector,source = dest_abs function_term in
  let vector_application = mk_icomb (`$`,vector) in
  let vector_variables =
    map
      (fun index -> mk_comb (vector_application,mk_small_numeral index))
      (1--6) in
  let center =
    map2
      (fun lo hi ->
        Num.div_num (Num.add_num lo hi) (Num.num_of_int 2))
      lower upper in
  let box_environment = zip vector_variables (zip lower upper) in
  let center_environment =
    zip vector_variables (map (fun value -> value,value) center) in
  let box_expression,box_source_theorem =
    candle_analytic_reify_real_expression
      (make_sqrt_interval box_environment) vector_variables source in
  let center_expression,center_source_theorem =
    candle_analytic_reify_real_expression
      (make_sqrt_interval center_environment) vector_variables source in
  let box_erased =
    mk_comb (`candle_analytic_erase_sqrt_certificates`,box_expression) in
  let center_erased =
    mk_comb (`candle_analytic_erase_sqrt_certificates`,center_expression) in
  let erased_equality =
    REWRITE_CONV
      [candle_analytic_erase_sqrt_certificates_def]
      (mk_eq (center_erased,box_erased)) in
  let valid_theorem = prove
   (list_mk_comb (`candle_analytic_valid_dim`,[`6`;box_expression]),
    REWRITE_TAC[candle_analytic_valid_dim_def; candle_poly_valid_dim_def] THEN
    CONV_TAC NUM_REDUCE_CONV) in
  let center_program,center_instructions = encode_program center_expression in
  let box_program,box_instructions = encode_program box_expression in
  if center_instructions <> box_instructions ||
     hyp box_source_theorem <> [] || hyp center_source_theorem <> [] ||
     hyp erased_equality <> [] || hyp valid_theorem <> [] ||
     rand (concl erased_equality) <> `T` then
    failwith "prep520 acceptance: reification contract mismatch";
  center_program,box_program,center_instructions;;

let run_component index plan =
  let _,_,_,_,_,_,lower,upper,_,_,_,_,functions = plan in
  let boxes = encode_boxes lower upper in
  let run_branch branch function_term =
    let started_prepare = Unix.gettimeofday () in
    let center_program,box_program,instructions =
      prepare_branch lower upper function_term in
    let prepare_seconds = Unix.gettimeofday () -. started_prepare in
    let started_compute = Unix.gettimeofday () in
    let compute_theorem =
      Kernel.compute
        (COMPUTE_INIT_THMS,candle_cv_matan_fs_taylor_handoff_compute_eqs)
        (list_mk_comb
          (`candle_cv_matan_fs_taylor_dual_check`,
           [center_program;box_program;boxes])) in
    let compute_seconds = Unix.gettimeofday () -. started_compute in
    let result = rand (concl compute_theorem) in
    let result_operator,result_arguments = strip_comb result in
    let flag,diagnostic =
      if aconv result_operator `Cexp_pair` then
        match result_arguments with
        | [flag;diagnostic] -> flag,diagnostic
        | _ -> failwith "prep520 acceptance: malformed checker pair"
      else failwith "prep520 acceptance: checker did not return a pair" in
    let verdict =
      if aconv flag `Cexp_num 1` then "accept"
      else if aconv flag `Cexp_num 0` then "reject"
      else failwith "prep520 acceptance: unexpected checker result" in
    if hyp compute_theorem <> [] then
      failwith "prep520 acceptance: compute assumptions";
    print_endline
      ("CANDLE_CV_MATAN_PREP520_PARTITION_BRANCH" ^
       " DEVELOPMENT_NON_RELEASE component=" ^ string_of_int index ^
       " branch=" ^ string_of_int branch ^
       " instructions=" ^ string_of_int instructions ^
       " verdict=" ^ verdict ^
       " diagnostic=" ^ string_of_term diagnostic ^
       " prepare_seconds=" ^ string_of_float prepare_seconds ^
       " compute_seconds=" ^ string_of_float compute_seconds ^
       " assumptions=0");
    verdict in
  map2 run_branch (0--1) functions;;

let verdicts = map2 run_component (0--3) plans;;
let accepted_components =
  length
    (filter
      (fun component_verdicts -> mem "accept" component_verdicts)
      verdicts);;

let axioms_after = axioms ();;
if length verdicts <> 4 ||
   length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "prep520 acceptance: final contract mismatch";;

print_endline
  ("CANDLE_CV_MATAN_PREP520_PARTITION_ACCEPTANCE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " components=4 accepted_components=" ^ string_of_int accepted_components ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_PREP520_PARTITION_ACCEPTANCE_OK";;

end;;
