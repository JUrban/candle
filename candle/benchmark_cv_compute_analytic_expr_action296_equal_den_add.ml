(* ========================================================================== *)
(* Equal-denominator rational-addition discriminator on genuine action 296. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Eight distinct accepted cells are evaluated  *)
(* by the retained centered Taylor program.  Rational pairs are then sampled *)
(* from those exact computed results.  The candidate avoids denominator      *)
(* cross-products when the two denominator predecessors are identical, but   *)
(* still passes the result through the unchanged checked normalizer.          *)
(*                                                                            *)
(* The candidate may only be interesting if every normalized output is       *)
(* structurally identical to the production result and the genuine reflected *)
(* batch is materially faster than the same-input production operation.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_normalize;;

let candle_action296_equal_den_add_axioms_before = axioms ();;

let candle_action296_equal_den_add_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-equal-den-add scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_action296_equal_den_add_marker "batch" "profiled-run" "begin";;

let candle_action296_equal_den_add_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_equal_den_add_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 equal-den add: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 equal-den add: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_equal_den_add_find left_domain left
  | P_result_mono _ ->
      failwith "action296 equal-den add: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 equal-den add: unexpected reference node";;

let candle_action296_equal_den_add_parent_domain =
  candle_action296_equal_den_add_find
    candle_action296_equal_den_add_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_equal_den_add_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_equal_den_add_parent_domain;;

let candle_action296_equal_den_add_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_equal_den_add_probe_lower,
    candle_action296_equal_den_add_probe_upper =
  candle_action296_equal_den_add_domain_bounds
    candle_action296_equal_den_add_probe_domain;;

let _ =
  candle_action296_equal_den_add_marker
    "shared" "whole-box-source-preparation" "begin";;
let candle_action296_equal_den_add_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_equal_den_add_probe_lower
    candle_action296_equal_den_add_probe_upper;;
let _ =
  candle_action296_equal_den_add_marker
    "shared" "whole-box-source-preparation" "end";;

let candle_action296_equal_den_add_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_equal_den_add_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_equal_den_add_subdivide remaining
        (List.flatten
          (map (candle_action296_equal_den_add_split axis) domains));;

let candle_action296_equal_den_add_domains =
  candle_action296_equal_den_add_subdivide [1;2;3]
    [candle_action296_equal_den_add_probe_domain];;

let _ =
  candle_action296_equal_den_add_marker
    "shared" "center-variant-preparation" "begin";;
let candle_action296_equal_den_add_cases =
  map
    (fun domain_th ->
      let lower,upper =
        candle_action296_equal_den_add_domain_bounds domain_th in
      let variant =
        candle_q_dim_taylor_model_prepare_point_variant_six
          candle_action296_equal_den_add_box_prepared lower upper in
      variant,lower,upper)
    candle_action296_equal_den_add_domains;;
let _ =
  candle_action296_equal_den_add_marker
    "shared" "center-variant-preparation" "end";;

let candle_action296_equal_den_add_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_taylor_model_certified_compute_eqs tm;;

let candle_action296_equal_den_add_capture (variant,lower,upper) =
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let boxes_term = rand (concl boxes_representation) in
  let result_th =
    candle_action296_equal_den_add_compute
      (list_mk_comb
        (`candle_cv_q_dim_taylor_model_program`,
         [variant.variant_program_representation_term;
          candle_action296_equal_den_add_box_prepared.
            program_representation_term;
          boxes_term])) in
  let result = rand (concl result_th) in
  let finish_th =
    candle_action296_equal_den_add_compute
      (list_mk_comb
        (`candle_cv_q_dim_taylor_model_certified_finish`,
         [boxes_term;result])) in
  let flag,_ =
    candle_q_dim_analytic_jet_dest_pair (rand (concl finish_th)) in
  if hyp result_th <> [] || hyp finish_th <> [] ||
     not (aconv flag `Cexp_num 1`) then
    failwith "action296 equal-den add: genuine result did not accept";
  result;;

let _ =
  candle_action296_equal_den_add_marker
    "boxes-8" "genuine-one-shot-capture" "begin";;
let candle_action296_equal_den_add_results =
  map candle_action296_equal_den_add_capture
    candle_action296_equal_den_add_cases;;
let _ =
  candle_action296_equal_den_add_marker
    "boxes-8" "genuine-one-shot-capture" "end";;

type candle_action296_equal_den_add_cval =
  | Candle_action296_equal_den_add_num of num
  | Candle_action296_equal_den_add_pair of term * term;;

let candle_action296_equal_den_add_view tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [argument] ->
        Candle_action296_equal_den_add_num (dest_numeral argument)
    | _ -> failwith "action296 equal-den add: malformed Cexp_num"
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [left;right] -> Candle_action296_equal_den_add_pair (left,right)
    | _ -> failwith "action296 equal-den add: malformed Cexp_pair"
  else failwith "action296 equal-den add: non-concrete cval";;

let rec candle_action296_equal_den_add_collect_rationals tm =
  match candle_action296_equal_den_add_view tm with
  | Candle_action296_equal_den_add_num _ -> []
  | Candle_action296_equal_den_add_pair (left,right) ->
      (match candle_action296_equal_den_add_view left,
             candle_action296_equal_den_add_view right with
       | Candle_action296_equal_den_add_pair
           (positive_term,negative_term),
         Candle_action296_equal_den_add_num _ ->
           (match candle_action296_equal_den_add_view positive_term,
                  candle_action296_equal_den_add_view negative_term with
            | Candle_action296_equal_den_add_num _,
              Candle_action296_equal_den_add_num _ -> [tm]
            | _ ->
                candle_action296_equal_den_add_collect_rationals left @
                candle_action296_equal_den_add_collect_rationals right)
       | _ ->
           candle_action296_equal_den_add_collect_rationals left @
           candle_action296_equal_den_add_collect_rationals right);;

let rec candle_action296_equal_den_add_pair_adjacent = function
  | left :: right :: tail ->
      (left,right) :: candle_action296_equal_den_add_pair_adjacent tail
  | [] -> []
  | _ -> failwith "action296 equal-den add: odd rational cardinality";;

let candle_action296_equal_den_add_base_pairs =
  List.flatten
    (map
      (fun result ->
        let rationals =
          candle_action296_equal_den_add_collect_rationals result in
        if length rationals <> 100 then
          failwith "action296 equal-den add: result rational shape drift";
        candle_action296_equal_den_add_pair_adjacent rationals)
      candle_action296_equal_den_add_results);;

let candle_action296_equal_den_add_dest_q tm =
  match candle_action296_equal_den_add_view tm with
  | Candle_action296_equal_den_add_pair (z,denominator_predecessor) ->
      (match candle_action296_equal_den_add_view z,
             candle_action296_equal_den_add_view denominator_predecessor with
       | Candle_action296_equal_den_add_pair
           (positive_term,negative_term),
         Candle_action296_equal_den_add_num predecessor ->
           (match candle_action296_equal_den_add_view positive_term,
                  candle_action296_equal_den_add_view negative_term with
            | Candle_action296_equal_den_add_num positive,
              Candle_action296_equal_den_add_num negative ->
                positive,negative,
                Num.add_num predecessor (Num.num_of_int 1)
            | _ -> failwith "action296 equal-den add: malformed signed q")
       | _ -> failwith "action296 equal-den add: malformed q")
  | _ -> failwith "action296 equal-den add: expected q";;

let candle_action296_equal_den_add_num_bits value =
  let zero = Num.num_of_int 0 and two = Num.num_of_int 2 in
  let rec loop n bits =
    if Num.eq_num n zero then bits
    else loop (Num.quo_num n two) (bits + 1) in
  loop value 0;;

let candle_action296_equal_den_add_gcd_steps numerator denominator =
  let zero = Num.num_of_int 0 in
  let rec loop steps a b =
    if Num.eq_num b zero then steps
    else loop (steps + 1) b (Num.mod_num a b) in
  loop 0 numerator denominator;;

let candle_action296_equal_den_add_host_profile pairs =
  let count = ref 0 and old_steps = ref 0 and fast_steps = ref 0 and
      old_max_steps = ref 0 and fast_max_steps = ref 0 and
      old_max_numerator_bits = ref 0 and fast_max_numerator_bits = ref 0 and
      old_max_denominator_bits = ref 0 and fast_max_denominator_bits = ref 0 in
  let update maximum value = if value > !maximum then maximum := value in
  map
    (fun (left,right) ->
      let lp,ln,ld = candle_action296_equal_den_add_dest_q left and
          rp,rn,rd = candle_action296_equal_den_add_dest_q right in
      if not (Num.eq_num ld rd) ||
         Num.string_of_num ld <> "1000000000000" then
        failwith "action296 equal-den add: non-shared scale";
      let old_positive =
        Num.add_num (Num.mul_num lp rd) (Num.mul_num rp ld) and
          old_negative =
            Num.add_num (Num.mul_num ln rd) (Num.mul_num rn ld) and
          old_denominator = Num.mul_num ld rd and
          fast_positive = Num.add_num lp rp and
          fast_negative = Num.add_num ln rn in
      let old_numerator =
        Num.abs_num (Num.sub_num old_positive old_negative) and
          fast_numerator =
            Num.abs_num (Num.sub_num fast_positive fast_negative) in
      let old_pair_steps =
        candle_action296_equal_den_add_gcd_steps
          old_numerator old_denominator and
          fast_pair_steps =
            candle_action296_equal_den_add_gcd_steps fast_numerator ld in
      count := !count + 1;
      old_steps := !old_steps + old_pair_steps;
      fast_steps := !fast_steps + fast_pair_steps;
      update old_max_steps old_pair_steps;
      update fast_max_steps fast_pair_steps;
      update old_max_numerator_bits
        (candle_action296_equal_den_add_num_bits old_numerator);
      update fast_max_numerator_bits
        (candle_action296_equal_den_add_num_bits fast_numerator);
      update old_max_denominator_bits
        (candle_action296_equal_den_add_num_bits old_denominator);
      update fast_max_denominator_bits
        (candle_action296_equal_den_add_num_bits ld))
    pairs;
  print_endline
    ("CANDLE_CV_ACTION296_EQUAL_DEN_ADD_HOST_PROFILE pairs=" ^
     string_of_int !count ^
     " old_gcd_steps_total=" ^ string_of_int !old_steps ^
     " fast_gcd_steps_total=" ^ string_of_int !fast_steps ^
     " old_gcd_steps_max=" ^ string_of_int !old_max_steps ^
     " fast_gcd_steps_max=" ^ string_of_int !fast_max_steps ^
     " old_numerator_bits_max=" ^
       string_of_int !old_max_numerator_bits ^
     " fast_numerator_bits_max=" ^
       string_of_int !fast_max_numerator_bits ^
     " old_denominator_bits_max=" ^
       string_of_int !old_max_denominator_bits ^
     " fast_denominator_bits_max=" ^
       string_of_int !fast_max_denominator_bits);;

let _ =
  candle_action296_equal_den_add_marker
    "pairs-400" "host-arithmetic-profile" "begin";;
let _ =
  candle_action296_equal_den_add_host_profile
    candle_action296_equal_den_add_base_pairs;;
let _ =
  candle_action296_equal_den_add_marker
    "pairs-400" "host-arithmetic-profile" "end";;

let rec candle_action296_equal_den_add_repeat count items accumulator =
  if count <= 0 then accumulator
  else
    candle_action296_equal_den_add_repeat (count - 1) items
      (items @ accumulator);;

let candle_action296_equal_den_add_benchmark_pairs =
  candle_action296_equal_den_add_repeat 16
    candle_action296_equal_den_add_base_pairs [];;

let candle_action296_equal_den_add_pair_term (left,right) =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_action296_equal_den_add_pair_list_term pairs =
  itlist
    (fun pair tail ->
      list_mk_comb
        (`Cexp_pair`,
         [candle_action296_equal_den_add_pair_term pair;tail]))
    pairs `Cexp_num 0`;;

let candle_action296_equal_den_add_base_term =
  candle_action296_equal_den_add_pair_list_term
    candle_action296_equal_den_add_base_pairs;;

let candle_action296_equal_den_add_benchmark_term =
  candle_action296_equal_den_add_pair_list_term
    candle_action296_equal_den_add_benchmark_pairs;;

let candle_cv_q_add_equal_den_candidate_def = new_definition
 `candle_cv_q_add_equal_den_candidate x y =
    Cexp_if (Cexp_eq (Cexp_snd x) (Cexp_snd y))
      (Cexp_pair
        (candle_cv_lc_zadd (Cexp_fst x) (Cexp_fst y))
        (Cexp_snd x))
      (candle_cv_q_add x y)`;;

let candle_cv_q_add_equal_den_normalized_candidate_def = new_definition
 `candle_cv_q_add_equal_den_normalized_candidate x y =
    candle_cv_q_normalize (candle_cv_q_add_equal_den_candidate x y)`;;

let candle_cv_q_add_equal_den_checksum_def = new_definition
 `candle_cv_q_add_equal_den_checksum q =
    Cexp_mod
      (Cexp_add
        (Cexp_add (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
        (Cexp_snd q))
      (Cexp_num 1000003)`;;

let candle_cv_q_add_equal_den_baseline_def = define
 `(candle_cv_q_add_equal_den_baseline (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_add_equal_den_baseline (Cexp_pair h t) =
     Cexp_add
       (Cexp_add
         (candle_cv_q_add_equal_den_checksum (Cexp_fst h))
         (candle_cv_q_add_equal_den_checksum (Cexp_snd h)))
       (candle_cv_q_add_equal_den_baseline t))`;;

let candle_cv_q_add_equal_den_old_def = define
 `(candle_cv_q_add_equal_den_old (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_add_equal_den_old (Cexp_pair h t) =
     Cexp_add
       (candle_cv_q_add_equal_den_checksum
         (candle_cv_q_add_normalized (Cexp_fst h) (Cexp_snd h)))
       (candle_cv_q_add_equal_den_old t))`;;

let candle_cv_q_add_equal_den_fast_def = define
 `(candle_cv_q_add_equal_den_fast (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_add_equal_den_fast (Cexp_pair h t) =
     Cexp_add
       (candle_cv_q_add_equal_den_checksum
         (candle_cv_q_add_equal_den_normalized_candidate
           (Cexp_fst h) (Cexp_snd h)))
       (candle_cv_q_add_equal_den_fast t))`;;

let candle_cv_q_add_equal_den_exact_def = define
 `(candle_cv_q_add_equal_den_exact (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_q_add_equal_den_exact (Cexp_pair h t) =
     Cexp_if
       (Cexp_eq
         (candle_cv_q_add_normalized (Cexp_fst h) (Cexp_snd h))
         (candle_cv_q_add_equal_den_normalized_candidate
           (Cexp_fst h) (Cexp_snd h)))
       (candle_cv_q_add_equal_den_exact t) (Cexp_num 0))`;;

let candle_cv_q_add_equal_den_baseline_compute = prove
 (`!pairs.
     candle_cv_q_add_equal_den_baseline pairs =
     Cexp_if (Cexp_ispair pairs)
       (Cexp_add
         (Cexp_add
           (candle_cv_q_add_equal_den_checksum
             (Cexp_fst (Cexp_fst pairs)))
           (candle_cv_q_add_equal_den_checksum
             (Cexp_snd (Cexp_fst pairs))))
         (candle_cv_q_add_equal_den_baseline (Cexp_snd pairs)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `pairs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_add_equal_den_baseline_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_add_equal_den_old_compute = prove
 (`!pairs.
     candle_cv_q_add_equal_den_old pairs =
     Cexp_if (Cexp_ispair pairs)
       (Cexp_add
         (candle_cv_q_add_equal_den_checksum
           (candle_cv_q_add_normalized
             (Cexp_fst (Cexp_fst pairs))
             (Cexp_snd (Cexp_fst pairs))))
         (candle_cv_q_add_equal_den_old (Cexp_snd pairs)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `pairs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_add_equal_den_old_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_add_equal_den_fast_compute = prove
 (`!pairs.
     candle_cv_q_add_equal_den_fast pairs =
     Cexp_if (Cexp_ispair pairs)
       (Cexp_add
         (candle_cv_q_add_equal_den_checksum
           (candle_cv_q_add_equal_den_normalized_candidate
             (Cexp_fst (Cexp_fst pairs))
             (Cexp_snd (Cexp_fst pairs))))
         (candle_cv_q_add_equal_den_fast (Cexp_snd pairs)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `pairs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_add_equal_den_fast_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_add_equal_den_exact_compute = prove
 (`!pairs.
     candle_cv_q_add_equal_den_exact pairs =
     Cexp_if (Cexp_ispair pairs)
       (Cexp_if
         (Cexp_eq
           (candle_cv_q_add_normalized
             (Cexp_fst (Cexp_fst pairs))
             (Cexp_snd (Cexp_fst pairs)))
           (candle_cv_q_add_equal_den_normalized_candidate
             (Cexp_fst (Cexp_fst pairs))
             (Cexp_snd (Cexp_fst pairs))))
         (candle_cv_q_add_equal_den_exact (Cexp_snd pairs))
         (Cexp_num 0))
       (Cexp_num 1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `pairs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_add_equal_den_exact_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_action296_equal_den_add_equations =
  union candle_cv_q_dim_taylor_model_certified_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_add_equal_den_candidate_def;
       candle_cv_q_add_equal_den_normalized_candidate_def;
       candle_cv_q_add_equal_den_checksum_def;
       candle_cv_q_add_equal_den_baseline_compute;
       candle_cv_q_add_equal_den_old_compute;
       candle_cv_q_add_equal_den_fast_compute;
       candle_cv_q_add_equal_den_exact_compute]);;

let candle_action296_equal_den_add_run phase constant argument =
  candle_action296_equal_den_add_marker "pairs-6400" phase "begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_action296_equal_den_add_equations
      (mk_comb (constant,argument)) in
  candle_action296_equal_den_add_marker "pairs-6400" phase "end";
  theorem;;

let candle_action296_equal_den_add_baseline =
  candle_action296_equal_den_add_run "baseline-traversal"
    `candle_cv_q_add_equal_den_baseline`
    candle_action296_equal_den_add_benchmark_term;;

let candle_action296_equal_den_add_old =
  candle_action296_equal_den_add_run "production-normalized-add"
    `candle_cv_q_add_equal_den_old`
    candle_action296_equal_den_add_benchmark_term;;

let candle_action296_equal_den_add_fast =
  candle_action296_equal_den_add_run "candidate-normalized-add"
    `candle_cv_q_add_equal_den_fast`
    candle_action296_equal_den_add_benchmark_term;;

(* Repeat in the opposite candidate/production order so a warm second call *)
(* cannot by itself decide the comparison.                                   *)

let candle_action296_equal_den_add_fast_repeat =
  candle_action296_equal_den_add_run "candidate-normalized-add-repeat"
    `candle_cv_q_add_equal_den_fast`
    candle_action296_equal_den_add_benchmark_term;;

let candle_action296_equal_den_add_old_repeat =
  candle_action296_equal_den_add_run "production-normalized-add-repeat"
    `candle_cv_q_add_equal_den_old`
    candle_action296_equal_den_add_benchmark_term;;

let _ =
  candle_action296_equal_den_add_marker
    "pairs-400" "exact-result-check" "begin";;
let candle_action296_equal_den_add_exact =
  candle_q_dim_analytic_jet_compute
    candle_action296_equal_den_add_equations
    (mk_comb
      (`candle_cv_q_add_equal_den_exact`,
       candle_action296_equal_den_add_base_term));;
let _ =
  candle_action296_equal_den_add_marker
    "pairs-400" "exact-result-check" "end";;

let candle_action296_equal_den_add_axioms_after = axioms ();;

if length candle_action296_equal_den_add_cases <> 8 ||
   length candle_action296_equal_den_add_base_pairs <> 400 ||
   length candle_action296_equal_den_add_benchmark_pairs <> 6400 ||
   hyp candle_action296_equal_den_add_baseline <> [] ||
   hyp candle_action296_equal_den_add_old <> [] ||
   hyp candle_action296_equal_den_add_fast <> [] ||
   hyp candle_action296_equal_den_add_fast_repeat <> [] ||
   hyp candle_action296_equal_den_add_old_repeat <> [] ||
   hyp candle_action296_equal_den_add_exact <> [] ||
   not
     (aconv (rand (concl candle_action296_equal_den_add_old))
            (rand (concl candle_action296_equal_den_add_fast))) ||
   not
     (aconv (rand (concl candle_action296_equal_den_add_fast_repeat))
            (rand (concl candle_action296_equal_den_add_old_repeat))) ||
   not
     (aconv (rand (concl candle_action296_equal_den_add_exact))
            `Cexp_num 1`) ||
   length candle_action296_equal_den_add_axioms_after <>
     length candle_action296_equal_den_add_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_equal_den_add_axioms_before)
       candle_action296_equal_den_add_axioms_after) then
  failwith "action296 equal-den add: final validation failed";;

let _ =
  candle_action296_equal_den_add_marker "batch" "profiled-run" "end";;

print_endline
  "CANDLE_CV_ACTION296_EQUAL_DEN_ADD_RESULT boxes=8 base_pairs=400 repeats=6400 exact_match=1 accepted=8";;
print_endline
  "CANDLE_CV_ACTION296_EQUAL_DEN_ADD_OK DEVELOPMENT_NON_RELEASE";;
