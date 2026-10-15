(* ========================================================================== *)
(* Fixed-scale Taylor handoff on one complete genuine Flyspeck [matan] root. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Exact reflected execution authenticates the   *)
(* complete analytic center and box jets.  Only the final Taylor aggregation  *)
(* is outward-rounded to a 10^-12 integer scale.  The numerical verdict is a *)
(* development result until the companion handoff soundness theorem lands.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_check.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_compute.ml";;
needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_check;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_compute;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare;;

module Test_cv_compute_analytic_expr_matan_genuine_root_fixed_handoff = struct

let axioms_before = axioms ();;

let q_interval lower upper =
  mk_pair
    (candle_q_term (rat_of_term lower),
     candle_q_term (rat_of_term upper));;
let boxes =
  mk_list (map2 q_interval lower upper,candle_q_interval_type);;
let boxes_representation =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;
let boxes_representation_term = rand (concl boxes_representation);;
let program_representation_term =
  rand (concl tight_program_representation);;

let compute equations phase term =
  print_endline
    ("CANDLE_CV_MATAN_GENUINE_ROOT_FIXED_HANDOFF_STAGE " ^ phase ^
     "-begin");
  let theorem = Kernel.compute (COMPUTE_INIT_THMS,equations) term in
  if hyp theorem <> [] then
    failwith ("genuine matan fixed handoff: assumptions in " ^ phase);
  print_endline
    ("CANDLE_CV_MATAN_GENUINE_ROOT_FIXED_HANDOFF_STAGE " ^ phase ^
     "-end");
  theorem;;

let center_environment_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "center-environment"
    (mk_comb
      (`candle_cv_q_center_environment_list`,boxes_representation_term));;
let center_environment = rand (concl center_environment_theorem);;

let center_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "center-full-jet"
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [center_environment;program_representation_term]));;
let center = rand (concl center_theorem);;

let box_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "box-full-jet"
    (list_mk_comb
      (`candle_cv_q_dim_analytic_program`,
       [boxes_representation_term;program_representation_term]));;
let box = rand (concl box_theorem);;

let domain_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "domain-combine"
    (list_mk_comb
      (`candle_cv_bool_and`,
       [mk_comb (`candle_cv_q_dim_analytic_result_domain`,center);
        mk_comb (`candle_cv_q_dim_analytic_result_domain`,box)]));;
let domain = rand (concl domain_theorem);;

let center_value_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "center-value"
    (mk_comb
      (`candle_cv_q_dim_jet_f`,
       mk_comb (`candle_cv_q_dim_analytic_result_jet`,center)));;
let center_value = rand (concl center_value_theorem);;

let center_gradient_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "center-gradient"
    (mk_comb
      (`candle_cv_q_dim_jet_gradient`,
       mk_comb (`candle_cv_q_dim_analytic_result_jet`,center)));;
let center_gradient = rand (concl center_gradient_theorem);;

let box_hessian_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "box-hessian"
    (mk_comb
      (`candle_cv_q_dim_jet_hessian`,
       mk_comb (`candle_cv_q_dim_analytic_result_jet`,box)));;
let box_hessian = rand (concl box_hessian_theorem);;

let box_valid_theorem =
  compute candle_cv_q_dim_analytic_jet_compute_eqs "box-valid"
    (mk_comb (`candle_cv_q_box_valid_list`,boxes_representation_term));;
let box_valid = rand (concl box_valid_theorem);;

let radii_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "exact-radii"
    (mk_comb (`candle_cv_q_radius_list`,boxes_representation_term));;
let radii = rand (concl radii_theorem);;

let value_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "fixed-value-upper"
    (mk_comb
      (`candle_cv_matan_fs_q_upper`,mk_comb (`Cexp_snd`,center_value)));;
let value = rand (concl value_theorem);;

let gradient_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "fixed-gradient-upper"
    (mk_comb
      (`candle_cv_matan_fs_q_abs_upper`,
       list_mk_comb
         (`candle_cv_q_dot_abs_upper`,[radii;center_gradient])));;
let gradient = rand (concl gradient_theorem);;

let weighted_rows_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs
    "fixed-weighted-rows-upper"
    (list_mk_comb
      (`candle_cv_matan_fs_weighted_rows_upper`,
       [radii;radii;box_hessian]));;
let weighted_rows = rand (concl weighted_rows_theorem);;

let hessian_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "fixed-hessian-half"
    (list_mk_comb
      (`candle_cv_matan_fs_ceil_div`,[weighted_rows;`Cexp_num 2`]));;
let hessian = rand (concl hessian_theorem);;

let positive_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "fixed-positive-sum"
    (list_mk_comb (`Cexp_add`,[gradient;hessian]));;
let positive = rand (concl positive_theorem);;

let upper_positive_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "fixed-final-upper"
    (list_mk_comb
      (`Cexp_add`,[mk_comb (`Cexp_fst`,value);positive]));;
let upper_positive = rand (concl upper_positive_theorem);;

let value_positive,value_negative =
  let partial,right = dest_comb value in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "genuine matan fixed handoff: value is not a pair";;

let cexp_num_string tm =
  let operator,numeral = dest_comb tm in
  if aconv operator `Cexp_num` then
    Num.string_of_num (dest_numeral numeral)
  else failwith "genuine matan fixed handoff: expected Cexp_num";;

let verdict_theorem =
  compute candle_cv_matan_fs_taylor_handoff_compute_eqs "fixed-verdict"
    (list_mk_comb
      (`Cexp_if`,
       [domain;
        list_mk_comb
          (`Cexp_if`,
           [box_valid;
            list_mk_comb
              (`Cexp_less`,[upper_positive;mk_comb (`Cexp_snd`,value)]);
            `Cexp_num 0`]);
        `Cexp_num 0`]));;
let verdict = rand (concl verdict_theorem);;
let upper = list_mk_comb (`Cexp_pair`,[upper_positive;mk_comb (`Cexp_snd`,value)]);;
let accepted = aconv verdict `Cexp_num 1`;;

if hyp tight_source_theorem <> [] || hyp tight_valid_theorem <> [] ||
   hyp boxes_representation <> [] || hyp center_theorem <> [] ||
   hyp box_theorem <> [] || hyp weighted_rows_theorem <> [] ||
   hyp verdict_theorem <> [] then
  failwith "genuine matan fixed handoff: theorem assumptions";;

let axioms_after = axioms ();;
if length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan fixed handoff: changed the global axiom set";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ROOT_FIXED_HANDOFF_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " historical_cells=1 historical_glue=0" ^
   " instructions=" ^ string_of_int tight_instruction_count ^
   " sqrt_scale=" ^ string_of_int scale_int ^
   " taylor_scale=1000000000000" ^
   " verdict=" ^ (if accepted then "accept" else "reject") ^
   " value_positive=" ^ cexp_num_string value_positive ^
   " value_negative=" ^ cexp_num_string value_negative ^
   " gradient=" ^ cexp_num_string gradient ^
   " weighted_rows=" ^ cexp_num_string weighted_rows ^
   " hessian=" ^ cexp_num_string hessian ^
   " upper_positive=" ^ cexp_num_string upper_positive ^
   " upper_chars=" ^ string_of_int (String.length (string_of_term upper)) ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_GENUINE_ROOT_FIXED_HANDOFF_OK";;

end;;
