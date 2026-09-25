(* ========================================================================== *)
(* Constant/variable Taylor-model completion probe on the action-296 box.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This isolates the complete six-dimensional   *)
(* leaf constructors used by the genuine reflected program.  Center boxes   *)
(* and rounded radii are computed once; each timed phase then evaluates 64   *)
(* identical result constructors so fixed evaluator setup is amortized.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;

let candle_action296_completion_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf-completion scope=repeat-64" ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_completion_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_completion_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 completion: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 completion: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_completion_find left_domain left
  | P_result_mono _ ->
      failwith "action296 completion: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 completion: unexpected reference node";;

let candle_action296_completion_parent_domain =
  candle_action296_completion_find
    candle_action296_completion_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_completion_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_completion_parent_domain;;

let candle_action296_completion_domain_pair,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_completion_probe_domain);;
let candle_action296_completion_actual_lower,
    candle_action296_completion_actual_upper =
  dest_pair candle_action296_completion_domain_pair;;
let candle_action296_completion_lower,_ =
  candle_reflected_nl_normalize_vector
    candle_action296_completion_actual_lower;;
let candle_action296_completion_upper,_ =
  candle_reflected_nl_normalize_vector
    candle_action296_completion_actual_upper;;
let candle_action296_completion_boxes =
  candle_poly_fixture_q_boxes
    candle_action296_completion_lower candle_action296_completion_upper;;
let candle_action296_completion_boxes_representation =
  candle_q_dim_analytic_jet_boxes_encode_conv
    candle_action296_completion_boxes;;
let candle_action296_completion_boxes_term =
  rand (concl candle_action296_completion_boxes_representation);;

let candle_action296_completion_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_taylor_model_compute_eqs tm;;

let _ =
  candle_action296_completion_marker "shared-inputs" "begin";;
let candle_action296_completion_centers =
  candle_action296_completion_compute
    (mk_comb
      (`candle_cv_q_center_environment_list`,
       candle_action296_completion_boxes_term));;
let candle_action296_completion_radii =
  candle_action296_completion_compute
    (mk_comb
      (`candle_cv_q_fixed_list_round_upper`,
       mk_comb
         (`candle_cv_q_radius_list`,
          candle_action296_completion_boxes_term)));;
let _ =
  candle_action296_completion_marker "shared-inputs" "end";;

let candle_action296_completion_centers_term =
  rand (concl candle_action296_completion_centers);;
let candle_action296_completion_radii_term =
  rand (concl candle_action296_completion_radii);;
let candle_action296_completion_one =
  `Cexp_pair (Cexp_pair (Cexp_num 1) (Cexp_num 0)) (Cexp_num 0)`;;
let candle_action296_completion_repetitions =
  itlist
    (fun _ tail -> list_mk_comb (`Cexp_pair`,[`Cexp_num 0`;tail]))
    (1--64) `Cexp_num 0`;;

let candle_cv_action296_completion_size_def = define
 `(candle_cv_action296_completion_size (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_action296_completion_size (Cexp_pair h t) =
     Cexp_add (candle_cv_action296_completion_size h)
       (candle_cv_action296_completion_size t))`;;

let candle_cv_action296_completion_size_compute = prove
 (`!value.
     candle_cv_action296_completion_size value =
     Cexp_if (Cexp_ispair value)
       (Cexp_add
         (candle_cv_action296_completion_size (Cexp_fst value))
         (candle_cv_action296_completion_size (Cexp_snd value)))
       (Cexp_num 1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `value:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_completion_size_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_action296_completion_constant_repeat_def = define
 `(candle_cv_action296_completion_constant_repeat
      center_boxes boxes radii q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_completion_constant_repeat
      center_boxes boxes radii q (Cexp_pair h t) =
    Cexp_add
      (candle_cv_action296_completion_size
        (candle_cv_q_dim_taylor_model_poly_constant
          center_boxes boxes radii q))
      (candle_cv_action296_completion_constant_repeat
        center_boxes boxes radii q t))`;;

let candle_cv_action296_completion_constant_repeat_compute = prove
 (`!center_boxes boxes radii q count.
     candle_cv_action296_completion_constant_repeat
       center_boxes boxes radii q count =
     Cexp_if (Cexp_ispair count)
       (Cexp_add
         (candle_cv_action296_completion_size
           (candle_cv_q_dim_taylor_model_poly_constant
             center_boxes boxes radii q))
         (candle_cv_action296_completion_constant_repeat
           center_boxes boxes radii q (Cexp_snd count)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_completion_constant_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_action296_completion_variable_repeat_def = define
 `(candle_cv_action296_completion_variable_repeat
      center_boxes boxes radii variable (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_completion_variable_repeat
      center_boxes boxes radii variable (Cexp_pair h t) =
    Cexp_add
      (candle_cv_action296_completion_size
        (candle_cv_q_dim_taylor_model_poly_variable
          center_boxes boxes radii variable))
      (candle_cv_action296_completion_variable_repeat
        center_boxes boxes radii variable t))`;;

let candle_cv_action296_completion_variable_repeat_compute = prove
 (`!center_boxes boxes radii variable count.
     candle_cv_action296_completion_variable_repeat
       center_boxes boxes radii variable count =
     Cexp_if (Cexp_ispair count)
       (Cexp_add
         (candle_cv_action296_completion_size
           (candle_cv_q_dim_taylor_model_poly_variable
             center_boxes boxes radii variable))
         (candle_cv_action296_completion_variable_repeat
           center_boxes boxes radii variable (Cexp_snd count)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `count:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_completion_variable_repeat_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_action296_completion_equations =
  candle_cv_q_dim_taylor_model_compute_eqs @
  map SPEC_ALL
   [candle_cv_action296_completion_size_compute;
    candle_cv_action296_completion_constant_repeat_compute;
    candle_cv_action296_completion_variable_repeat_compute];;

let candle_action296_completion_constant_call =
  list_mk_comb
    (`candle_cv_action296_completion_constant_repeat`,
     [candle_action296_completion_centers_term;
      candle_action296_completion_boxes_term;
      candle_action296_completion_radii_term;
      candle_action296_completion_one;
      candle_action296_completion_repetitions]);;

let candle_action296_completion_variable_call =
  list_mk_comb
    (`candle_cv_action296_completion_variable_repeat`,
     [candle_action296_completion_centers_term;
      candle_action296_completion_boxes_term;
      candle_action296_completion_radii_term;
      `Cexp_num 0`;
      candle_action296_completion_repetitions]);;

let _ = candle_action296_completion_marker "constant" "begin";;
let candle_action296_completion_constant_result =
  candle_q_dim_analytic_jet_compute
    candle_action296_completion_equations
    candle_action296_completion_constant_call;;
let _ = candle_action296_completion_marker "constant" "end";;

let _ = candle_action296_completion_marker "variable" "begin";;
let candle_action296_completion_variable_result =
  candle_q_dim_analytic_jet_compute
    candle_action296_completion_equations
    candle_action296_completion_variable_call;;
let _ = candle_action296_completion_marker "variable" "end";;

if hyp candle_action296_completion_constant_result <> [] ||
   hyp candle_action296_completion_variable_result <> [] then
  failwith "action296 completion: computed theorem assumptions";;

print_endline
  ("CANDLE_CV_ACTION296_LEAF_COMPLETION_RESULT repeats=64 dimensions=6" ^
   " program_instructions=" ^
   string_of_int candle_action296_plan_instruction_count);;
print_endline
  "CANDLE_CV_ACTION296_LEAF_COMPLETION_OK DEVELOPMENT_NON_RELEASE";;
