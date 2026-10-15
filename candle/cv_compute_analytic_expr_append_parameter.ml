(* ========================================================================== *)
(* A reusable logical bridge from a seven-dimensional parameter box to the  *)
(* original six-dimensional Flyspeck source.                                 *)
(*                                                                            *)
(* The extra coordinate is ordinary checker data.  A separately proved      *)
(* enclosure for the exact Flyspeck constant selects that coordinate after   *)
(* the reflected numerical theorem has covered the complete parameter box.   *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

module Candle_cv_analytic_expr_append_parameter = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_reflected_nl_append_parameter = new_definition
 `candle_reflected_nl_append_parameter (x:real^6) (p:real) =
    ((lambda i. if i <= 6 then x$i else p):real^7)`;;

let candle_reflected_nl_append_parameter_dim_six =
  DIMINDEX_CONV `dimindex (:6)`;;

let candle_reflected_nl_append_parameter_dim_seven =
  DIMINDEX_CONV `dimindex (:7)`;;

let candle_reflected_nl_append_parameter_interval = prove
 (`!x l u p pl pu.
     x IN interval [l,u] /\ pl <= p /\ p <= pu
     ==>
     candle_reflected_nl_append_parameter x p IN
       interval
         [candle_reflected_nl_append_parameter l pl,
          candle_reflected_nl_append_parameter u pu]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
  REWRITE_TAC[candle_reflected_nl_append_parameter] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC
    [LAMBDA_BETA;candle_reflected_nl_append_parameter_dim_seven] THEN
  ASM_CASES_TAC `i <= 6` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[candle_reflected_nl_append_parameter_dim_six]);;

let candle_reflected_nl_append_parameter_sound = prove
 (`!f7 f6 l u p pl pu.
     pl <= p /\ p <= pu /\
     (!z. z IN
          interval
            [candle_reflected_nl_append_parameter l pl,
             candle_reflected_nl_append_parameter u pu]
          ==> f7 z < &0) /\
     (!x. f7 (candle_reflected_nl_append_parameter x p) = f6 x)
     ==>
     (!x. x IN interval [l,u] ==> f6 x < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^6` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM (fun source ->
    MP_TAC (SPEC `candle_reflected_nl_append_parameter x p` source)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC candle_reflected_nl_append_parameter_interval THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_reflected_nl_append_parameter_vector components parameter =
  if length components <> 6 then
    failwith "append-parameter bridge: expected six coordinates";
  let six_vector =
    mk_comb (`vector:real list->real^6`,mk_flist components) in
  let seven_vector =
    mk_comb
      (`vector:real list->real^7`,
       mk_flist (components @ [parameter])) in
  let goal =
    mk_eq
      (list_mk_comb
        (`candle_reflected_nl_append_parameter`,[six_vector;parameter]),
       seven_vector) in
  prove
      (goal,
     REWRITE_TAC
       [CART_EQ;candle_reflected_nl_append_parameter_dim_seven] THEN
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     RULE_ASSUM_TAC (REWRITE_RULE[IN_NUMSEG]) THEN
     SUBGOAL_THEN
       `i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7`
       (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
      [ASM_ARITH_TAC;
       ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC
         [candle_reflected_nl_append_parameter;LAMBDA_BETA;vector;
          IN_NUMSEG;ARITH;
          candle_reflected_nl_append_parameter_dim_six;
          candle_reflected_nl_append_parameter_dim_seven] THEN
     CONV_TAC (DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let candle_reflected_nl_append_parameter_source_correspondence
    seven_function six_function parameter =
  let point = `x:real^6` in
  let goal =
    mk_forall
      (point,
       mk_eq
         (mk_comb
           (seven_function,
            list_mk_comb
              (`candle_reflected_nl_append_parameter`,[point;parameter])),
          mk_comb (six_function,point))) in
  let theorem =
    prove
      (goal,
       GEN_TAC THEN
       REWRITE_TAC
         [candle_reflected_nl_append_parameter] THEN
       CONV_TAC (DEPTH_CONV BETA_CONV) THEN
       SIMP_TAC
         [LAMBDA_BETA;IN_NUMSEG;
          candle_reflected_nl_append_parameter_dim_seven;ARITH]) in
  if hyp theorem <> [] then
    failwith "append-parameter bridge: source correspondence assumptions";
  theorem;;

let candle_reflected_nl_append_parameter_prove_box_six
    prepared seven_function six_function parameter parameter_bounds
    lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "append-parameter bridge: expected six box coordinates";
  let bounds_conclusion = concl parameter_bounds in
  let lower_bound,upper_bound = dest_conj bounds_conclusion in
  let parameter_lower,parameter_in_lower = dest_binop `(<=):real->real->bool`
    lower_bound in
  let parameter_in_upper,parameter_upper = dest_binop `(<=):real->real->bool`
    upper_bound in
  if not (aconv parameter parameter_in_lower) ||
     not (aconv parameter parameter_in_upper) ||
     hyp parameter_bounds <> [] then
    failwith "append-parameter bridge: parameter enclosure mismatch";
  let seven_lower = lower @ [parameter_lower] in
  let seven_upper = upper @ [parameter_upper] in
  let seven_theorem =
    candle_q_dim_analytic_jet_prove_box_seven
      prepared seven_lower seven_upper in
  let seven_boxes =
    candle_poly_fixture_q_boxes seven_lower seven_upper in
  let seven_lower_selector =
    `candle_q_box_lower_vector:
       (((num#num)#num)#((num#num)#num))list->real^7` in
  let seven_upper_selector =
    `candle_q_box_upper_vector:
       (((num#num)#num)#((num#num)#num))list->real^7` in
  let seven_lower_identity =
    candle_reflected_nl_selector_vector_identity_dim
      `:7` seven_lower_selector seven_boxes seven_lower in
  let seven_upper_identity =
    candle_reflected_nl_selector_vector_identity_dim
      `:7` seven_upper_selector seven_boxes seven_upper in
  let lower_append =
    candle_reflected_nl_append_parameter_vector lower parameter_lower in
  let upper_append =
    candle_reflected_nl_append_parameter_vector upper parameter_upper in
  let explicit_seven_theorem =
    BETA_RULE
      (REWRITE_RULE
        [seven_lower_identity;seven_upper_identity;
         GSYM lower_append;GSYM upper_append]
        seven_theorem) in
  let lower_vector =
    mk_comb (`vector:real list->real^6`,mk_flist lower) in
  let upper_vector =
    mk_comb (`vector:real list->real^6`,mk_flist upper) in
  let source_correspondence =
    BETA_RULE
      (candle_reflected_nl_append_parameter_source_correspondence
        seven_function six_function parameter) in
  let bridge =
    BETA_RULE
      (SPECL
        [seven_function;six_function;lower_vector;upper_vector;parameter;
         parameter_lower;parameter_upper]
        candle_reflected_nl_append_parameter_sound) in
  let result =
    MATCH_MP bridge
      (CONJ (CONJUNCT1 parameter_bounds)
        (CONJ (CONJUNCT2 parameter_bounds)
          (CONJ explicit_seven_theorem source_correspondence))) in
  if hyp result <> [] then
    failwith "append-parameter bridge: result assumptions";
  result;;

end;;
