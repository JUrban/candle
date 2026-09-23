(* ========================================================================== *)
(* Exact-data adapter for captured Flyspeck nonlinear polynomial fixtures.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This adapter performs no numerical checking.  *)
(* It maps an explicit scalar-variable order to vector coordinates, invokes  *)
(* the theorem-producing source reifier, and represents exact rational box   *)
(* endpoints as checker data.  The computed checker remains responsible for  *)
(* box validity and acceptance.                                               *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_flyspeck_reify.ml";;

module Candle_cv_polynomial_expr_flyspeck_fixture = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_flyspeck_reify;;

let candle_poly_fixture_vector_dimension vector =
  let vector_constructor,vector_arguments = dest_type (type_of vector) in
  if vector_constructor <> "cart" || length vector_arguments <> 2 ||
     hd vector_arguments <> `:real` then
    failwith "Candle Flyspeck fixture: expected a real vector";
  let index_type = List.nth vector_arguments 1 in
  let dimension_theorem =
    DIMINDEX_CONV (inst [index_type,`:N`] `dimindex (:N)`) in
  let dimension = dest_small_numeral (rand (concl dimension_theorem)) in
  if dimension <= 0 then
    failwith "Candle Flyspeck fixture: empty vector dimension";
  dimension;;

let candle_poly_fixture_mem_term tm =
  exists (fun candidate -> aconv tm candidate);;

let candle_poly_fixture_vectorize_scalar_source
      vector scalar_variables scalar_source =
  let dimension = candle_poly_fixture_vector_dimension vector in
  if length scalar_variables <> dimension then
    failwith "Candle Flyspeck fixture: scalar basis length mismatch";
  if exists (fun variable -> type_of variable <> `:real` ||
                             not (is_var variable)) scalar_variables then
    failwith "Candle Flyspeck fixture: expected real scalar variables";
  if length (setify Term.(<) scalar_variables) <>
     length scalar_variables then
    failwith "Candle Flyspeck fixture: duplicate scalar variable";
  if type_of scalar_source <> `:real` then
    failwith "Candle Flyspeck fixture: source is not real-valued";
  if exists
      (fun variable ->
        not (candle_poly_fixture_mem_term variable scalar_variables))
      (frees scalar_source) then
    failwith "Candle Flyspeck fixture: source escapes scalar basis";
  let components =
    candle_poly_vector_components vector dimension in
  let vector_source =
    subst (zip components scalar_variables) scalar_source in
  if exists (fun variable -> not (aconv variable vector))
       (frees vector_source) then
    failwith "Candle Flyspeck fixture: vector substitution escaped basis";
  vector_source;;

let candle_poly_fixture_q_interval lower upper =
  if type_of lower <> `:real` || type_of upper <> `:real` ||
     frees lower <> [] || frees upper <> [] ||
     not (is_ratconst lower) || not (is_ratconst upper) then
    failwith "Candle Flyspeck fixture: expected closed rational bounds";
  mk_pair
    (candle_q_term (rat_of_term lower),
     candle_q_term (rat_of_term upper));;

let candle_poly_fixture_q_boxes lower upper =
  if lower = [] || length lower <> length upper then
    failwith "Candle Flyspeck fixture: box cardinality mismatch";
  mk_list
    (map2 candle_poly_fixture_q_interval lower upper,
     candle_q_interval_type);;

let candle_poly_prepare_scalar_fixture
      vector scalar_variables scalar_source lower upper =
  let dimension = candle_poly_fixture_vector_dimension vector in
  if length lower <> dimension || length upper <> dimension then
    failwith "Candle Flyspeck fixture: bound dimension mismatch";
  let vector_source =
    candle_poly_fixture_vectorize_scalar_source
      vector scalar_variables scalar_source in
  let expression,valid,source_theorem,program,run_theorem =
    candle_poly_reify_vector_expression vector vector_source in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  vector_source,boxes,expression,valid,source_theorem,program,run_theorem;;

end;;
