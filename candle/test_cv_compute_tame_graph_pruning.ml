(* Focused checks for the exact AFP Generator.notame reflected predicate. *)

needs "candle/test_cv_compute_tame_graph_enumerator_seed.ml";;
needs "candle/cv_compute_tame_graph_pruning.ml";;

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_pruning;;

let candle_cv_tame_pruning_axioms_before = axioms ();;

let candle_cv_tame_pruning_pair left right =
  mk_comb (mk_comb (`Cexp_pair`,left),right);;

let candle_cv_tame_pruning_num value =
  mk_comb (`Cexp_num`,mk_small_numeral value);;

let candle_cv_tame_pruning_list values =
  List.fold_right candle_cv_tame_pruning_pair values `Cexp_num 0`;;

let candle_cv_tame_pruning_face vertices final_flag =
  candle_cv_tame_pruning_pair
    (candle_cv_tame_pruning_list
      (List.map candle_cv_tame_pruning_num vertices))
    (candle_cv_tame_pruning_num (if final_flag then 1 else 0));;

let candle_cv_tame_pruning_graph vertex_count faces_at =
  candle_cv_tame_pruning_pair `Cexp_num 0`
    (candle_cv_tame_pruning_pair
      (candle_cv_tame_pruning_num vertex_count)
      (candle_cv_tame_pruning_pair
        (candle_cv_tame_pruning_list
          (List.map candle_cv_tame_pruning_list faces_at))
        `Cexp_num 0`));;

let candle_cv_tame_pruning_triangle =
  candle_cv_tame_pruning_face [0;1;2] true;;

let candle_cv_tame_pruning_pentagon =
  candle_cv_tame_pruning_face [0;1;2;3;4] true;;

let candle_cv_tame_pruning_repeat value count =
  let rec build remaining acc =
    if remaining = 0 then acc
    else build (remaining - 1) (value :: acc) in
  build count [];;

let candle_cv_tame_pruning_degree7 =
  candle_cv_tame_pruning_graph 1
    [candle_cv_tame_pruning_repeat candle_cv_tame_pruning_triangle 7];;

let candle_cv_tame_pruning_degree8 =
  candle_cv_tame_pruning_graph 1
    [candle_cv_tame_pruning_repeat candle_cv_tame_pruning_triangle 8];;

let candle_cv_tame_pruning_exceptional_degree7 =
  candle_cv_tame_pruning_graph 1
    [candle_cv_tame_pruning_pentagon ::
     candle_cv_tame_pruning_repeat candle_cv_tame_pruning_triangle 6];;

let candle_cv_tame_pruning_vertex16 =
  candle_cv_tame_pruning_graph 16 [];;

let candle_cv_tame_pruning_check graph expected label =
  let theorem = candle_cv_tame_pruning_compute
    (mk_comb (`candle_cv_tame_notame`,graph)) in
  if not (aconv (rand (concl theorem)) (candle_cv_tame_pruning_num expected))
  then failwith ("tame pruning mismatch: " ^ label)
  else theorem;;

let candle_cv_tame_pruning_seed_theorem =
  candle_cv_tame_pruning_check candle_cv_tame_p0_expected 0 "p0 seed";;

let candle_cv_tame_pruning_degree7_theorem =
  candle_cv_tame_pruning_check candle_cv_tame_pruning_degree7 0
    "degree 7 without exceptional face";;

let candle_cv_tame_pruning_degree8_theorem =
  candle_cv_tame_pruning_check candle_cv_tame_pruning_degree8 1
    "degree 8 without exceptional face";;

let candle_cv_tame_pruning_exceptional_degree7_theorem =
  candle_cv_tame_pruning_check candle_cv_tame_pruning_exceptional_degree7 1
    "degree 7 with exceptional face";;

let candle_cv_tame_pruning_vertex16_theorem =
  candle_cv_tame_pruning_check candle_cv_tame_pruning_vertex16 1
    "vertex bound 16";;

let candle_cv_tame_pruning_filter_input =
  candle_cv_tame_pruning_list
   [candle_cv_tame_p0_expected;
    candle_cv_tame_pruning_degree8;
    candle_cv_tame_pruning_degree7;
    candle_cv_tame_pruning_exceptional_degree7;
    candle_cv_tame_pruning_vertex16];;

let candle_cv_tame_pruning_filter_expected =
  candle_cv_tame_pruning_list
   [candle_cv_tame_p0_expected;candle_cv_tame_pruning_degree7];;

let candle_cv_tame_pruning_filter_theorem =
  candle_cv_tame_pruning_compute
    (mk_comb
      (`candle_cv_tame_filter_notame`,candle_cv_tame_pruning_filter_input));;

if not
 (aconv (rand (concl candle_cv_tame_pruning_filter_theorem))
        candle_cv_tame_pruning_filter_expected) then
  failwith "tame pruning: filtered child identity/order mismatch";;

let candle_cv_tame_pruning_axioms_after = axioms ();;

if length candle_cv_tame_pruning_axioms_after <>
     length candle_cv_tame_pruning_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_pruning_axioms_before)
     candle_cv_tame_pruning_axioms_after) then
  failwith "tame pruning: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_PRUNING_TEST_OK seed_retained=true degree7_retained=true degree8_rejected=true exceptional_degree7_rejected=true vertex16_rejected=true filter_order=exact axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
