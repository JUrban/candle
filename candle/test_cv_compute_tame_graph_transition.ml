(* Focused checks for the composed AFP enumerator and next_tame transition. *)

needs "candle/test_cv_compute_tame_graph_successor_p0.ml";;
needs "candle/cv_compute_tame_graph_transition.ml";;

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_transition;;

let candle_cv_tame_transition_axioms_before = axioms ();;

let candle_cv_tame_transition_num n =
  mk_comb (`Cexp_num`,mk_small_numeral n);;

let candle_cv_tame_transition_pair left right =
  mk_comb (mk_comb (`Cexp_pair`,left),right);;

let candle_cv_tame_transition_list values =
  List.fold_right candle_cv_tame_transition_pair values `Cexp_num 0`;;

let candle_cv_tame_transition_nat_list values =
  candle_cv_tame_transition_list
    (List.map candle_cv_tame_transition_num values);;

let candle_cv_tame_transition_check term expected label =
  let theorem = candle_cv_tame_transition_compute term in
  if not (aconv (rand (concl theorem)) expected) then
    failwith ("tame transition mismatch: " ^ label)
  else theorem;;

let candle_cv_tame_transition_enum33_expected =
  candle_cv_tame_transition_list
   [candle_cv_tame_transition_nat_list [0;0;2];
    candle_cv_tame_transition_nat_list [0;1;2]];;

let candle_cv_tame_transition_enum33 =
  candle_cv_tame_transition_check
    (list_mk_comb (`candle_cv_tame_enumerator`,
      [candle_cv_tame_transition_num 3;candle_cv_tame_p0_open_face]))
    candle_cv_tame_transition_enum33_expected "enumerator 3 3";;

let candle_cv_tame_transition_enum43_expected =
  candle_cv_tame_transition_list
   [candle_cv_tame_transition_nat_list [0;0;0;2];
    candle_cv_tame_transition_nat_list [0;0;1;2];
    candle_cv_tame_transition_nat_list [0;1;1;2]];;

let candle_cv_tame_transition_enum43 =
  candle_cv_tame_transition_check
    (list_mk_comb (`candle_cv_tame_enumerator`,
      [candle_cv_tame_transition_num 4;candle_cv_tame_p0_open_face]))
    candle_cv_tame_transition_enum43_expected "enumerator 4 3";;

let candle_cv_tame_transition_candidates_p0 =
  candle_cv_tame_transition_list [candle_cv_tame_transition_num 3];;

let candle_cv_tame_transition_next0_seed =
  candle_cv_tame_transition_check
    (list_mk_comb (`candle_cv_tame_next_tame0`,
      [candle_cv_tame_transition_candidates_p0;candle_cv_tame_p0_expected]))
    candle_cv_tame_p0_successors "next_tame0 p0 seed";;

let candle_cv_tame_transition_next_seed_expected =
  candle_cv_tame_transition_list [candle_cv_tame_p0_first_successor];;

let candle_cv_tame_transition_next_seed =
  candle_cv_tame_transition_check
    (list_mk_comb (`candle_cv_tame_next_tame`,
      [candle_cv_tame_transition_candidates_p0;candle_cv_tame_p0_expected]))
    candle_cv_tame_transition_next_seed_expected "next_tame p0 seed";;

let candle_cv_tame_transition_second_is_tame =
  candle_cv_tame_transition_check
    (mk_comb (`candle_cv_tame_is_tame`,
      candle_cv_tame_p0_second_successor))
    (candle_cv_tame_transition_num 0) "final triangle is_tame";;

let candle_cv_tame_transition_first_final =
  candle_cv_tame_transition_check
    (mk_comb (`candle_cv_tame_graph_final`,
      candle_cv_tame_p0_first_successor))
    (candle_cv_tame_transition_num 0) "retained child nonfinal";;

let candle_cv_tame_transition_axioms_after = axioms ();;

if length candle_cv_tame_transition_axioms_after <>
     length candle_cv_tame_transition_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_transition_axioms_before)
     candle_cv_tame_transition_axioms_after) then
  failwith "tame transition: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_TRANSITION_TEST_OK enum33=2 enum43=3 next_tame0_children=2 next_tame_children=1 final_pruned=1 complete_graph_identities=isabelle_exact axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
