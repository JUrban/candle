(* Focused exact checks for AFP tame-graph scoring and polygon-size pruning. *)

needs "candle/test_cv_compute_tame_graph_successor_p0.ml";;
needs "candle/cv_compute_tame_graph_scoring.ml";;

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_scoring;;

let candle_cv_tame_scoring_axioms_before = axioms ();;

let candle_cv_tame_scoring_num n =
  mk_comb (`Cexp_num`,mk_small_numeral n);;

let candle_cv_tame_scoring_pair left right =
  mk_comb (mk_comb (`Cexp_pair`,left),right);;

let candle_cv_tame_scoring_list values =
  List.fold_right candle_cv_tame_scoring_pair values `Cexp_num 0`;;

let candle_cv_tame_scoring_check term expected label =
  let theorem = candle_cv_tame_scoring_compute term in
  if not (aconv (rand (concl theorem)) expected) then
    failwith ("tame scoring mismatch: " ^ label)
  else theorem;;

(* Check every non-default row of the two AFP score tables. *)
let candle_cv_tame_scoring_face_rows =
  [(3,0);(4,2058);(5,4819);(6,7120);(7,15410)];;

let _ = List.iter
  (fun (size,score) ->
    ignore (candle_cv_tame_scoring_check
      (mk_comb (`candle_cv_tame_squander_face`,
        candle_cv_tame_scoring_num size))
      (candle_cv_tame_scoring_num score)
      ("squanderFace " ^ string_of_int size)))
  candle_cv_tame_scoring_face_rows;;

let candle_cv_tame_scoring_vertex_rows =
  [(0,3,6177);(0,4,9696);(1,2,6557);(1,3,6176);
   (2,1,7967);(2,2,4116);(2,3,12846);(3,1,3106);
   (3,2,8165);(4,0,3466);(4,1,3655);(5,0,395);
   (5,1,11354);(6,0,6854);(7,0,14493);(2,0,15410)];;

let _ = List.iter
  (fun (tri,quad,score) ->
    ignore (candle_cv_tame_scoring_check
      (list_mk_comb (`candle_cv_tame_squander_vertex`,
        [candle_cv_tame_scoring_num tri;
         candle_cv_tame_scoring_num quad]))
      (candle_cv_tame_scoring_num score)
      ("squanderVertex " ^ string_of_int tri ^ "," ^
       string_of_int quad)))
  candle_cv_tame_scoring_vertex_rows;;

let candle_cv_tame_scoring_seed_lower =
  candle_cv_tame_scoring_check
    (mk_comb (`candle_cv_tame_squander_lower_bound`,
      candle_cv_tame_p0_expected))
    (candle_cv_tame_scoring_num 0) "seed lower bound";;

let candle_cv_tame_scoring_first_lower =
  candle_cv_tame_scoring_check
    (mk_comb (`candle_cv_tame_squander_lower_bound`,
      candle_cv_tame_p0_first_successor))
    (candle_cv_tame_scoring_num 0) "first child lower bound";;

let candle_cv_tame_scoring_second_table_expected =
  candle_cv_tame_scoring_list
    (List.map
      (fun vertex -> candle_cv_tame_scoring_pair
        (candle_cv_tame_scoring_num vertex)
        (candle_cv_tame_scoring_num 15410))
      [0;1;2]);;

let candle_cv_tame_scoring_second_table =
  candle_cv_tame_scoring_check
    (mk_comb (`candle_cv_tame_excess_table`,
      candle_cv_tame_p0_second_successor))
    candle_cv_tame_scoring_second_table_expected
    "second child complete ExcessTable";;

let candle_cv_tame_scoring_second_lower =
  candle_cv_tame_scoring_check
    (mk_comb (`candle_cv_tame_squander_lower_bound`,
      candle_cv_tame_p0_second_successor))
    (candle_cv_tame_scoring_num 15410)
    "second child independent excess maximum";;

let candle_cv_tame_scoring_candidates_p0 =
  candle_cv_tame_scoring_list [candle_cv_tame_scoring_num 3];;

let candle_cv_tame_scoring_candidates_p2 =
  candle_cv_tame_scoring_list
    (List.map candle_cv_tame_scoring_num [3;4;5]);;

let candle_cv_tame_scoring_seed_p0_sizes =
  candle_cv_tame_scoring_check
    (list_mk_comb (`candle_cv_tame_polysizes`,
      [candle_cv_tame_scoring_candidates_p0;candle_cv_tame_p0_expected]))
    candle_cv_tame_scoring_candidates_p0 "seed p0 polysizes";;

let candle_cv_tame_scoring_seed_p2_sizes =
  candle_cv_tame_scoring_check
    (list_mk_comb (`candle_cv_tame_polysizes`,
      [candle_cv_tame_scoring_candidates_p2;candle_cv_tame_p0_expected]))
    candle_cv_tame_scoring_candidates_p2 "seed p2 polysizes";;

let candle_cv_tame_scoring_rejected_sizes =
  candle_cv_tame_scoring_check
    (list_mk_comb (`candle_cv_tame_polysizes`,
      [candle_cv_tame_scoring_candidates_p2;
       candle_cv_tame_p0_second_successor]))
    `Cexp_num 0` "score-at-target polysizes";;

let candle_cv_tame_scoring_threshold_sizes =
  candle_cv_tame_scoring_check
    (list_mk_comb (`candle_cv_tame_filter_polysizes`,
      [candle_cv_tame_scoring_num 12000;
       candle_cv_tame_scoring_candidates_p2]))
    (candle_cv_tame_scoring_list
      (List.map candle_cv_tame_scoring_num [3;4]))
    "strict target threshold";;

let candle_cv_tame_scoring_second_tame13a =
  candle_cv_tame_scoring_check
    (mk_comb (`candle_cv_tame_is_tame13a`,
      candle_cv_tame_p0_second_successor))
    (candle_cv_tame_scoring_num 0) "second child is_tame13a";;

let candle_cv_tame_scoring_axioms_after = axioms ();;

if length candle_cv_tame_scoring_axioms_after <>
     length candle_cv_tame_scoring_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_scoring_axioms_before)
     candle_cv_tame_scoring_axioms_after) then
  failwith "tame scoring: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_SCORING_TEST_OK face_rows=5 vertex_rows=16 seed_lower=0 first_child_lower=0 second_child_lower=15410 second_child_table=3 p0_sizes=1 p2_sizes=3 strict_threshold=true axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
