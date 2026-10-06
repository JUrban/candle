(* Exact first-successor batch for the authentic AFP p=0 seed. *)

needs "candle/test_cv_compute_tame_graph_enumerator_seed.ml";;
needs "candle/cv_compute_tame_graph_successor.ml";;

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_successor;;

let candle_cv_tame_p0_successor_axioms_before = axioms ();;

(* enumerator 3 3 = [[0;0;2]; [0;1;2]].  This is the exact p=0 table *)
(* slice from the Isabelle enumerator, retained as authenticated input data. *)
let candle_cv_tame_p0_enum_002 =
 `Cexp_pair (Cexp_num 0)
   (Cexp_pair (Cexp_num 0)
    (Cexp_pair (Cexp_num 2) (Cexp_num 0)))`;;

let candle_cv_tame_p0_enum_012 =
 `Cexp_pair (Cexp_num 0)
   (Cexp_pair (Cexp_num 1)
    (Cexp_pair (Cexp_num 2) (Cexp_num 0)))`;;

let candle_cv_tame_p0_enumeration =
  mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_enum_002),
    mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_enum_012),`Cexp_num 0`));;

let candle_cv_tame_p0_successor_workload =
  list_mk_comb
    (`candle_cv_tame_generate_polygon_from_enum`,
     [candle_cv_tame_p0_expected;
      candle_cv_tame_p0_open_face;
      `Cexp_num 2`;
      candle_cv_tame_p0_enumeration]);;

let candle_cv_tame_p0_successor_theorem =
  candle_cv_tame_successor_compute candle_cv_tame_p0_successor_workload;;

let candle_cv_tame_p0_successor_repeat_theorem =
  candle_cv_tame_successor_compute candle_cv_tame_p0_successor_workload;;

if not
 (aconv (concl candle_cv_tame_p0_successor_theorem)
        (concl candle_cv_tame_p0_successor_repeat_theorem)) then
  failwith "tame p=0 successor: prepared repeat changed theorem identity";;

let candle_cv_tame_p0_successors =
  rand (concl candle_cv_tame_p0_successor_theorem);;

let candle_cv_tame_p0_first_successor,
    candle_cv_tame_p0_successor_tail =
  dest_binary "Cexp_pair" candle_cv_tame_p0_successors;;

let candle_cv_tame_p0_second_successor,
    candle_cv_tame_p0_successor_end =
  dest_binary "Cexp_pair" candle_cv_tame_p0_successor_tail;;

if not (aconv candle_cv_tame_p0_successor_end `Cexp_num 0`) then
  failwith "tame p=0 successor: expected exactly two successors";;

(* Independent literal projection copied from the Isabelle first-step oracle: *)
(* faces, vertex count, faceListAt, and heights must all agree exactly.         *)
let candle_cv_tame_p0_reference_num n =
  mk_comb (`Cexp_num`,mk_small_numeral n);;

let candle_cv_tame_p0_reference_pair left right =
  mk_comb (mk_comb (`Cexp_pair`,left),right);;

let candle_cv_tame_p0_reference_list values =
  List.fold_right candle_cv_tame_p0_reference_pair values `Cexp_num 0`;;

let candle_cv_tame_p0_reference_nat_list values =
  candle_cv_tame_p0_reference_list
    (List.map candle_cv_tame_p0_reference_num values);;

let candle_cv_tame_p0_reference_face vertices final_flag =
  candle_cv_tame_p0_reference_pair
    (candle_cv_tame_p0_reference_nat_list vertices)
    (candle_cv_tame_p0_reference_num (if final_flag then 1 else 0));;

let candle_cv_tame_p0_reference_graph faces vertex_count faces_at heights =
  candle_cv_tame_p0_reference_pair
    (candle_cv_tame_p0_reference_list faces)
    (candle_cv_tame_p0_reference_pair
      (candle_cv_tame_p0_reference_num vertex_count)
      (candle_cv_tame_p0_reference_pair
        (candle_cv_tame_p0_reference_list
          (List.map candle_cv_tame_p0_reference_list faces_at))
        (candle_cv_tame_p0_reference_nat_list heights)));;

let candle_cv_tame_p0_reference_a =
  candle_cv_tame_p0_reference_face [0;1;2] true;;
let candle_cv_tame_p0_reference_b =
  candle_cv_tame_p0_reference_face [0;2;3] true;;
let candle_cv_tame_p0_reference_c =
  candle_cv_tame_p0_reference_face [3;2;1;0] false;;
let candle_cv_tame_p0_reference_d =
  candle_cv_tame_p0_reference_face [2;1;0] true;;

let candle_cv_tame_p0_reference_first =
  candle_cv_tame_p0_reference_graph
    [candle_cv_tame_p0_reference_a;
     candle_cv_tame_p0_reference_b;
     candle_cv_tame_p0_reference_c]
    4
    [[candle_cv_tame_p0_reference_a;
      candle_cv_tame_p0_reference_c;
      candle_cv_tame_p0_reference_b];
     [candle_cv_tame_p0_reference_a;
      candle_cv_tame_p0_reference_c];
     [candle_cv_tame_p0_reference_a;
      candle_cv_tame_p0_reference_b;
      candle_cv_tame_p0_reference_c];
     [candle_cv_tame_p0_reference_c;
      candle_cv_tame_p0_reference_b]]
    [0;0;0;1];;

let candle_cv_tame_p0_reference_second =
  candle_cv_tame_p0_reference_graph
    [candle_cv_tame_p0_reference_a;candle_cv_tame_p0_reference_d]
    3
    [[candle_cv_tame_p0_reference_a;candle_cv_tame_p0_reference_d];
     [candle_cv_tame_p0_reference_a;candle_cv_tame_p0_reference_d];
     [candle_cv_tame_p0_reference_a;candle_cv_tame_p0_reference_d]]
    [0;0;0];;

let candle_cv_tame_p0_reference_batch =
  candle_cv_tame_p0_reference_list
    [candle_cv_tame_p0_reference_first;
     candle_cv_tame_p0_reference_second];;

if not
 (aconv candle_cv_tame_p0_successors candle_cv_tame_p0_reference_batch) then
  failwith "tame p=0 successor: complete graph identities differ from Isabelle";;

let candle_cv_tame_p0_first_count =
  candle_cv_tame_successor_compute
    (mk_comb (`candle_cv_tame_graph_vertex_count`,
      candle_cv_tame_p0_first_successor));;

let candle_cv_tame_p0_second_count =
  candle_cv_tame_successor_compute
    (mk_comb (`candle_cv_tame_graph_vertex_count`,
      candle_cv_tame_p0_second_successor));;

if not (aconv (rand (concl candle_cv_tame_p0_first_count)) `Cexp_num 4`) then
  failwith "tame p=0 successor: 002 child should have four vertices";;

if not (aconv (rand (concl candle_cv_tame_p0_second_count)) `Cexp_num 3`) then
  failwith "tame p=0 successor: 012 child should have three vertices";;

let candle_cv_tame_p0_first_final =
  candle_cv_tame_successor_compute
    (mk_comb (`candle_cv_tame_graph_final`,candle_cv_tame_p0_first_successor));;

let candle_cv_tame_p0_second_final =
  candle_cv_tame_successor_compute
    (mk_comb (`candle_cv_tame_graph_final`,candle_cv_tame_p0_second_successor));;

if not (aconv (rand (concl candle_cv_tame_p0_first_final)) `Cexp_num 0`) then
  failwith "tame p=0 successor: 002 child should retain one nonfinal face";;

if not (aconv (rand (concl candle_cv_tame_p0_second_final)) `Cexp_num 1`) then
  failwith "tame p=0 successor: 012 child should be final";;

let candle_cv_tame_p0_prune_002 =
  candle_cv_tame_successor_compute
    (list_mk_comb
      (`candle_cv_tame_contains_duplicate_edge`,
       [candle_cv_tame_p0_expected;
        candle_cv_tame_p0_open_face;
        candle_cv_tame_p0_enum_002]));;

let candle_cv_tame_p0_prune_012 =
  candle_cv_tame_successor_compute
    (list_mk_comb
      (`candle_cv_tame_contains_duplicate_edge`,
       [candle_cv_tame_p0_expected;
        candle_cv_tame_p0_open_face;
        candle_cv_tame_p0_enum_012]));;

if not (aconv (rand (concl candle_cv_tame_p0_prune_002)) `Cexp_num 0`) ||
   not (aconv (rand (concl candle_cv_tame_p0_prune_012)) `Cexp_num 0`) then
  failwith "tame p=0 successor: Isabelle duplicate-edge decisions differ";;

let candle_cv_tame_p0_successor_axioms_after = axioms ();;

if length candle_cv_tame_p0_successor_axioms_after <>
     length candle_cv_tame_p0_successor_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_p0_successor_axioms_before)
     candle_cv_tame_p0_successor_axioms_after) then
  failwith "tame p=0 successor: changed the global axiom set";;

let _ = print_string "CANDLE_CV_TAME_P0_SUCCESSOR_CANONICAL ";;
let _ = print_term candle_cv_tame_p0_successors;;
let _ = print_newline ();;

let _ = print_endline
  "CANDLE_CV_TAME_P0_SUCCESSOR_TIMING internal_clock=deterministic_zero external_host_timing_required=true";;

let _ = print_endline
  "CANDLE_CV_TAME_P0_SUCCESSOR_TEST_OK enum=2 duplicate_pruned=0 retained=2 graph_identities=isabelle_exact child_vertex_counts=4,3 child_final_flags=0,1 axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
