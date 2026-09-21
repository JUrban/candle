(* Exercise late loading after a client has already introduced the short
   transformer names used by Flyspeck.  The generic theory's bound variables
   must not be captured by these constants. *)
let candle_partition_collision_bisect_left_def = new_definition
 `bisect_left (i:num) (d:num) = d`;;
let candle_partition_collision_bisect_right_def = new_definition
 `bisect_right (i:num) (d:num) = d`;;
let candle_partition_collision_frac_left_def = new_definition
 `frac_left (i:num) (r:real) (d:num) = d`;;
let candle_partition_collision_frac_right_def = new_definition
 `frac_right (i:num) (r:real) (d:num) = d`;;
let candle_partition_collision_dimension_def = new_definition
 `dimension (s:num->bool) = 0`;;

needs "candle/cv_compute_partition_composition.ml";;

open Candle_cv_partition_composition;;

let candle_partition_test_bisect_left_def = new_definition
 `candle_partition_test_bisect_left i d = 2 * d + i`;;
let candle_partition_test_bisect_right_def = new_definition
 `candle_partition_test_bisect_right i d = 2 * d + i + 1`;;
let candle_partition_test_frac_left_def = new_definition
 `candle_partition_test_frac_left i n q d = 3 * d + i + n + q`;;
let candle_partition_test_frac_right_def = new_definition
 `candle_partition_test_frac_right i n q d = 3 * d + i + n + q + 1`;;

let candle_partition_test_predicate_def = new_definition
 `candle_partition_test_predicate d <=> d < 1000`;;

let candle_partition_test_invariant_def = new_definition
 `candle_partition_test_invariant (d:num) <=> T`;;

let candle_partition_test_bisect_closure = prove
 (`!i d.
     candle_partition_test_predicate
       (candle_partition_test_bisect_left i d) /\
     candle_partition_test_predicate
       (candle_partition_test_bisect_right i d)
     ==> candle_partition_test_predicate d`,
  REWRITE_TAC[candle_partition_test_predicate_def;
              candle_partition_test_bisect_left_def;
              candle_partition_test_bisect_right_def] THEN
  ARITH_TAC);;

let candle_partition_test_frac_closure = prove
 (`!i n q d.
     candle_partition_test_predicate
       (candle_partition_test_frac_left i n q d) /\
     candle_partition_test_predicate
       (candle_partition_test_frac_right i n q d)
     ==> candle_partition_test_predicate d`,
  REWRITE_TAC[candle_partition_test_predicate_def;
              candle_partition_test_frac_left_def;
              candle_partition_test_frac_right_def] THEN
  ARITH_TAC);;

let candle_partition_test_tree =
 `Candle_partition_bisect 0
    (Candle_partition_recurse_right 1 3 10 Candle_partition_leaf)
    (Candle_partition_recurse_left 2 7 10
      (Candle_partition_bisect 0
        Candle_partition_leaf Candle_partition_leaf))`;;

let candle_partition_test_holds = prove
 (`candle_partition_holds
     candle_partition_test_predicate
     candle_partition_test_bisect_left candle_partition_test_bisect_right
     candle_partition_test_frac_left candle_partition_test_frac_right
     1
     (Candle_partition_bisect 0
       (Candle_partition_recurse_right 1 3 10 Candle_partition_leaf)
       (Candle_partition_recurse_left 2 7 10
         (Candle_partition_bisect 0
           Candle_partition_leaf Candle_partition_leaf)))`,
  REWRITE_TAC[candle_partition_holds_def;
              candle_partition_test_predicate_def;
              candle_partition_test_bisect_left_def;
              candle_partition_test_bisect_right_def;
              candle_partition_test_frac_left_def;
              candle_partition_test_frac_right_def] THEN
  ARITH_TAC);;

let candle_partition_test_sound =
  let generic =
    ISPECL
      [`candle_partition_test_predicate:num->bool`;
       `candle_partition_test_bisect_left:num->num->num`;
       `candle_partition_test_bisect_right:num->num->num`;
       `candle_partition_test_frac_left:num->num->num->num->num`;
       `candle_partition_test_frac_right:num->num->num->num->num`]
      candle_partition_composition_sound in
  let closed =
    MP generic
      (CONJ candle_partition_test_bisect_closure
        candle_partition_test_frac_closure) in
  MP (ISPECL [candle_partition_test_tree;`1`] closed)
    candle_partition_test_holds;;

let candle_partition_test_bisect_invariant = prove
 (`!i d. candle_partition_test_invariant d ==>
     candle_partition_test_invariant
       (candle_partition_test_bisect_left i d) /\
     candle_partition_test_invariant
       (candle_partition_test_bisect_right i d)`,
  REWRITE_TAC[candle_partition_test_invariant_def;
              candle_partition_test_bisect_left_def;
              candle_partition_test_bisect_right_def] THEN
  ARITH_TAC);;

let candle_partition_test_frac_invariant = prove
 (`!i n q d. candle_partition_test_invariant d ==>
     candle_partition_test_invariant
       (candle_partition_test_frac_left i n q d) /\
     candle_partition_test_invariant
       (candle_partition_test_frac_right i n q d)`,
  REWRITE_TAC[candle_partition_test_invariant_def;
              candle_partition_test_frac_left_def;
              candle_partition_test_frac_right_def] THEN
  ARITH_TAC);;

let candle_partition_test_sound_with_invariant =
  let generic =
    ISPECL
      [`candle_partition_test_invariant:num->bool`;
       `candle_partition_test_predicate:num->bool`;
       `candle_partition_test_bisect_left:num->num->num`;
       `candle_partition_test_bisect_right:num->num->num`;
       `candle_partition_test_frac_left:num->num->num->num->num`;
       `candle_partition_test_frac_right:num->num->num->num->num`]
      candle_partition_composition_sound_with_invariant in
  let obligations = prove
    (`(!i d. candle_partition_test_invariant d ==>
         candle_partition_test_invariant
           (candle_partition_test_bisect_left i d) /\
         candle_partition_test_invariant
           (candle_partition_test_bisect_right i d)) /\
      (!i n q d. candle_partition_test_invariant d ==>
         candle_partition_test_invariant
           (candle_partition_test_frac_left i n q d) /\
         candle_partition_test_invariant
           (candle_partition_test_frac_right i n q d)) /\
      (!i d. candle_partition_test_invariant d ==>
         candle_partition_test_predicate
           (candle_partition_test_bisect_left i d) /\
         candle_partition_test_predicate
           (candle_partition_test_bisect_right i d)
         ==> candle_partition_test_predicate d) /\
      (!i n q d. candle_partition_test_invariant d ==>
         candle_partition_test_predicate
           (candle_partition_test_frac_left i n q d) /\
         candle_partition_test_predicate
           (candle_partition_test_frac_right i n q d)
         ==> candle_partition_test_predicate d)`,
     MESON_TAC[candle_partition_test_bisect_invariant;
               candle_partition_test_frac_invariant;
               candle_partition_test_bisect_closure;
               candle_partition_test_frac_closure]) in
  let closed = MP generic obligations in
  MATCH_MP (ISPECL [candle_partition_test_tree;`1`] closed)
    (CONJ
      (prove
        (`candle_partition_test_invariant 1`,
         REWRITE_TAC[candle_partition_test_invariant_def] THEN ARITH_TAC))
      candle_partition_test_holds);;

let candle_partition_test_well_formed = prove
 (`candle_partition_well_formed 3
     (Candle_partition_bisect 0
       (Candle_partition_recurse_right 1 3 10 Candle_partition_leaf)
       (Candle_partition_recurse_left 2 7 10
         (Candle_partition_bisect 0
           Candle_partition_leaf Candle_partition_leaf)))`,
  REWRITE_TAC[candle_partition_well_formed_def] THEN ARITH_TAC);;

let candle_partition_test_counts = prove
 (`candle_partition_case_count
      (Candle_partition_bisect 0
        (Candle_partition_recurse_right 1 3 10 Candle_partition_leaf)
        (Candle_partition_recurse_left 2 7 10
          (Candle_partition_bisect 0
            Candle_partition_leaf Candle_partition_leaf))) = 5 /\
    candle_partition_leaf_count
      (Candle_partition_bisect 0
        (Candle_partition_recurse_right 1 3 10 Candle_partition_leaf)
        (Candle_partition_recurse_left 2 7 10
          (Candle_partition_bisect 0
            Candle_partition_leaf Candle_partition_leaf))) = 3`,
  REWRITE_TAC[candle_partition_case_count_def;
              candle_partition_leaf_count_def] THEN ARITH_TAC);;

if hyp candle_partition_test_sound <> [] ||
   not (aconv (concl candle_partition_test_sound)
     `candle_partition_test_predicate 1`) ||
   hyp candle_partition_test_sound_with_invariant <> [] ||
   not (aconv (concl candle_partition_test_sound_with_invariant)
     `candle_partition_test_predicate 1`) ||
   hyp candle_partition_test_well_formed <> [] ||
   hyp candle_partition_test_counts <> []
then failwith "partition composition theorem interface mismatch";;

print_endline "CANDLE_CV_PARTITION_COMPOSITION_OK";;
