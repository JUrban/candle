needs "candle/cv_compute_split_partition_composition.ml";;

open Candle_cv_split_partition_composition;;

let candle_split_test_left_def = new_definition
 `candle_split_test_left i (t:real) d = 2 * d + i`;;
let candle_split_test_right_def = new_definition
 `candle_split_test_right i (t:real) d = 2 * d + i + 1`;;
let candle_split_test_predicate_def = new_definition
 `candle_split_test_predicate d <=> d < 1000`;;

let candle_split_test_closure = prove
 (`!i t d.
     candle_split_test_predicate (candle_split_test_left i t d) /\
     candle_split_test_predicate (candle_split_test_right i t d)
     ==> candle_split_test_predicate d`,
  REWRITE_TAC[candle_split_test_predicate_def;
              candle_split_test_left_def;
              candle_split_test_right_def] THEN
  ARITH_TAC);;

let candle_split_test_tree =
 `Candle_split_partition_node 0 #0.5
    Candle_split_partition_leaf
    (Candle_split_partition_node 1 #1.25
      Candle_split_partition_leaf Candle_split_partition_leaf)`;;

let candle_split_test_holds = prove
 (`candle_split_partition_holds
     candle_split_test_predicate candle_split_test_left
     candle_split_test_right 1
     (Candle_split_partition_node 0 #0.5
       Candle_split_partition_leaf
       (Candle_split_partition_node 1 #1.25
         Candle_split_partition_leaf Candle_split_partition_leaf))`,
  REWRITE_TAC[candle_split_partition_holds_def;
              candle_split_test_predicate_def;
              candle_split_test_left_def;
              candle_split_test_right_def] THEN
  ARITH_TAC);;

let candle_split_test_sound =
  let generic =
    ISPECL
      [`candle_split_test_predicate:num->bool`;
       `candle_split_test_left:num->real->num->num`;
       `candle_split_test_right:num->real->num->num`]
      candle_split_partition_composition_sound in
  let closed = MP generic candle_split_test_closure in
  MP (ISPECL [candle_split_test_tree;`1`] closed)
    candle_split_test_holds;;

let candle_split_test_counts = prove
 (`candle_split_partition_node_count
      (Candle_split_partition_node 0 #0.5
        Candle_split_partition_leaf
        (Candle_split_partition_node 1 #1.25
          Candle_split_partition_leaf Candle_split_partition_leaf)) = 5 /\
    candle_split_partition_leaf_count
      (Candle_split_partition_node 0 #0.5
        Candle_split_partition_leaf
        (Candle_split_partition_node 1 #1.25
          Candle_split_partition_leaf Candle_split_partition_leaf)) = 3`,
  REWRITE_TAC[candle_split_partition_node_count_def;
              candle_split_partition_leaf_count_def] THEN
  ARITH_TAC);;

if hyp candle_split_test_sound <> [] ||
   not (aconv (concl candle_split_test_sound)
     `candle_split_test_predicate 1`) ||
   hyp candle_split_test_counts <> []
then failwith "split partition composition theorem interface mismatch";;

print_endline "CANDLE_CV_SPLIT_PARTITION_COMPOSITION_OK";;
