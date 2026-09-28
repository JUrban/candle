needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_sound.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_sound;;

let candle_compact_tree_test_q value =
  mk_pair (mk_pair (mk_small_numeral value,`0`),`0`);;

let candle_compact_tree_test_interval lower upper =
  mk_pair
    (candle_compact_tree_test_q lower,
     candle_compact_tree_test_q upper);;

let candle_compact_tree_test_boxes lower upper =
  mk_list
    ([candle_compact_tree_test_interval lower upper;
      candle_compact_tree_test_interval 0 1],
     `:(((num#num)#num)#((num#num)#num))`);;

let candle_compact_tree_test_boxes2 lower1 upper1 lower2 upper2 =
  mk_list
    ([candle_compact_tree_test_interval lower1 upper1;
      candle_compact_tree_test_interval lower2 upper2],
     `:(((num#num)#num)#((num#num)#num))`);;

let candle_compact_tree_test_leaf boxes =
  list_mk_comb
    (`Candle_q_dim_taylor_model_tree_leaf`,
     [`Candle_analytic_poly (Candle_poly_const 0 0 0)`;boxes]);;

let candle_compact_tree_test_node axis boxes left right =
  list_mk_comb
    (`Candle_q_dim_taylor_model_tree_node`,
     [mk_small_numeral axis;boxes;left;right]);;

let candle_compact_tree_test_left_boxes =
  candle_compact_tree_test_boxes 0 1;;
let candle_compact_tree_test_right_boxes =
  candle_compact_tree_test_boxes 1 2;;
let candle_compact_tree_test_root_boxes =
  candle_compact_tree_test_boxes 0 2;;

let candle_compact_tree_test_left =
  candle_compact_tree_test_leaf candle_compact_tree_test_left_boxes;;
let candle_compact_tree_test_right =
  candle_compact_tree_test_leaf candle_compact_tree_test_right_boxes;;
let candle_compact_tree_test_tree =
  candle_compact_tree_test_node 1 candle_compact_tree_test_root_boxes
    candle_compact_tree_test_left candle_compact_tree_test_right;;

let candle_compact_tree_test_call tree_dim tree =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_tree_topology_check`,
     [mk_comb (`Cexp_num`,mk_small_numeral tree_dim);
      mk_comb
        (`candle_cv_q_dim_taylor_model_tree_topology`,
         tree)]);;

let candle_compact_tree_test_compute call =
  let representation =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_tree_topology_def;
       candle_cv_q_interval_list_def; candle_cv_q_interval_def;
       candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
      call in
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_dim_taylor_model_tree_compact_compute_eqs)
    (rand (concl representation));;

let candle_compact_tree_test_result =
  candle_compact_tree_test_compute
    (candle_compact_tree_test_call 2 candle_compact_tree_test_tree);;

let candle_compact_tree_test_expect label expected result =
  if not (aconv (rand (concl result)) expected) then
    failwith ("compact tree topology: " ^ label);;

candle_compact_tree_test_expect "valid split rejected" `Cexp_num 1`
  candle_compact_tree_test_result;;

let candle_compact_tree_test_bad_axis =
  candle_compact_tree_test_node 0 candle_compact_tree_test_root_boxes
    candle_compact_tree_test_left candle_compact_tree_test_right;;

candle_compact_tree_test_expect "bad axis accepted" `Cexp_num 0`
  (candle_compact_tree_test_compute
    (candle_compact_tree_test_call 2 candle_compact_tree_test_bad_axis));;

let candle_compact_tree_test_bad_face_left =
  candle_compact_tree_test_leaf (candle_compact_tree_test_boxes 0 0);;
let candle_compact_tree_test_bad_face =
  candle_compact_tree_test_node 1 candle_compact_tree_test_root_boxes
    candle_compact_tree_test_bad_face_left candle_compact_tree_test_right;;

candle_compact_tree_test_expect "changed split face accepted" `Cexp_num 0`
  (candle_compact_tree_test_compute
    (candle_compact_tree_test_call 2 candle_compact_tree_test_bad_face));;

let candle_compact_tree_test_bad_other_left =
  candle_compact_tree_test_leaf (candle_compact_tree_test_boxes2 0 1 0 2);;
let candle_compact_tree_test_bad_other =
  candle_compact_tree_test_node 1 candle_compact_tree_test_root_boxes
    candle_compact_tree_test_bad_other_left candle_compact_tree_test_right;;

candle_compact_tree_test_expect "changed non-split endpoint accepted" `Cexp_num 0`
  (candle_compact_tree_test_compute
    (candle_compact_tree_test_call 2 candle_compact_tree_test_bad_other));;

candle_compact_tree_test_expect "wrong dimension accepted" `Cexp_num 0`
  (candle_compact_tree_test_compute
    (candle_compact_tree_test_call 3 candle_compact_tree_test_tree));;

let candle_compact_tree_test_encoded_boxes =
  rand
    (concl
      (REWRITE_CONV
        [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
         candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
        (mk_comb
          (`candle_cv_q_interval_list`,candle_compact_tree_test_root_boxes))));;
let candle_compact_tree_test_malformed =
  list_mk_comb
    (`Cexp_pair`,
     [candle_compact_tree_test_encoded_boxes;
      list_mk_comb (`Cexp_pair`,[`Cexp_num 1`;`Cexp_num 0`])]);;
let candle_compact_tree_test_malformed_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_tree_topology_check`,
     [`Cexp_num 2`;candle_compact_tree_test_malformed]);;

candle_compact_tree_test_expect "malformed topology accepted" `Cexp_num 0`
  (candle_compact_tree_test_compute candle_compact_tree_test_malformed_call);;

let candle_compact_tree_test_abstract =
  SPEC `2`
    (SPEC candle_compact_tree_test_tree
      candle_cv_q_dim_taylor_model_tree_topology_check_correct);;

if hyp candle_compact_tree_test_abstract <> [] then
  failwith "compact tree topology: unexpected theorem assumptions";;

let candle_compact_tree_test_valid_representation =
  REWRITE_CONV
    [candle_cv_q_dim_taylor_model_tree_topology_def;
     candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (candle_compact_tree_test_call 2 candle_compact_tree_test_tree);;

let candle_compact_tree_test_acceptance =
  TRANS candle_compact_tree_test_valid_representation
    candle_compact_tree_test_result;;

let candle_compact_tree_test_dim_two = DIMINDEX_CONV `dimindex (:2)`;;

let candle_compact_tree_test_well_formed =
  MATCH_MP
    (REWRITE_RULE
      [candle_compact_tree_test_dim_two]
      (ISPECL
        [candle_compact_tree_test_tree;`ARB:real^2`]
        candle_cv_q_dim_taylor_model_tree_topology_accept_sound))
    candle_compact_tree_test_acceptance;;

if hyp candle_compact_tree_test_well_formed <> [] then
  failwith "compact tree topology: sound handoff has assumptions";;

print_endline "CANDLE_CV_COMPACT_TREE_TOPOLOGY_OK DEVELOPMENT_NON_RELEASE";;
