(* Exact one-step state check for the reflected AFP depth-first worklist. *)

needs "candle/test_cv_compute_tame_graph_transition.ml";;
needs "candle/cv_compute_tame_graph_worklist.ml";;

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_worklist;;

let candle_cv_tame_worklist_axioms_before = axioms ();;

let candle_cv_tame_worklist_one_step_term =
  list_mk_comb
    (`candle_cv_tame_worklist_run`,
     [`Cexp_num 1`;
      candle_cv_tame_transition_candidates_p0;
      candle_cv_tame_p0_expected]);;

let candle_cv_tame_worklist_one_step =
  candle_cv_tame_worklist_eval candle_cv_tame_worklist_one_step_term;;

let candle_cv_tame_worklist_one_step_expected_stats =
 `Cexp_pair (Cexp_num 1)
   (Cexp_pair (Cexp_num 0)
    (Cexp_pair (Cexp_num 2)
     (Cexp_pair (Cexp_num 1)
      (Cexp_pair (Cexp_num 1) (Cexp_num 1)))))`;;

let candle_cv_tame_worklist_one_step_expected =
  candle_cv_tame_transition_pair
    candle_cv_tame_transition_next_seed_expected
    (candle_cv_tame_transition_pair `Cexp_num 0`
      candle_cv_tame_worklist_one_step_expected_stats);;

if not
 (aconv (rand (concl candle_cv_tame_worklist_one_step))
        candle_cv_tame_worklist_one_step_expected) then
  failwith "tame worklist: exact one-step state mismatch";;

let candle_cv_tame_worklist_zero_step =
  candle_cv_tame_worklist_eval
    (list_mk_comb
      (`candle_cv_tame_worklist_run`,
       [`Cexp_num 0`;
        candle_cv_tame_transition_candidates_p0;
        candle_cv_tame_p0_expected]));;

let candle_cv_tame_worklist_zero_expected =
  candle_cv_tame_transition_pair
    (candle_cv_tame_transition_list [candle_cv_tame_p0_expected])
    (candle_cv_tame_transition_pair `Cexp_num 0`
      `Cexp_pair (Cexp_num 0)
        (Cexp_pair (Cexp_num 0)
         (Cexp_pair (Cexp_num 0)
          (Cexp_pair (Cexp_num 0)
           (Cexp_pair (Cexp_num 0) (Cexp_num 1)))))`);;

if not
 (aconv (rand (concl candle_cv_tame_worklist_zero_step))
        candle_cv_tame_worklist_zero_expected) then
  failwith "tame worklist: fail-closed zero-fuel state mismatch";;

let candle_cv_tame_worklist_axioms_after = axioms ();;

if length candle_cv_tame_worklist_axioms_after <>
     length candle_cv_tame_worklist_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_worklist_axioms_before)
     candle_cv_tame_worklist_axioms_after) then
  failwith "tame worklist: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_WORKLIST_TEST_OK fuel0_preserves_frontier=true fuel1_visited=1 fuel1_stage0_children=2 fuel1_retained=1 fuel1_final_pruned=1 fuel1_maximum_frontier=1 exact_state=true axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
