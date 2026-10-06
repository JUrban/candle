(* ========================================================================== *)
(* Deterministic reflected worklist for the AFP tame-graph enumerator.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The traversal is the depth-first order used by *)
(* Worklist.worklist_tree_aux: successors are prepended to the remaining      *)
(* frontier.  Explicit numeric cval fuel makes bounded p=2 experiments and    *)
(* chunked complete p=0 execution fail closed on exhaustion.                  *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_transition.ml";;

module Candle_cv_tame_graph_worklist = struct

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_successor;;
open Candle_cv_tame_graph_scoring;;
open Candle_cv_tame_graph_transition;;

(* Stats fields, in Isabelle oracle order for the overlapping measurements:  *)
(* visited, final visits, next_tame0 children, retained children, final        *)
(* pruned children, maximum frontier.                                         *)
let candle_cv_tame_worklist_stats_def = new_definition
 `candle_cv_tame_worklist_stats visited final_visits stage0_children
      retained_children final_pruned maximum_frontier =
    Cexp_pair visited
      (Cexp_pair final_visits
        (Cexp_pair stage0_children
          (Cexp_pair retained_children
            (Cexp_pair final_pruned maximum_frontier))))`;;

let candle_cv_tame_worklist_stats_empty_def = new_definition
 `candle_cv_tame_worklist_stats_empty =
    candle_cv_tame_worklist_stats
      (Cexp_num 0) (Cexp_num 0) (Cexp_num 0)
      (Cexp_num 0) (Cexp_num 0) (Cexp_num 1)`;;

let candle_cv_tame_worklist_stats_visited_def = new_definition
 `candle_cv_tame_worklist_stats_visited stats = Cexp_fst stats`;;

let candle_cv_tame_worklist_stats_final_visits_def = new_definition
 `candle_cv_tame_worklist_stats_final_visits stats =
    Cexp_fst (Cexp_snd stats)`;;

let candle_cv_tame_worklist_stats_stage0_children_def = new_definition
 `candle_cv_tame_worklist_stats_stage0_children stats =
    Cexp_fst (Cexp_snd (Cexp_snd stats))`;;

let candle_cv_tame_worklist_stats_retained_children_def = new_definition
 `candle_cv_tame_worklist_stats_retained_children stats =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd stats)))`;;

let candle_cv_tame_worklist_stats_final_pruned_def = new_definition
 `candle_cv_tame_worklist_stats_final_pruned stats =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd stats))))`;;

let candle_cv_tame_worklist_stats_maximum_frontier_def = new_definition
 `candle_cv_tame_worklist_stats_maximum_frontier stats =
    Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd stats))))`;;

let candle_cv_tame_worklist_stats_bump_def = new_definition
 `candle_cv_tame_worklist_stats_bump graph stage0 kept rest stats =
    (let stage0_count = candle_cv_tame_list_length stage0 in
     let kept_count = candle_cv_tame_list_length kept in
     let frontier = Cexp_add kept_count
       (candle_cv_tame_list_length rest) in
     candle_cv_tame_worklist_stats
       (Cexp_add (candle_cv_tame_worklist_stats_visited stats)
         (Cexp_num 1))
       (Cexp_add (candle_cv_tame_worklist_stats_final_visits stats)
         (Cexp_if (candle_cv_tame_graph_final graph)
           (Cexp_num 1) (Cexp_num 0)))
       (Cexp_add (candle_cv_tame_worklist_stats_stage0_children stats)
         stage0_count)
       (Cexp_add (candle_cv_tame_worklist_stats_retained_children stats)
         kept_count)
       (Cexp_add (candle_cv_tame_worklist_stats_final_pruned stats)
         (Cexp_sub stage0_count kept_count))
       (candle_cv_tame_max_num
         (candle_cv_tame_worklist_stats_maximum_frontier stats)
         frontier))`;;

(* Result = pair frontier (pair reversed_final_visits stats). *)
let candle_cv_tame_worklist_result_def = new_definition
 `candle_cv_tame_worklist_result frontier finals stats =
    Cexp_pair frontier (Cexp_pair finals stats)`;;

let candle_cv_tame_worklist_result_frontier_def = new_definition
 `candle_cv_tame_worklist_result_frontier result = Cexp_fst result`;;

let candle_cv_tame_worklist_result_finals_def = new_definition
 `candle_cv_tame_worklist_result_finals result =
    Cexp_fst (Cexp_snd result)`;;

let candle_cv_tame_worklist_result_stats_def = new_definition
 `candle_cv_tame_worklist_result_stats result =
    Cexp_snd (Cexp_snd result)`;;

let candle_cv_tame_worklist_num_def =
  new_recursive_definition num_RECURSION
 `(candle_cv_tame_worklist_num 0 candidates frontier finals stats =
     candle_cv_tame_worklist_result frontier finals stats) /\
  (candle_cv_tame_worklist_num (SUC n) candidates frontier finals stats =
     Cexp_if (Cexp_ispair frontier)
       (let graph = Cexp_fst frontier in
        let rest = Cexp_snd frontier in
        let stage0 = candle_cv_tame_next_tame0 candidates graph in
        let kept = candle_cv_tame_filter_final_tame stage0 in
        let next_frontier = candle_cv_tame_list_append kept rest in
        let next_finals =
          Cexp_if (candle_cv_tame_graph_final graph)
            (Cexp_pair graph finals) finals in
        let next_stats =
          candle_cv_tame_worklist_stats_bump graph stage0 kept rest stats in
        candle_cv_tame_worklist_num n candidates
          next_frontier next_finals next_stats)
       (candle_cv_tame_worklist_result frontier finals stats))`;;

let candle_cv_tame_worklist_def = define
 `(candle_cv_tame_worklist (Cexp_num n) candidates frontier finals stats =
     candle_cv_tame_worklist_num n candidates frontier finals stats) /\
  (candle_cv_tame_worklist (Cexp_pair x y) candidates frontier finals stats =
     candle_cv_tame_worklist_result frontier finals stats)`;;

let candle_cv_tame_worklist_run_def = new_definition
 `candle_cv_tame_worklist_run fuel candidates seed =
    candle_cv_tame_worklist fuel candidates
      (candle_cv_tame_singleton seed) (Cexp_num 0)
      candle_cv_tame_worklist_stats_empty`;;

let candle_cv_tame_worklist_compute = prove
 (`!fuel candidates frontier finals stats.
    candle_cv_tame_worklist fuel candidates frontier finals stats =
      Cexp_if (Cexp_ispair fuel)
        (candle_cv_tame_worklist_result frontier finals stats)
        (Cexp_if (Cexp_eq fuel (Cexp_num 0))
          (candle_cv_tame_worklist_result frontier finals stats)
          (Cexp_if (Cexp_ispair frontier)
            (let graph = Cexp_fst frontier in
             let rest = Cexp_snd frontier in
             let stage0 = candle_cv_tame_next_tame0 candidates graph in
             let kept = candle_cv_tame_filter_final_tame stage0 in
             let next_frontier = candle_cv_tame_list_append kept rest in
             let next_finals =
               Cexp_if (candle_cv_tame_graph_final graph)
                 (Cexp_pair graph finals) finals in
             let next_stats =
               candle_cv_tame_worklist_stats_bump
                 graph stage0 kept rest stats in
             candle_cv_tame_worklist
               (Cexp_sub fuel (Cexp_num 1)) candidates
               next_frontier next_finals next_stats)
            (candle_cv_tame_worklist_result frontier finals stats)))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THENL
   [MP_TAC (SPEC `a:num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
    REWRITE_TAC[candle_cv_tame_worklist_def;
                candle_cv_tame_worklist_num_def; cexp_if_def;
                cexp_ispair_def; cexp_eq_def; cexp_sub_def;
                injectivity "cval"; injectivity "num"; NOT_SUC;
                ARITH_RULE `SUC n - 1 = n`];
    REWRITE_TAC[candle_cv_tame_worklist_def; cexp_if_def;
                cexp_ispair_def]]);;

let candle_cv_tame_worklist_compute_eqs =
  candle_cv_tame_transition_compute_eqs @
  map SPEC_ALL
   [candle_cv_tame_worklist_stats_def;
    candle_cv_tame_worklist_stats_empty_def;
    candle_cv_tame_worklist_stats_visited_def;
    candle_cv_tame_worklist_stats_final_visits_def;
    candle_cv_tame_worklist_stats_stage0_children_def;
    candle_cv_tame_worklist_stats_retained_children_def;
    candle_cv_tame_worklist_stats_final_pruned_def;
    candle_cv_tame_worklist_stats_maximum_frontier_def;
    candle_cv_tame_worklist_stats_bump_def;
    candle_cv_tame_worklist_result_def;
    candle_cv_tame_worklist_result_frontier_def;
    candle_cv_tame_worklist_result_finals_def;
    candle_cv_tame_worklist_result_stats_def;
    candle_cv_tame_worklist_compute;
    candle_cv_tame_worklist_run_def];;

let candle_cv_tame_worklist_eval tm =
  compute candle_cv_tame_worklist_compute_eqs tm;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_WORKLIST_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
