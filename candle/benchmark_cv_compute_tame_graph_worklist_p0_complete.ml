(* Complete executable p=0 worklist benchmark from the prepared exact state. *)

needs "candle/prepare_cv_compute_tame_graph_worklist_p0.ml";;

let _ = candle_cv_tame_worklist_run_p0_prefix 1000;;

let _ = print_endline
  "CANDLE_CV_TAME_P0_WORKLIST_COMPLETE_BENCHMARK_OK DEVELOPMENT_NON_RELEASE fuel=1000 expected_visited=239 expected_final_graphs=0";;
