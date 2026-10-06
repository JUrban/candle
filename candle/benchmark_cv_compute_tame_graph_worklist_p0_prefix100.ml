(* Run after the stable p=0 worklist support is prepared. *)

needs "candle/prepare_cv_compute_tame_graph_worklist_p0.ml";;

let _ =
  let _ = candle_cv_tame_worklist_run_p0_prefix 100 in
  print_endline
    "CANDLE_CV_TAME_P0_WORKLIST_PREFIX100_BENCHMARK_OK DEVELOPMENT_NON_RELEASE";;
