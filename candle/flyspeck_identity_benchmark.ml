#use "candle/flyspeck_identity_ocaml_oracle.ml";;

let benchmark repetitions label thunk =
  Gc.full_major ();
  let allocated_before = Gc.allocated_bytes () in
  let time_before = Sys.time () in
  for _ = 1 to repetitions do ignore (thunk ()) done;
  let elapsed = Sys.time () -. time_before in
  let allocated = Gc.allocated_bytes () -. allocated_before in
  Printf.printf "identity-benchmark %s repetitions=%d seconds=%.6f allocated_bytes=%.0f\n%!"
    label repetitions elapsed allocated;;

let benchmark_input = List.init 5000 (fun x -> x);;
let benchmark_duplicated =
  List.flatten (List.map (fun x -> [x;x]) (List.init 2500 (fun x -> x)));;

benchmark 100 "original-filter-all" (fun () ->
  original_filter (fun _ -> true) benchmark_input);;
benchmark 100 "normalized-filter-all" (fun () ->
  normalized_filter (fun _ -> true) benchmark_input);;
benchmark 100 "original-filter-mixed" (fun () ->
  original_filter (fun x -> x mod 2 = 0) benchmark_input);;
benchmark 100 "normalized-filter-mixed" (fun () ->
  normalized_filter (fun x -> x mod 2 = 0) benchmark_input);;
benchmark 100 "original-partition-mixed" (fun () ->
  original_partition (fun x -> x mod 2 = 0) benchmark_input);;
benchmark 100 "normalized-partition-mixed" (fun () ->
  normalized_partition (fun x -> x mod 2 = 0) benchmark_input);;
benchmark 100 "original-uniq-duplicates" (fun () ->
  original_uniq benchmark_duplicated);;
benchmark 100 "normalized-uniq-duplicates" (fun () ->
  normalized_uniq benchmark_duplicated);;
benchmark 100 "original-qmap-identity" (fun () ->
  original_qmap (fun x -> x) benchmark_input);;
