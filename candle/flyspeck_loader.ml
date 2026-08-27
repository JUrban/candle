(* Manifest-rooted direct Flyspeck source loader, initial full-build slice.
   The manifest launcher must first bind [candle_flyspeck_root] and
   [candle_flyspeck_build_mode].  They are source-level inputs because the
   current verified runtime does not yet implement [Sys.getenv]. *)

if candle_flyspeck_build_mode <> "full" then
  failwith "candle_flyspeck_build_mode must be full";;

let candle_flyspeck_text_root =
  Filename.concat candle_flyspeck_root "text_formalization";;

let candle_flyspeck_required_sources =
  [Filename.concat candle_flyspeck_text_root "build/strictbuild.hl";
   Filename.concat candle_flyspeck_root "formal_lp";
   Filename.concat candle_flyspeck_root "formal_graph";
   Filename.concat candle_flyspeck_root "formal_ineqs";
   Filename.concat candle_flyspeck_root "jHOLLight"];;

let candle_flyspeck_require_source path =
  if not (Sys.file_exists path) then
    failwith ("missing pinned Flyspeck source: " ^ path);;

List.iter candle_flyspeck_require_source candle_flyspeck_required_sources;;

let candle_flyspeck_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;

List.iter candle_flyspeck_add_load_path
  [candle_flyspeck_text_root;
   Filename.concat candle_flyspeck_root "formal_ineqs";
   Filename.concat candle_flyspeck_root "jHOLLight"];;

needs "build/strictbuild.hl";;

let candle_flyspeck_loaded_sources =
  map (fun source -> flyspeck_needs source; source)
    Build.build_sequence_full;;

if List.length candle_flyspeck_loaded_sources <>
   List.length Build.build_sequence_full then
  failwith "incomplete Flyspeck full source sequence";;

needs "candle/flyspeck_l2_target.ml";;

print_endline "CANDLE_FLYSPECK_DIRECT_FULL_OK";;
