(* Manifest-rooted direct Flyspeck source loader, initial full-build slice.
   The manifest launcher must first bind [candle_hollight_root],
   [candle_flyspeck_root], and [candle_flyspeck_build_mode].  The loader turns
   these hashed source-level inputs into the small environment allowlist used
   by Flyspeck; it does not inherit ambient host variables. *)

if candle_flyspeck_build_mode <> "full" then
  failwith "candle_flyspeck_build_mode must be full";;

(* Start the pinned Candle/HOL source stack in this clean process.  The release
   launcher runs this loader exactly once; reusing a populated REPL is outside
   the reproducibility contract. *)
#use "hol.ml";;

let candle_flyspeck_text_root =
  Filename.concat candle_flyspeck_root "text_formalization";;

Sys.configure_manifest_environment
  candle_hollight_root candle_flyspeck_text_root candle_hollight_root false;;

if Sys.getcwd () <> candle_hollight_root ||
   Sys.getenv "FLYSPECK_DIR" <> candle_flyspeck_text_root ||
   Sys.getenv "HOLLIGHT_DIR" <> candle_hollight_root then
  failwith "Candle manifest environment mismatch";;

let candle_flyspeck_required_sources =
  [Filename.concat candle_hollight_root "hol.ml";
   Filename.concat candle_flyspeck_text_root "build/strictbuild.hl";
   Filename.concat candle_flyspeck_root "formal_lp/README.txt";
   Filename.concat candle_flyspeck_root "formal_graph/archive/README.md";
   Filename.concat candle_flyspeck_root "formal_ineqs/README.md";
   Filename.concat candle_flyspeck_root "jHOLLight/.project"];;

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
