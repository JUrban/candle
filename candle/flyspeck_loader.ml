(* Manifest-rooted direct Flyspeck source loader, initial full-build slice.
   The manifest launcher must first bind [candle_hollight_root],
   [candle_flyspeck_root], [candle_flyspeck_overlay_root], and
   [candle_flyspeck_build_mode].  The loader turns these hashed source-level
   inputs into the small environment allowlist used by Flyspeck; it does not
   inherit ambient host variables. *)

if candle_flyspeck_build_mode <> "full" then
  failwith "candle_flyspeck_build_mode must be full";;

(* Start the pinned Candle/HOL source stack in this clean process.  The release
   launcher runs this loader exactly once; reusing a populated REPL is outside
   the reproducibility contract. *)
#use "hol.ml";;

let candle_flyspeck_text_root =
  Filename.concat candle_flyspeck_root "text_formalization";;
let candle_flyspeck_metadata_root =
  Filename.concat candle_hollight_root "candle/flyspeck_metadata";;
let candle_flyspeck_date_input =
  Filename.concat candle_flyspeck_metadata_root "date.txt";;
let candle_flyspeck_user_input =
  Filename.concat candle_flyspeck_metadata_root "user.txt";;

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
   Filename.concat candle_flyspeck_root "jHOLLight/.project";
   candle_flyspeck_date_input;
   candle_flyspeck_user_input];;

let candle_flyspeck_require_source path =
  if not (Sys.file_exists path) then
    failwith ("missing pinned Flyspeck source: " ^ path);;

List.iter candle_flyspeck_require_source candle_flyspeck_required_sources;;

(* This generated program is SHA-256-pinned by the outer release manifest and
   MD5-authenticated here before execution.  Its OCaml-compatible MD5 values
   are checked in-process before any Flyspeck build source is evaluated.
   [hol.ml] and this loader necessarily start before the preflight, so the
   release launcher must still authenticate the executable and those bootstrap
   sources. *)
let candle_flyspeck_source_digest_program =
  Filename.concat candle_hollight_root "candle/flyspeck_source_digests.ml";;
let candle_flyspeck_full_build_program =
  Filename.concat candle_hollight_root "candle/flyspeck_full_build.ml";;

if not (Sys.file_exists candle_flyspeck_source_digest_program) ||
   Digest.to_hex (Digest.file candle_flyspeck_source_digest_program) <>
     "795a2a1a28ab69e7a4ec8cf4b4d24dce" then
  failwith "Flyspeck source digest program authentication failed";;

if not (Sys.file_exists candle_flyspeck_full_build_program) ||
   Digest.to_hex (Digest.file candle_flyspeck_full_build_program) <>
     "fa440c6eae11574a55adab1f881fd834" then
  failwith "Flyspeck static full-build program authentication failed";;

needs "candle/flyspeck_source_digests.ml";;
needs "candle/flyspeck_source_integrity.ml";;

candle_flyspeck_verify_sources 399 candle_hollight_root candle_flyspeck_root
  candle_flyspeck_source_digests;;

let candle_flyspeck_source_identity (source_root,source,digest) =
  let root =
    if source_root = "candle" then candle_hollight_root
    else if source_root = "flyspeck" then candle_flyspeck_root
    else failwith ("unknown Flyspeck source root: " ^ source_root) in
  let original = Filename.concat root source in
  original,(Filename.basename original,digest);;

Cakeml.configureSourceIdentities
  (map candle_flyspeck_source_identity candle_flyspeck_source_digests);;

(* The host-side normalizer may materialize only these five outputs in a
   separate tree.  The outer release manifest authenticates size and SHA-256;
   this process independently checks OCaml-compatible MD5 before registering
   exact original-path -> normalized-path substitutions.  The overlay root is
   never put on [load_path], so an extra output cannot shadow a pinned source. *)
let candle_flyspeck_normalized_sources =
  [(Filename.concat candle_flyspeck_text_root "build/strictbuild.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/build/strictbuild.hl",
    "35aa60993c762f45e08e7145e9da2bad");
   (Filename.concat candle_flyspeck_text_root "general/lib.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/lib.hl",
    "3bc47551633759af22a39bcb4e1be8e5");
   (Filename.concat candle_flyspeck_text_root "general/print_types.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/print_types.hl",
    "221e52fdf51a79f1910c55a9ba886be3");
   (Filename.concat candle_flyspeck_text_root "jordan/tactics_jordan.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/tactics_jordan.hl",
    "e2076c132f1901e8e9dab2b1ed3cf02a");
   (Filename.concat candle_flyspeck_text_root
      "../formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    "fddf2accd2071d09095166ff7af885c7")];;

if List.length candle_flyspeck_normalized_sources <> 5 then
  failwith "incomplete Flyspeck normalized source table";;

let candle_flyspeck_verify_normalized_source (_,path,expected) =
  if not (Sys.file_exists path) then
    failwith ("missing normalized Flyspeck source: " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected then
    failwith ("normalized Flyspeck source digest mismatch: " ^ path);;

List.iter candle_flyspeck_verify_normalized_source
  candle_flyspeck_normalized_sources;;

Cakeml.configureNormalizationOverlay
  (map (fun (original,normalized,_) -> original,normalized)
       candle_flyspeck_normalized_sources);;

candle_configure_manifest_process_inputs
  candle_flyspeck_date_input candle_flyspeck_user_input;;

let candle_flyspeck_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;

List.iter candle_flyspeck_add_load_path
  [candle_flyspeck_text_root;
   Filename.concat candle_flyspeck_root "formal_ineqs";
   Filename.concat candle_flyspeck_root "jHOLLight"];;

needs "build/strictbuild.hl";;

(* This authenticated generated program contains the exact 297 manifest roots
   as #flyspeck_needs actions.  A source error or neutralization error flushes
   the remaining driver and therefore prevents every following phrase and the
   final success marker from executing. *)
needs "candle/flyspeck_full_build.ml";;

needs "candle/flyspeck_l2_target.ml";;

print_endline "CANDLE_FLYSPECK_DIRECT_FULL_OK";;
