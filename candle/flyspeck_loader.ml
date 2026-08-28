(* Manifest-rooted direct Flyspeck source loader, initial full-build slice.
   The manifest launcher must first bind [candle_hollight_root],
   [candle_flyspeck_root], [candle_flyspeck_overlay_root],
   [candle_flyspeck_generated_root], and [candle_flyspeck_build_mode].  The
   loader turns these hashed source-level inputs into the small environment
   allowlist used by Flyspeck; it does not inherit ambient host variables. *)

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
let candle_flyspeck_lp_source_root =
  Filename.concat candle_flyspeck_root "formal_lp/glpk/binary";;
let candle_flyspeck_lp_generated_hard_7 =
  Filename.concat candle_flyspeck_generated_root
    "formal_lp/glpk/binary/hard_7.dat";;

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
   candle_flyspeck_user_input;
   candle_flyspeck_lp_generated_hard_7];;

let candle_flyspeck_require_source path =
  if not (Sys.file_exists path) then
    failwith ("missing pinned Flyspeck source: " ^ path);;

List.iter candle_flyspeck_require_source candle_flyspeck_required_sources;;

if Digest.to_hex (Digest.file candle_flyspeck_lp_generated_hard_7) <>
     "8fe3a451e601c3263fbe11530fedc5ca" then
  failwith "prepared hard_7.dat authentication failed";;

(* Replace ambient directory enumeration and in-process tar/rm calls by one
   exact, deterministic certificate inventory.  The outer manifest pins all
   39 SHA-256 values and the archive-to-hard_7.dat derivation; this loader also
   authenticates the prepared exceptional member before any Flyspeck source
   runs. *)
let candle_flyspeck_lp_certificate_basenames =
  ["easy_1.dat";
   "easy_10.dat";
   "easy_11.dat";
   "easy_12.dat";
   "easy_13.dat";
   "easy_14.dat";
   "easy_15.dat";
   "easy_16.dat";
   "easy_17.dat";
   "easy_18.dat";
   "easy_19.dat";
   "easy_2.dat";
   "easy_20.dat";
   "easy_21.dat";
   "easy_22.dat";
   "easy_23.dat";
   "easy_24.dat";
   "easy_3.dat";
   "easy_4.dat";
   "easy_5.dat";
   "easy_6.dat";
   "easy_7.dat";
   "easy_8.dat";
   "easy_9.dat";
   "hard_1.dat";
   "hard_10.dat";
   "hard_11.dat";
   "hard_12.dat";
   "hard_13.dat";
   "hard_14.dat";
   "hard_15.dat";
   "hard_2.dat";
   "hard_3.dat";
   "hard_4.dat";
   "hard_5.dat";
   "hard_6.dat";
   "hard_7.dat";
   "hard_8.dat";
   "hard_9.dat"];;

let candle_flyspeck_lp_certificate_path basename =
  if basename = "hard_7.dat" then candle_flyspeck_lp_generated_hard_7
  else Filename.concat candle_flyspeck_lp_source_root basename;;

let candle_flyspeck_lp_certificate_files =
  map candle_flyspeck_lp_certificate_path
      candle_flyspeck_lp_certificate_basenames;;

if List.length candle_flyspeck_lp_certificate_files <> 39 ||
   List.exists (fun path -> Filename.check_suffix path ".gz")
               candle_flyspeck_lp_certificate_files then
  failwith "Flyspeck LP certificate inventory mismatch";;

List.iter candle_flyspeck_require_source
  candle_flyspeck_lp_certificate_files;;

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
     "e321ace652d99cd574dfa3b9fc512201" then
  failwith "Flyspeck source digest program authentication failed";;

if not (Sys.file_exists candle_flyspeck_full_build_program) ||
   Digest.to_hex (Digest.file candle_flyspeck_full_build_program) <>
     "ae887e2178b05532cea07f1ba116eef1" then
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

(* The host-side normalizer may materialize only these fourteen outputs in a
   separate tree.  The outer release manifest authenticates size and SHA-256;
   this process independently checks OCaml-compatible MD5 before registering
   exact original-path -> normalized-path substitutions.  The overlay root is
   never put on [load_path], so an extra output cannot shadow a pinned source. *)
let candle_flyspeck_normalized_sources =
  [(Filename.concat candle_flyspeck_text_root "build/strictbuild.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/build/strictbuild.hl",
    "35aa60993c762f45e08e7145e9da2bad");
   (Filename.concat candle_flyspeck_text_root "general/flyspeck_eval_4.14.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/flyspeck_eval_4.14.hl",
    "3ba61c19dc69f135bf014dff38fc2ead");
   (Filename.concat candle_flyspeck_text_root "general/lib.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/lib.hl",
    "3bc47551633759af22a39bcb4e1be8e5");
   (Filename.concat candle_flyspeck_text_root "general/print_types.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/print_types.hl",
    "221e52fdf51a79f1910c55a9ba886be3");
   (Filename.concat candle_flyspeck_text_root "general/parser_verbose.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/parser_verbose.hl",
    "ca206581943b009ea815225c0ff9ad95");
   (Filename.concat candle_flyspeck_text_root "general/debug.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/debug.hl",
    "9180a21c2ba1ae40ae032387d0418255");
   (Filename.concat candle_flyspeck_text_root "general/serialization.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/serialization.hl",
    "c109c6567cd777812a1479cb54eea6e9");
   (Filename.concat candle_flyspeck_text_root
      "general/update_database_400.ml",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/update_database_400.ml",
    "85ffaa8772cbaf66897720a5bf6215bd");
   (Filename.concat candle_flyspeck_root "jHOLLight/caml/ssreflect.hl",
    Filename.concat candle_flyspeck_overlay_root
      "jHOLLight/caml/ssreflect.hl",
    "2d0f8e0f45731595440fb400ac6956e6");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/main/lp_certificate.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/main/lp_certificate.hl",
    "639783011d135bd2aa117330b257174d");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/verify_all.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/verify_all.hl",
    "f37e71e8e7319c0036082fc8c2525055");
   (Filename.concat candle_flyspeck_text_root "jordan/tactics_jordan.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/tactics_jordan.hl",
    "e2076c132f1901e8e9dab2b1ed3cf02a");
   (Filename.concat candle_flyspeck_text_root
      "../formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    "fddf2accd2071d09095166ff7af885c7");
   (Filename.concat candle_flyspeck_text_root
      "tame/linear_programming_results.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/tame/linear_programming_results.hl",
    "873d319b17157a5f244f40d18450eacd")];;

if List.length candle_flyspeck_normalized_sources <> 14 then
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
