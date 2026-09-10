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
     "a026a372db63b0002623030cba2c01f3" then
  failwith "Flyspeck source digest program authentication failed";;

if not (Sys.file_exists candle_flyspeck_full_build_program) ||
   Digest.to_hex (Digest.file candle_flyspeck_full_build_program) <>
     "6b4169352f02a47939dbbc64bcb9bf5a" then
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

(* The host-side normalizer materializes all twenty-four outputs in a separate tree;
   this process registers only the twenty-three selected by the direct source graph.
   The outer release manifest authenticates size and SHA-256; this process checks
   OCaml-compatible MD5 before registering exact original-to-normalized paths.
   The overlay root is never put on [load_path], so an extra output cannot shadow
   a pinned source; the unselected OCaml-3.10 output cannot enter the loader. *)
let candle_flyspeck_normalized_sources =
  [(Filename.concat candle_flyspeck_text_root "build/strictbuild.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/build/strictbuild.hl",
    "05ec78d1d0efad0c1f3554ffd47b94d0");
   (Filename.concat candle_flyspeck_text_root "general/flyspeck_eval_4.14.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/flyspeck_eval_4.14.hl",
    "7ca870cd84b14e56da55eefa51a3828e");
   (Filename.concat candle_flyspeck_text_root "general/lib.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/lib.hl",
    "3bc47551633759af22a39bcb4e1be8e5");
   (Filename.concat candle_flyspeck_text_root "general/print_types.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/print_types.hl",
    "937774e3558ecfe48afda2f7f54dc5b9");
   (Filename.concat candle_flyspeck_text_root "general/hol_pervasives.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/hol_pervasives.hl",
    "fe90a871fbd8e40750f5445480af2e40");
   (Filename.concat candle_flyspeck_text_root "general/sphere.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/sphere.hl",
    "1e134647152103f755a0884313b3ad72");
   (Filename.concat candle_flyspeck_text_root "general/hales_tactic.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/hales_tactic.hl",
    "f5155d756ee2da58d1957f8892a60517");
   (Filename.concat candle_flyspeck_text_root "general/truong_tactic.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/truong_tactic.hl",
    "1f369a87dc5dcbc4c1b75eae67cb4afb");
   (Filename.concat candle_flyspeck_text_root "general/parser_verbose.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/parser_verbose.hl",
    "3209a4491e57ae1c43afd673be59d7e3");
   (Filename.concat candle_flyspeck_text_root "general/debug.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/debug.hl",
    "318079c3dbff839fb4a778aff20a8204");
   (Filename.concat candle_flyspeck_text_root "general/serialization.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/serialization.hl",
    "1d7f8887a5f880ffebd96526d23e7a36");
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
    "c1282e344707f2a8af85c258b9cf0e22");
   (Filename.concat candle_flyspeck_text_root "jordan/tactics_jordan.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/tactics_jordan.hl",
    "750508a2cadac11cd053fec89cb2a5fb");
   (Filename.concat candle_flyspeck_text_root
      "../formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    "15b9dada3bf16bc851bd825605ad19f8");
   (Filename.concat candle_flyspeck_text_root
      "tame/linear_programming_results.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/tame/linear_programming_results.hl",
    "873d319b17157a5f244f40d18450eacd");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/break_case_exec.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/break_case_exec.hl",
    "877814cc08f081a8a25d6dfbc64aba1e");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/mk_all_ineq.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/mk_all_ineq.hl",
    "44f7f8842ee7bf2d2aeca90d5a1d2d94");
   (Filename.concat candle_flyspeck_root
      "formal_graph/archive/archive_all.ml",
    Filename.concat candle_flyspeck_overlay_root
      "formal_graph/archive/archive_all.ml",
    "787e8244a0350c237a406f7e91fb97b7");
   (Filename.concat candle_flyspeck_root "jHOLLight/caml/sections.hl",
    Filename.concat candle_flyspeck_overlay_root
      "jHOLLight/caml/sections.hl",
    "f7f829fcc3465c1336bdd80f74ab148c");
   (Filename.concat candle_flyspeck_root "formal_lp/glpk/lpproc.ml",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/glpk/lpproc.ml",
    "0399bf375d48d4bb4de408e428b84ec3")];;

if List.length candle_flyspeck_normalized_sources <> 23 then
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
