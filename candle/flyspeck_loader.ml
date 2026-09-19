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
     "5aaca51e970777a80d2a1d963feeb2a2" then
  failwith "Flyspeck source digest program authentication failed";;

if not (Sys.file_exists candle_flyspeck_full_build_program) ||
   Digest.to_hex (Digest.file candle_flyspeck_full_build_program) <>
     "28ed5be32d3533d6caadd160ad00d154" then
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

(* The host-side normalizer materializes all fifty-four outputs in a separate tree;
   this process registers only the fifty-three selected by the direct source graph.
   The outer release manifest authenticates size and SHA-256; this process checks
   OCaml-compatible MD5 before registering exact original-to-normalized paths.
   The overlay root is never put on [load_path], so an extra output cannot shadow
   a pinned source; the unselected OCaml-3.10 output cannot enter the loader. *)
let candle_flyspeck_normalized_sources =
  [
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/main/prove_flyspeck_lp.hl",
    "a01c82d20e64cffe5a4a16bf1c08ad06");
   (Filename.concat candle_flyspeck_root
      "formal_lp/more_arith/prove_lp.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/more_arith/prove_lp.hl",
    "93a89444e9e90fa2392911a20ed13a72");
   (Filename.concat candle_flyspeck_text_root
      "general/lib.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/lib.hl",
    "9c119e851799375ea9e0b65080eafa0f");
   (Filename.concat candle_flyspeck_text_root
      "general/flyspeck_lib.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/flyspeck_lib.hl",
    "bd55c20647b6d66f47dd1b119c8a51d1");
   (Filename.concat candle_flyspeck_text_root
      "general/print_types.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/print_types.hl",
    "937774e3558ecfe48afda2f7f54dc5b9");
   (Filename.concat candle_flyspeck_text_root
      "jordan/tactics_jordan.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/tactics_jordan.hl",
    "eb149bb1ba9ab79c598f1e8467b0de45");
   (Filename.concat candle_flyspeck_text_root
      "general/serialization.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/serialization.hl",
    "1d7f8887a5f880ffebd96526d23e7a36");
   (Filename.concat candle_flyspeck_text_root
      "general/update_database_400.ml",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/update_database_400.ml",
    "85ffaa8772cbaf66897720a5bf6215bd");
   (Filename.concat candle_flyspeck_text_root
      "general/flyspeck_eval_4.14.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/flyspeck_eval_4.14.hl",
    "7ca870cd84b14e56da55eefa51a3828e");
   (Filename.concat candle_flyspeck_root
      "jHOLLight/caml/ssreflect.hl",
    Filename.concat candle_flyspeck_overlay_root
      "jHOLLight/caml/ssreflect.hl",
    "620d9c7687482fd95245e71aae89a553");
   (Filename.concat candle_flyspeck_text_root
      "tame/ssreflect/FNJLBXS-compiled.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/tame/ssreflect/FNJLBXS-compiled.hl",
    "349edbfdd14163c7c827b1b84b9fb66e");
   (Filename.concat candle_flyspeck_text_root
      "local/pent_hex.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/local/pent_hex.hl",
    "57de064a23be1517bbf5bb54e3950282");
   (Filename.concat candle_flyspeck_root
      "formal_ineqs/misc/misc_functions.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_ineqs/misc/misc_functions.hl",
    "c55a512aed20092ef945ae23aae90536");
   (Filename.concat candle_flyspeck_root
      "formal_ineqs/arith/arith_num.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_ineqs/arith/arith_num.hl",
    "d23f7c80b428cbb942fc11f81e083282");
   (Filename.concat candle_flyspeck_root
      "formal_ineqs/arith/arith_cache.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_ineqs/arith/arith_cache.hl",
    "4435dbc49c013c948975b7132906172c");
   (Filename.concat candle_flyspeck_root
      "formal_lp/glpk/glpk_link.ml",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/glpk/glpk_link.ml",
    "7034cd37bfda474171f5135efaf73a62");
   (Filename.concat candle_flyspeck_text_root
      "build/strictbuild.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/build/strictbuild.hl",
    "74e99f344b84daae4e890dd5b8126812");
   (Filename.concat candle_flyspeck_text_root
      "general/sphere.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/sphere.hl",
    "1e134647152103f755a0884313b3ad72");
   (Filename.concat candle_flyspeck_text_root
      "general/hales_tactic.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/hales_tactic.hl",
    "3945b87bbbcf00c8d4414542725feff9");
   (Filename.concat candle_flyspeck_text_root
      "general/truong_tactic.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/truong_tactic.hl",
    "1c9fd2e8252945b87d5a982d3ca4b446");
   (Filename.concat candle_flyspeck_text_root
      "jordan/hash_term.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/hash_term.hl",
    "4eb74e9553aae99fe76f8cc30472678b");
   (Filename.concat candle_flyspeck_text_root
      "jordan/float.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/float.hl",
    "05be687afff4d25745cd9496907cfb58");
   (Filename.concat candle_flyspeck_text_root
      "jordan/misc_defs_and_lemmas.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/jordan/misc_defs_and_lemmas.hl",
    "aaf5311e880df99921ae000a743256b4");
   (Filename.concat candle_flyspeck_text_root
      "general/parser_verbose.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/parser_verbose.hl",
    "3209a4491e57ae1c43afd673be59d7e3");
   (Filename.concat candle_flyspeck_text_root
      "general/debug.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/debug.hl",
    "318079c3dbff839fb4a778aff20a8204");
   (Filename.concat candle_flyspeck_text_root
      "general/hol_pervasives.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/general/hol_pervasives.hl",
    "fe90a871fbd8e40750f5445480af2e40");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/main/lp_certificate.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/main/lp_certificate.hl",
    "dcca51c5dc5dd5679f0b7337202c4f75");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/verify_all.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/verify_all.hl",
    "37d1180dfbfff7c2d6e524220dba4140");
   (Filename.concat candle_flyspeck_text_root
      "tame/linear_programming_results.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/tame/linear_programming_results.hl",
    "513f24367b716db938ffd02fe55641fd");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/calc_derivative.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/calc_derivative.hl",
    "0f281d7446704c953b6432caf15a419a");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/ineqdata3q1h.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/ineqdata3q1h.hl",
    "e456941142a1f3b1a3988640c50853c2");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/ineq.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/ineq.hl",
    "0a9d7a8267181e033f096727ca46375f");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/main_estimate_ineq.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/main_estimate_ineq.hl",
    "458d53a166b06a0c02586f196fb1fdbc");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/parse_ineq.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/parse_ineq.hl",
    "9308eb7403651593ba93be7ebdc9e1de");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/optimize.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/optimize.hl",
    "f18f79c743c1324839d655f38a0dcb92");
   (Filename.concat candle_flyspeck_text_root
      "nonlinear/merge_ineq.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/nonlinear/merge_ineq.hl",
    "c3dd4e6d2518fdfd0c92947380393965");
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
   (Filename.concat candle_flyspeck_root
      "jHOLLight/caml/sections.hl",
    Filename.concat candle_flyspeck_overlay_root
      "jHOLLight/caml/sections.hl",
    "f7f829fcc3465c1336bdd80f74ab148c");
   (Filename.concat candle_flyspeck_root
      "formal_lp/glpk/lpproc.ml",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/glpk/lpproc.ml",
    "f5ac089e3708ca15e8f678a5aafaf466");
   (Filename.concat candle_flyspeck_root
      "formal_lp/ineqs/constants_approx.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/ineqs/constants_approx.hl",
    "bef049628dd0aa5906b74553c86a5655");
   (Filename.concat candle_flyspeck_text_root
      "tame/good_list_archive.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/tame/good_list_archive.hl",
    "0dbf7b9572f1d6a5f5a2a70c8a7ea7b5");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/ineqs/lp_ineqs.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/ineqs/lp_ineqs.hl",
    "7a315e6e82c7e9f6ee43777933bf0110");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/ineqs/lp_body_ineqs.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/ineqs/lp_body_ineqs.hl",
    "cfd6585a2c79a24401482c0881d490d7");
   (Filename.concat candle_flyspeck_text_root
      "fan/Conforming.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/fan/Conforming.hl",
    "5a243f132756bcfdc6fcdc324fc760ec");
   (Filename.concat candle_flyspeck_text_root
      "packing/EMNWUUS.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/packing/EMNWUUS.hl",
    "49847a2b33348b673321c1daca202ea3");
   (Filename.concat candle_flyspeck_text_root
      "packing/OXLZLEZ2.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/packing/OXLZLEZ2.hl",
    "1e9d210b32fedae512af4154ca1abdc9");
   (Filename.concat candle_flyspeck_text_root
      "packing/AJRIPQN.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/packing/AJRIPQN.hl",
    "803d1bae0841fb4d55d6b14a04934576");
   (Filename.concat candle_flyspeck_text_root
      "packing/marchal3.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/packing/marchal3.hl",
    "be8cba1fe893b5bcff75e3a6a4424219");
   (Filename.concat candle_flyspeck_text_root
      "packing/SLTSTLO.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/packing/SLTSTLO.hl",
    "78e1641aace383531357719f10fa90cb");
   (Filename.concat candle_flyspeck_text_root
      "local/ZLZTHIC.hl",
    Filename.concat candle_flyspeck_overlay_root
      "text_formalization/local/ZLZTHIC.hl",
    "94685b843623c0918058a08cd8c984a8");
   (Filename.concat candle_flyspeck_root
      "formal_lp/hypermap/ineqs/lp_ineqs_quads-compiled.hl",
    Filename.concat candle_flyspeck_overlay_root
      "formal_lp/hypermap/ineqs/lp_ineqs_quads-compiled.hl",
    "9de99cf5a983e899733f76058a0c8814")];;

if List.length candle_flyspeck_normalized_sources <> 53 then
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
  [candle_hollight_root;
   candle_flyspeck_text_root;
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
