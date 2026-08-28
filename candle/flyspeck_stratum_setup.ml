(* Runtime setup for an authenticated cumulative Flyspeck stratum.  The
   generated runtime config must be loaded first.  Unlike flyspeck_loader.ml,
   this setup stops after strictbuild so the selected cumulative prefix can be
   executed and checked separately. *)

if candle_flyspeck_build_mode <> "stratum-runtime" then
  failwith "Flyspeck stratum setup requires stratum-runtime mode";;

#use "hol.ml";;

let candle_flyspeck_text_root =
  Filename.concat candle_flyspeck_root "text_formalization";;

Sys.configure_manifest_environment
  candle_hollight_root candle_flyspeck_text_root candle_hollight_root false;;

if Sys.getcwd () <> candle_hollight_root ||
   Sys.getenv "FLYSPECK_DIR" <> candle_flyspeck_text_root ||
   Sys.getenv "HOLLIGHT_DIR" <> candle_hollight_root then
  failwith "Flyspeck stratum manifest environment mismatch";;

let candle_flyspeck_stratum_verify_md5 label path expected =
  if not (Sys.file_exists path) then
    failwith ("missing Flyspeck stratum " ^ label ^ ": " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected then
    failwith ("Flyspeck stratum " ^ label ^ " digest mismatch: " ^ path);;

candle_flyspeck_stratum_verify_md5 "instrumented prefix"
  candle_flyspeck_stratum_program candle_flyspeck_stratum_program_md5;;

needs "candle/flyspeck_source_digests.ml";;
needs "candle/flyspeck_source_integrity.ml";;

candle_flyspeck_verify_sources 399 candle_hollight_root candle_flyspeck_root
  candle_flyspeck_source_digests;;

let candle_flyspeck_stratum_source_identity (source_root,source,digest) =
  let root =
    if source_root = "candle" then candle_hollight_root
    else if source_root = "flyspeck" then candle_flyspeck_root
    else failwith ("unknown Flyspeck source root: " ^ source_root) in
  let original = Filename.concat root source in
  original,(Filename.basename original,digest);;

Cakeml.configureSourceIdentities
  (map candle_flyspeck_stratum_source_identity
       candle_flyspeck_source_digests);;

if List.length candle_flyspeck_stratum_normalized_sources <>
     candle_flyspeck_stratum_normalization_count then
  failwith "incomplete Flyspeck stratum normalized source table";;

List.iter
  (fun (_,path,digest) ->
     candle_flyspeck_stratum_verify_md5 "normalized source" path digest)
  candle_flyspeck_stratum_normalized_sources;;

Cakeml.configureNormalizationOverlay
  (map (fun (original,normalized,_) -> original,normalized)
       candle_flyspeck_stratum_normalized_sources);;

if List.length candle_flyspeck_stratum_generated_inputs <> 43 then
  failwith "incomplete Flyspeck stratum generated-input table";;

List.iter
  (fun (path,digest) ->
     candle_flyspeck_stratum_verify_md5 "generated input" path digest)
  candle_flyspeck_stratum_generated_inputs;;

if List.length candle_flyspeck_lp_certificate_files <> 39 then
  failwith "incomplete Flyspeck LP certificate runtime list";;

let candle_flyspeck_stratum_date_input,
    candle_flyspeck_stratum_user_input =
  match candle_flyspeck_stratum_process_inputs with
  | [(date_input,date_digest); (user_input,user_digest)] ->
      candle_flyspeck_stratum_verify_md5
        "date process input" date_input date_digest;
      candle_flyspeck_stratum_verify_md5
        "user process input" user_input user_digest;
      date_input,user_input
  | _ -> failwith "Flyspeck stratum process-input order mismatch";;

candle_configure_manifest_process_inputs
  candle_flyspeck_stratum_date_input candle_flyspeck_stratum_user_input;;

let candle_flyspeck_stratum_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;

List.iter candle_flyspeck_stratum_add_load_path
  [candle_flyspeck_text_root;
   Filename.concat candle_flyspeck_root "formal_ineqs";
   Filename.concat candle_flyspeck_root "jHOLLight"];;

needs "build/strictbuild.hl";;

if !Cakeml.pendingLoadedSourceId <> None then
  failwith "pending Flyspeck source identity after strictbuild";;

let candle_flyspeck_stratum_initial_loaded_files = !loaded_files;;

if List.length candle_flyspeck_stratum_action_identities <>
     candle_flyspeck_stratum_action_count then
  failwith "Flyspeck stratum action identity count mismatch";;

let candle_flyspeck_stratum_previous_loaded_files = ref !loaded_files;;
let candle_flyspeck_stratum_action_events =
  ref ([]:(int * (string * string) * string) list);;

let candle_flyspeck_stratum_commit_action index expected_identity marker =
  if index <> List.length !candle_flyspeck_stratum_action_events then
    failwith "Flyspeck stratum action event index mismatch"
  else if List.nth candle_flyspeck_stratum_action_identities index <>
          expected_identity then
    failwith "Flyspeck stratum action event identity mismatch"
  else
    let previous = !candle_flyspeck_stratum_previous_loaded_files in
    let current = !loaded_files in
    let outcome =
      if current = previous then
        if List.mem expected_identity previous then "skip-ledger"
        else "skip-loader-cache"
      else if not (List.mem expected_identity previous) &&
              current = expected_identity :: previous then "load"
      else failwith "Flyspeck action has an unexpected loader identity delta" in
    candle_flyspeck_stratum_action_events :=
      (index,expected_identity,outcome) ::
      !candle_flyspeck_stratum_action_events;
    candle_flyspeck_stratum_previous_loaded_files := current;
    print_endline marker;;

print_endline
  ("CANDLE_FLYSPECK_STRATUM_PREFLIGHT_OK " ^
   candle_flyspeck_stratum_attempt_nonce);;
