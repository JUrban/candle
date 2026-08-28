(* Test-only setup for the authenticated direct Flyspeck Dopen prefix.
   The generated config must be loaded first.  This deliberately does not load
   flyspeck_loader.ml or the 297-entry full-build driver. *)

if candle_flyspeck_build_mode <> "dopen-prefix" then
  failwith "Dopen prefix requires dopen-prefix mode";;

#use "hol.ml";;

let candle_flyspeck_text_root =
  Filename.concat candle_flyspeck_root "text_formalization";;

Sys.configure_manifest_environment
  candle_hollight_root candle_flyspeck_text_root candle_hollight_root false;;

if Sys.getcwd () <> candle_hollight_root ||
   Sys.getenv "FLYSPECK_DIR" <> candle_flyspeck_text_root ||
   Sys.getenv "HOLLIGHT_DIR" <> candle_hollight_root then
  failwith "Dopen prefix manifest environment mismatch";;

let candle_flyspeck_dopen_verify_md5 label path expected =
  if not (Sys.file_exists path) then
    failwith ("missing Dopen prefix " ^ label ^ ": " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected then
    failwith ("Dopen prefix " ^ label ^ " digest mismatch: " ^ path);;

List.iter
  (fun (path,digest) ->
     candle_flyspeck_dopen_verify_md5 "original source" path digest)
  candle_flyspeck_dopen_original_sources;;

List.iter
  (fun (_,path,digest) ->
     candle_flyspeck_dopen_verify_md5 "normalized source" path digest)
  candle_flyspeck_dopen_normalized_sources;;

candle_flyspeck_dopen_verify_md5 "strictbuild prefix"
  candle_flyspeck_dopen_prefix candle_flyspeck_dopen_prefix_md5;;

let candle_flyspeck_dopen_date_input,
    candle_flyspeck_dopen_user_input =
  match candle_flyspeck_dopen_process_inputs with
  | [(date_input,date_digest); (user_input,user_digest)] ->
      candle_flyspeck_dopen_verify_md5 "date input" date_input date_digest;
      candle_flyspeck_dopen_verify_md5 "user input" user_input user_digest;
      date_input,user_input
  | _ -> failwith "Dopen prefix process-input order mismatch";;

candle_configure_manifest_process_inputs
  candle_flyspeck_dopen_date_input candle_flyspeck_dopen_user_input;;

Cakeml.configureSourceIdentities
  candle_flyspeck_dopen_action_identities;;

Cakeml.configureNormalizationOverlay
  (map (fun (original,normalized,_) -> original,normalized)
       candle_flyspeck_dopen_normalized_sources);;

let candle_flyspeck_dopen_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;

List.iter candle_flyspeck_dopen_add_load_path
  [candle_flyspeck_text_root;
   Filename.concat candle_flyspeck_root "formal_ineqs";
   Filename.concat candle_flyspeck_root "jHOLLight"];;

print_endline "CANDLE_FLYSPECK_DOPEN_PREFIX_PREFLIGHT_OK";;
