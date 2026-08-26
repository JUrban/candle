(* Exercise a safe PFT/DMTCP boundary.  In dmtcp mode, the first generation
   writes a deliberately invalid tail and is killed by the checkpoint command.
   The restored process truncates that tail before continuing the same logical
   stream. *)

let resume_hollight_dir =
  try Sys.getenv "HOLLIGHT_DIR"
  with Not_found -> failwith "HOLLIGHT_DIR is not set";;

let resume_output =
  try Sys.getenv "CANDLE_PFT_OUTPUT"
  with Not_found -> failwith "CANDLE_PFT_OUTPUT is not set";;

let resume_mode =
  try Sys.getenv "CANDLE_PFT_RESUME_MODE"
  with Not_found -> failwith "CANDLE_PFT_RESUME_MODE is not set";;

let resume_marker =
  try Sys.getenv "CANDLE_PFT_RESUME_MARKER"
  with Not_found -> failwith "CANDLE_PFT_RESUME_MARKER is not set";;

needs (Filename.concat resume_hollight_dir "ProofTrace/pft.ml");;
pft_stream_checkpoint_interval := 20;;
start_pft_stream resume_output;;

let resume_before = prove (`T`, REWRITE_TAC []);;
save_pft_stream_target "candle$RESUME_BEFORE" resume_before;;

let resume_checkpoint = prepare_pft_stream_checkpoint();;
Printf.printf "PFT_CHECKPOINT_READY offset=%d commands=%d\n%!"
  resume_checkpoint.checkpoint_offset
  resume_checkpoint.checkpoint_command_count;;

if resume_mode = "baseline" then
  restore_pft_stream_checkpoint resume_checkpoint
else if resume_mode = "dmtcp" then begin
  let state = pft_stream_state() in
  output_string state.channel "\254stale-after-checkpoint";
  flush state.channel;
  let channel = open_out resume_marker in
  output_string channel "checkpoint requested\n";
  close_out channel;
  (try ignore (Sys.command "dmtcp_command -kc")
   with Sys_error _ -> ());
  restore_pft_stream_checkpoint resume_checkpoint;
  print_endline "PFT_CHECKPOINT_RESTORED"
end else
  failwith "CANDLE_PFT_RESUME_MODE must be baseline or dmtcp";;

let resume_after = CONJ resume_before resume_before;;
save_pft_stream_target "candle$RESUME_AFTER" resume_after;;

let resume_export = finish_pft_stream();;
Printf.printf "PFT_RESUME_SMOKE_OK commands=%d limits=(%d,%d,%d)\n%!"
  resume_export.export_commands
  resume_export.export_type_count
  resume_export.export_term_count
  resume_export.export_theorem_count;;
