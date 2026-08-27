#use "candle/build/insulate.ml";;
#use "candle/nums.ml";;
#use "candle/pretty.ml";;
#use "candle/ocaml.ml";;

candle_configure_manifest_process_inputs
  "candle/flyspeck_metadata/date.txt"
  "candle/flyspeck_metadata/user.txt";;

let candle_unix_process_to_string command =
  let channel = Unix.open_process_in command
  and buffer = Buffer.create 64 in
  let rec read () = Buffer.add_channel buffer channel 1; read () in
  try read () with End_of_file ->
    Unix.close_process_in channel;
    Buffer.contents buffer;;

if candle_unix_process_to_string "date" <> "1970-01-01T00:00:00Z\n" then
  failwith "deterministic date mismatch";;
if candle_unix_process_to_string "whoami" <> "candle-manifest\n" then
  failwith "deterministic user mismatch";;

let candle_unix_buffer = Buffer.create 0;;
Buffer.add_string candle_unix_buffer "serial";;
Buffer.add_char candle_unix_buffer 'i';;
Buffer.add_string candle_unix_buffer "ze";;
if Buffer.contents candle_unix_buffer <> "serialize" then
  failwith "Buffer append order mismatch";;
Buffer.reset candle_unix_buffer;;
if Buffer.contents candle_unix_buffer <> "" then
  failwith "Buffer reset mismatch";;

let candle_unix_rejects_command =
  try let _ = Unix.open_process_in "sh -c date" in false
  with Failure _ -> true;;
let candle_unix_rejects_clock =
  try let _ = Unix.gettimeofday () in false
  with Failure _ -> true;;
let candle_sys_rejects_command =
  try let _ = Sys.command "true" in false
  with Failure _ -> true;;

if not candle_unix_rejects_command || not candle_unix_rejects_clock ||
   not candle_sys_rejects_command then
  failwith "Unix fail-closed contract mismatch";;

print_endline "CANDLE_UNIX_METADATA_OK";;
