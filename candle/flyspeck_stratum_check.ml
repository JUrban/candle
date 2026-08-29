(* Loaded only after every action and its exact loader-ledger transition check
   in the selected cumulative prefix has returned successfully. *)

if !Cakeml.pendingLoadedSourceIds <> [] then
  failwith "pending Flyspeck source identity at stratum boundary";;

if List.length !candle_flyspeck_stratum_action_events <>
     candle_flyspeck_stratum_action_count then
  failwith "incomplete Flyspeck stratum action event ledger";;

let candle_flyspeck_stratum_observed_action_identities =
  rev (map (fun (_,identity,_) -> identity)
           !candle_flyspeck_stratum_action_events);;

if candle_flyspeck_stratum_observed_action_identities <>
     candle_flyspeck_stratum_action_identities then
  failwith "Flyspeck stratum action event order mismatch";;

if !loaded_files <> !candle_flyspeck_stratum_previous_loaded_files then
  failwith "Flyspeck loader identity ledger changed after the final action";;

print_endline
  ("CANDLE_FLYSPECK_STRATUM_BOUNDARY_OK " ^
   candle_flyspeck_stratum_attempt_nonce ^ " " ^
   candle_flyspeck_stratum_boundary ^ " " ^
   string_of_int candle_flyspeck_stratum_action_count);;
