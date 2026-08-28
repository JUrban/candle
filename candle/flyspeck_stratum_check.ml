(* Loaded only after every action and output-only marker in the selected
   cumulative prefix has returned successfully. *)

let candle_flyspeck_stratum_identity_count identity =
  List.length (List.filter (fun observed -> observed = identity) !loaded_files);;

if !Cakeml.pendingLoadedSourceId <> None then
  failwith "pending Flyspeck source identity at stratum boundary";;

List.iter
  (fun identity ->
     if candle_flyspeck_stratum_identity_count identity < 1 then
       failwith "selected Flyspeck action identity is absent at stratum boundary")
  candle_flyspeck_stratum_action_identities;;

print_endline
  ("CANDLE_FLYSPECK_STRATUM_BOUNDARY_OK " ^
   candle_flyspeck_stratum_boundary ^ " " ^
   string_of_int candle_flyspeck_stratum_action_count);;
