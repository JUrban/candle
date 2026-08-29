(* Loaded only after the exact strictbuild prefix has returned successfully. *)

let candle_flyspeck_dopen_identity_count identity =
  List.length (List.filter (fun observed -> observed = identity) !loaded_files);;

let candle_flyspeck_dopen_parser_identity,
    candle_flyspeck_dopen_debug_identity =
  match candle_flyspeck_dopen_action_identities with
  | [(_,parser_identity); (_,debug_identity)] ->
      parser_identity,debug_identity
  | _ -> failwith "Dopen prefix action identity order mismatch";;

if candle_flyspeck_dopen_identity_count
     candle_flyspeck_dopen_parser_identity <> 1 ||
   candle_flyspeck_dopen_identity_count
     candle_flyspeck_dopen_debug_identity <> 1 ||
   !Cakeml.pendingLoadedSourceIds <> [] then
  failwith "Dopen prefix loader action commit mismatch";;

if Parser_verbose.string_of_lexcodel [Ident "x"] <> "x   " ||
   Debug.parse_type_verbose "bool" <> bool_ty then
  failwith "Dopen prefix exported binding mismatch";;

print_endline "CANDLE_FLYSPECK_DOPEN_PREFIX_OK";;
