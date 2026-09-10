let flyspeck_debug_original_expander = !Cakeml.unquote;;

let flyspeck_debug_verbose_expander s = "verbose:" ^ s;;

let flyspeck_debug_set_verbose_parsing () =
  Cakeml.unquote := flyspeck_debug_verbose_expander;;

let flyspeck_debug_restore_parsing () =
  Cakeml.unquote := flyspeck_debug_original_expander;;

flyspeck_debug_set_verbose_parsing ();;

let flyspeck_debug_verbose_registration_ok =
  (!Cakeml.unquote) "probe" = "verbose:probe";;

flyspeck_debug_restore_parsing ();;

let flyspeck_debug_restore_registration_ok =
  (!Cakeml.unquote) "probe" = flyspeck_debug_original_expander "probe";;

let flyspeck_debug_registration_oracle_ok =
  flyspeck_debug_verbose_registration_ok &&
  flyspeck_debug_restore_registration_ok;;

if flyspeck_debug_registration_oracle_ok then ()
else failwith "Flyspeck Debug registration oracle mismatch";;
