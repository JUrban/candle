let original r = r > 11.9999;;

module Float = struct
  let flyspeck_shadow = true
end;;

let normalized r = Stdlib.Float.compare r 11.9999 = 1;;

let cases =
  [0.0; 11.9999; 12.0; infinity; 0.0 /. 0.0];;

let () =
  if List.for_all (fun value -> original value = normalized value) cases then
    print_endline "LPPROC_FLOAT_COMPARE_OCAML_ORACLE_OK"
  else
    failwith "explicit float comparator changed feasibility threshold";;
