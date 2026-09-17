let original hypermap_id =
  let p = Printf.sprintf in
  [p "param card_node := %d;" 13;
   p "param hypermap_id := %s;" hypermap_id;
   p "param card_face := %d;\n" 21];;

let normalized hypermap_id =
  let p_int = Printf.sprintf in
  let p = Printf.sprintf in
  [p_int "param card_node := %d;" 13;
   p "param hypermap_id := %s;" hypermap_id;
   p_int "param card_face := %d;\n" 21];;

let () =
  let observed = original "HYPERMAP-7" in
  if observed = normalized "HYPERMAP-7" &&
     observed =
       ["param card_node := 13;";
        "param hypermap_id := HYPERMAP-7;";
        "param card_face := 21;\n"]
  then print_endline "LPPROC_FORMAT_ALIAS_OCAML_ORACLE_OK"
  else failwith "split format aliases changed native output";;
