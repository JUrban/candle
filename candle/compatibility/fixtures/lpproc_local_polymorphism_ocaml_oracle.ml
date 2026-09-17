let get_values key fields =
  List.map snd (List.filter (fun (field,_) -> field = key) fields);;

let original face_fields vertex_fields =
  let add key fields tail = (get_values key fields) @ tail in
  (add "face" face_fields [[9]], add "vertex" vertex_fields [9]);;

let normalized face_fields vertex_fields =
  let add key fields tail = (get_values key fields) @ tail in
  let addv key fields tail = (get_values key fields) @ tail in
  (add "face" face_fields [[9]], addv "vertex" vertex_fields [9]);;

let () =
  let expected = ([[1;2];[9]],[3;9]) in
  let observed_original =
    original [("face",[1;2])] [("vertex",3)] in
  let observed_normalized =
    normalized [("face",[1;2])] [("vertex",3)] in
  if observed_original = expected && observed_normalized = observed_original
  then print_endline "LPPROC_LOCAL_POLYMORPHISM_OCAML_ORACLE_OK"
  else failwith "duplicated local helper changed native behavior";;
