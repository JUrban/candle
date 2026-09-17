(* Duplicate the same pure helper at its second concrete type. *)
let candle_lpproc_get_values key fields =
  List.map snd (List.filter (fun (field,_) -> field = key) fields);;

let candle_lpproc_modify_normalized face_fields vertex_fields =
  let add key fields tail =
    (candle_lpproc_get_values key fields) @ tail in
  let addv key fields tail =
    (candle_lpproc_get_values key fields) @ tail in
  (add "face" face_fields [[9]],
   addv "vertex" vertex_fields [9]);;

let candle_lpproc_normalized_observation =
  candle_lpproc_modify_normalized
    [("face",[1;2])] [("vertex",3)];;

let candle_lpproc_local_polymorphism_ok =
  candle_lpproc_normalized_observation = ([[1;2];[9]],[3;9]);;
