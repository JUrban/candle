(* DEVELOPMENT reproducer for Lpproc.modify_bb's local polymorphic helper. *)
let candle_lpproc_get_values key fields =
  List.map snd (List.filter (fun (field,_) -> field = key) fields);;

let candle_lpproc_modify_raw face_fields vertex_fields =
  let add key fields tail =
    (candle_lpproc_get_values key fields) @ tail in
  (add "face" face_fields [[9]],
   add "vertex" vertex_fields [9]);;

let candle_lpproc_raw_observation =
  candle_lpproc_modify_raw
    [("face",[1;2])] [("vertex",3)];;
