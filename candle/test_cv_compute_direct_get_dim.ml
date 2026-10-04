(* Direct-state smoke for the legacy nonlinear vector-dimension decoder. *)

let _ =
  let vector = `x:real^6` in
  let result = M_taylor.get_dim vector in
  if result <> 6 then
    failwith "direct get_dim: expected dimension six"
  else
    print_endline "CANDLE_CV_DIRECT_GET_DIM_OK dimension=6";;
