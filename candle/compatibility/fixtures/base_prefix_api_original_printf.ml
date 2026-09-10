let candle_flyspeck_original_output_filestring tmpfile a =
  let outs = open_out tmpfile in
  let _ = try Printf.fprintf outs "%s" a
          with _ as t -> (close_out outs; raise t) in
  close_out outs;;
