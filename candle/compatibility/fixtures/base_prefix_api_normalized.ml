let candle_flyspeck_normalized_all_forall bod =
  let mk_forall = mk_binder "!" in
  itlist (curry mk_forall) (sort Term.(<) (frees bod)) bod;;

let candle_flyspeck_normalized_flatten_frees tms =
  List.concat (map frees tms);;

let candle_flyspeck_normalized_output_filestring tmpfile a =
  let outs = open_out tmpfile in
  let _ = try output_string outs a
          with _ as t -> (close_out outs; raise t) in
  close_out outs;;

let build_and_report () : unit =
  failwith "Candle Flyspeck: dynamic strictbuild build_and_report is disabled by the static manifest";;

let candle_flyspeck_build_and_report_fail_closed =
  try build_and_report (); false with Failure message ->
    message =
      "Candle Flyspeck: dynamic strictbuild build_and_report is disabled by the static manifest";;

let candle_flyspeck_base_prefix_api_oracle_ok =
  let aty = mk_vartype "A" in
  let x = mk_var("x",aty) in
  let y = mk_var("y",aty) in
  let z = mk_var("z",aty) in
  let body = mk_eq(x,y) in
  let quantified = candle_flyspeck_normalized_all_forall body in
  let binders,result = strip_forall quantified in
  binders = sort Term.(<) [x;y] && result = body &&
  candle_flyspeck_normalized_flatten_frees
    [mk_eq(x,y); mk_eq(y,z)] = [x;y;y;z] &&
  candle_flyspeck_build_and_report_fail_closed;;
