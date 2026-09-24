(* ========================================================================== *)
(* Capture every pass box from the already authenticated genuine inequality. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The real-functions checkpoint supplies the     *)
(* source identity and formal/informal verifier records.  This continuation   *)
(* reruns only certificate search and adaptive precision selection, then      *)
(* serializes the exact logical boxes used by all pass leaves.                 *)
(* ========================================================================== *)

let candle_nl_batch_search_options =
  Candle_informal_search_options.make
    !candle_nl_capture_params.raw_intervals0 1e-10 200 6 0;;

let candle_nl_batch_search_functions =
  map
    (fun f -> Candle_informal_verifier_record.f f,
      Candle_informal_verifier_record.taylor f)
    candle_nl_capture_informal_functions;;

let candle_nl_batch_informal_domain =
  Informal_taylor.mk_m_center_domain
    6 candle_nl_capture_xx2 candle_nl_capture_zz2;;

let candle_nl_batch_certificate =
  Informal_search.construct_certificate
    candle_nl_batch_search_options
    candle_nl_batch_informal_domain
    candle_nl_batch_search_functions;;

let candle_nl_batch_stats =
  Certificate.result_stats candle_nl_batch_certificate;;

if candle_nl_batch_stats.pass <> 16 ||
   candle_nl_batch_stats.pass_raw <> 0 ||
   candle_nl_batch_stats.pass_mono <> 0 ||
   candle_nl_batch_stats.mono <> 0 ||
   candle_nl_batch_stats.glue <> 15 ||
   candle_nl_batch_stats.glue_convex <> 0 then
  failwith "real-leaf batch certificate shape drift";;

let candle_nl_batch_precision_tree,_ =
  Informal_verifier.m_verify_raw0
    6 1 6 candle_nl_capture_informal_functions
    candle_nl_batch_certificate
    candle_nl_capture_xx2 candle_nl_capture_zz2;;

let candle_nl_batch_root_domain =
  M_taylor.mk_m_center_domain
    candle_nl_capture_dimension 6
    candle_nl_capture_xx1 candle_nl_capture_zz1;;

let rec candle_nl_batch_collect_leaves path domain_th tree =
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      if raw_flag then failwith "unexpected raw nonlinear batch leaf"
      else [rev path,status,function_index,domain_th]
  | P_result_glue (status,split_index,convex_flag,left,right) ->
      if convex_flag then failwith "unexpected convex nonlinear batch branch"
      else
        let left_domain,right_domain =
          M_verifier.split_domain
            candle_nl_capture_dimension 6 (split_index + 1) domain_th in
        candle_nl_batch_collect_leaves
          ((status.pp,split_index + 1,0) :: path) left_domain left @
        candle_nl_batch_collect_leaves
          ((status.pp,split_index + 1,1) :: path) right_domain right
  | P_result_mono _ ->
      failwith "unexpected monotonicity node in nonlinear batch"
  | P_result_ref _ ->
      failwith "unexpected reference node in nonlinear batch";;

let candle_nl_batch_leaves =
  candle_nl_batch_collect_leaves
    [] candle_nl_batch_root_domain candle_nl_batch_precision_tree;;

if length candle_nl_batch_leaves <> 16 then
  failwith "real-leaf batch leaf count drift";;

let candle_nl_batch_path_string path =
  String.concat ","
    (map
      (fun (precision,index,side) ->
        string_of_int precision ^ ":" ^ string_of_int index ^ ":" ^
        string_of_int side)
      path);;

let candle_nl_batch_bound_rational tm =
  try rat_of_term tm with Failure _ ->
    rat_of_term
      (rand (concl (Arith_float.FLOAT_TO_NUM_CONV tm)));;

let candle_nl_batch_box_identity lower upper =
  String.concat ","
    (map
      (fun tm -> Num.string_of_num (candle_nl_batch_bound_rational tm))
      lower) ^ "|" ^
  String.concat ","
    (map
      (fun tm -> Num.string_of_num (candle_nl_batch_bound_rational tm))
      upper);;

let candle_nl_batch_print_leaf index (path,status,function_index,domain_th) =
  let box,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let lower,upper = dest_pair box in
  let lower_terms = dest_vector lower in
  let upper_terms = dest_vector upper in
  print_endline
    ("CANDLE_NL_BATCH_LEAF index=" ^ string_of_int index ^
     " function_index=" ^ string_of_int function_index ^
     " pp=" ^ string_of_int status.pp ^
     " path=" ^ candle_nl_batch_path_string path ^
     " box_md5=" ^
     Digest.to_hex
       (Digest.string
         (candle_nl_batch_box_identity lower_terms upper_terms)));
  candle_nl_capture_print_term
    ("batch_leaf_" ^ string_of_int index ^ "_lower_list")
    (mk_real_list lower_terms);
  candle_nl_capture_print_term
    ("batch_leaf_" ^ string_of_int index ^ "_upper_list")
    (mk_real_list upper_terms);;

let _ =
  do_list
    (fun (index,leaf) -> candle_nl_batch_print_leaf index leaf)
    (zip (0--15) candle_nl_batch_leaves);;

let _ = print_endline "CANDLE_NL_REAL_LEAF_BATCH_CAPTURE_OK";;
