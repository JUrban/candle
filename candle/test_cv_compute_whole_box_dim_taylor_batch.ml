(* Multiple data-only whole-box experiments in one restored checker state. *)
needs "candle/test_cv_compute_whole_box_dim_taylor.ml";;

let candle_dim_taylor_expect_accept label boxes_rep =
  let check_tm =
    list_mk_comb
     (`candle_cv_q_dim_whole_box_check`,
      [candle_dim_taylor_pf_rep;candle_dim_taylor_pds_rep;
       candle_dim_taylor_pdds_rep;boxes_rep]) in
  let started = Unix.gettimeofday() in
  let check_th =
    compute candle_cv_q_dim_whole_box_compute_eqs check_tm in
  let elapsed = Unix.gettimeofday() -. started in
  let verdict,_ =
    candle_dim_taylor_dest_pair (rand (concl check_th)) in
  if hyp check_th <> [] then
    failwith ("conditional Taylor acceptance theorem: " ^ label)
  else if not (aconv verdict `Cexp_num 1`) then
    failwith ("dimension-parametric Taylor checker rejected: " ^ label)
  else
    print_endline
     ("CANDLE_CV_WHOLE_BOX_DIM_TAYLOR_BATCH label=" ^ label ^
      " status=accept compute_seconds=" ^ string_of_float elapsed);;

let candle_dim_taylor_point_zero_box =
 `((((0,0),0),((0,0),0)):
   ((num#num)#num)#((num#num)#num))`;;

let candle_dim_taylor_point_zero_boxes_rep =
  candle_dim_taylor_cval_list
    (replicate
      (candle_dim_taylor_interval_rep candle_dim_taylor_point_zero_box) 6);;

let candle_dim_taylor_narrow_box =
 `((((0,0),0),((1,0),255)):
   ((num#num)#num)#((num#num)#num))`;;

let candle_dim_taylor_narrow_boxes_rep =
  candle_dim_taylor_cval_list
    (replicate
      (candle_dim_taylor_interval_rep candle_dim_taylor_narrow_box) 6);;

let _ =
  candle_dim_taylor_expect_accept
    "point-zero" candle_dim_taylor_point_zero_boxes_rep;;

let _ =
  candle_dim_taylor_expect_accept
    "narrow-uniform" candle_dim_taylor_narrow_boxes_rep;;

print_endline "CANDLE_CV_WHOLE_BOX_DIM_TAYLOR_BATCH_OK";;
