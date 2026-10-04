(* Direct-state smoke for the two legacy nonlinear evaluator adaptations. *)

let _ =
  let _ =
    print_endline "CANDLE_CV_DIRECT_VERIFIER_DISPATCH phase=begin" in
  let vector = `x:real^6` in
  if M_taylor.get_dim vector <> 6 then
    failwith "direct verifier dispatch: dimension decoder mismatch"
  else
    let _ =
      print_endline "CANDLE_CV_DIRECT_VERIFIER_DISPATCH phase=dimension" in
    let function_term = `\x:real^6. sqrt(x$1)` in
    let variable,body = dest_abs function_term in
    let _ =
      if M_verifier_main.is_poly body then
        failwith "direct verifier dispatch: sqrt body classified as polynomial"
      else
        print_endline "CANDLE_CV_DIRECT_VERIFIER_DISPATCH phase=nonpolynomial" in
    let operator,argument = dest_comb body in
    let operator_name,_ = dest_const operator in
    let _ =
      if operator_name <> "sqrt" then
        failwith "direct verifier dispatch: unexpected unary operator"
      else
        print_endline "CANDLE_CV_DIRECT_VERIFIER_DISPATCH phase=unary-shape" in
    let argument_function = mk_abs (variable,argument) in
    let _ =
      if M_verifier_main.is_poly argument then
        print_endline "CANDLE_CV_DIRECT_VERIFIER_DISPATCH phase=argument-poly"
      else
        failwith "direct verifier dispatch: argument is not polynomial" in
    let _,_ =
      M_verifier_main.mk_funs 6 6 argument_function in
    let _ =
      print_endline "CANDLE_CV_DIRECT_VERIFIER_DISPATCH phase=argument" in
    let _,_ = M_verifier_main.mk_funs 6 6 function_term in
    print_endline
      "CANDLE_CV_DIRECT_VERIFIER_DISPATCH_OK dimension=6 unary_fallback=1";;
