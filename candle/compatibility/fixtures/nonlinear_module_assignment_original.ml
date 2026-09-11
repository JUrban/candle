let candle_nonlinear_assignment_state = ref ([]:int list);;

let candle_nonlinear_assignment_remove value =
  candle_nonlinear_assignment_state :=
    List.filter (fun item -> not (item = value)) !candle_nonlinear_assignment_state;;

let candle_nonlinear_assignment_ok =
  let _ = candle_nonlinear_assignment_state := [1;2;3;2] in
  let _ = candle_nonlinear_assignment_remove 2 in
  !candle_nonlinear_assignment_state = [1;3];;
