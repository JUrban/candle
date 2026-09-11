type candle_calc_derivative_mini_type = Candle_calc_derivative_mini_real;;

type candle_calc_derivative_mini_term =
  Candle_calc_derivative_mini_var of string * candle_calc_derivative_mini_type;;

let candle_calc_derivative_mini_mk_var (name,ty) =
  Candle_calc_derivative_mini_var(name,ty);;

let candle_calc_derivative_mini_get_var =
  let real_ty = Candle_calc_derivative_mini_real in
  let counter = ref 0 in
  fun () ->
    let _ = counter := !counter + 1 in
    let name = "F" ^ string_of_int !counter in
    candle_calc_derivative_mini_mk_var (name,real_ty);;

let candle_calc_derivative_mini_result1 =
  candle_calc_derivative_mini_get_var ();;
let candle_calc_derivative_mini_result2 =
  candle_calc_derivative_mini_get_var ();;

let candle_calc_derivative_tuple_constructor_oracle_ok =
  candle_calc_derivative_mini_result1 =
    Candle_calc_derivative_mini_var
      ("F1",Candle_calc_derivative_mini_real) &&
  candle_calc_derivative_mini_result2 =
    Candle_calc_derivative_mini_var
      ("F2",Candle_calc_derivative_mini_real);;
