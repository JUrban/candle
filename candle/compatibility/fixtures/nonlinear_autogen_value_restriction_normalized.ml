type candle_nonlinear_autogen_term = Candle_nonlinear_autogen_term of int;;

module Candle_nonlinear_autogen_value = struct
  let autogen = ref ([]:candle_nonlinear_autogen_term list);;
  let autogen_add term = autogen := !autogen @ [term];;
end;;

let _ = Candle_nonlinear_autogen_value.autogen_add
  (Candle_nonlinear_autogen_term 11);;

let candle_nonlinear_autogen_value_ok =
  !Candle_nonlinear_autogen_value.autogen =
    [Candle_nonlinear_autogen_term 11];;
