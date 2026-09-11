type candle_nonlinear_texmarker =
  | Candle_nonlinear_section
  | Candle_nonlinear_ineqdoc
  | Candle_nonlinear_comment;;

module Candle_nonlinear_ineqdoc_value = struct
  let ineqdoc =
    ref ([]:(candle_nonlinear_texmarker * string * string) list);;
  let addtex (marker,name,text) =
    ineqdoc := (marker,name,text)::!ineqdoc;;
end;;

let _ = Candle_nonlinear_ineqdoc_value.addtex
  (Candle_nonlinear_section,"section","text");;

let candle_nonlinear_ineqdoc_value_ok =
  !Candle_nonlinear_ineqdoc_value.ineqdoc =
    [(Candle_nonlinear_section,"section","text")];;
