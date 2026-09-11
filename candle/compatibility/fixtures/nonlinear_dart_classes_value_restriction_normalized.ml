type candle_nonlinear_dart_thm = Candle_nonlinear_dart_thm of int;;

module Candle_nonlinear_dart_classes_value = struct
  let dart_classes = ref ([]:candle_nonlinear_dart_thm list);;
  let define_dart th =
    let _ = dart_classes := th::!dart_classes in
    th;;
end;;

let candle_nonlinear_dart_value =
  Candle_nonlinear_dart_classes_value.define_dart
    (Candle_nonlinear_dart_thm 7);;

let candle_nonlinear_dart_classes_value_ok =
  candle_nonlinear_dart_value = Candle_nonlinear_dart_thm 7 &&
  !Candle_nonlinear_dart_classes_value.dart_classes =
    [Candle_nonlinear_dart_thm 7];;
