type flyspeck_parser_mini_pretype = Flyspeck_parser_mini_dpty;;

type flyspeck_parser_mini_preterm =
  Flyspeck_parser_mini_varp of string * flyspeck_parser_mini_pretype;;

let flyspeck_parser_mini_generator =
  let counter = ref 0 in
  fun () ->
    let count = !counter in
    (counter := count + 1;
     let name = "GEN%PVAR%" ^ string_of_int count in
     Flyspeck_parser_mini_varp (name,Flyspeck_parser_mini_dpty));;

let flyspeck_parser_mini_result0 = flyspeck_parser_mini_generator ();;
let flyspeck_parser_mini_result1 = flyspeck_parser_mini_generator ();;

let flyspeck_parser_tuple_constructor_oracle_ok =
  flyspeck_parser_mini_result0 =
    Flyspeck_parser_mini_varp
      ("GEN%PVAR%0",Flyspeck_parser_mini_dpty) &&
  flyspeck_parser_mini_result1 =
    Flyspeck_parser_mini_varp
      ("GEN%PVAR%1",Flyspeck_parser_mini_dpty);;
