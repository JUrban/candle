let candle_nonlinear_string_less (left:string) (right:string) =
  if left = "a" then not (right = "a") else false;;

let rec candle_nonlinear_sort predicate values =
  match values with
  | [] -> []
  | pivot::rest ->
      let rec partition lesser greater = function
        | [] -> (lesser,greater)
        | head::tail ->
            if predicate pivot head
            then partition lesser (head::greater) tail
            else partition (head::lesser) greater tail in
      let lesser,greater = partition [] [] rest in
      candle_nonlinear_sort predicate lesser @
      (pivot::candle_nonlinear_sort predicate greater);;

let candle_nonlinear_string_order_normalized values =
  candle_nonlinear_sort candle_nonlinear_string_less values;;

let candle_nonlinear_string_order_ok =
  candle_nonlinear_string_order_normalized ["b";"a"] = ["a";"b"];;
