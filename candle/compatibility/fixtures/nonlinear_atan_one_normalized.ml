let candle_float_of_int value =
  let rec add_ones remaining result =
    if remaining = 0 then result
    else add_ones (remaining - 1) (result +. 1.0) in
  if value < 0 then -. add_ones (-value) 0.0
  else add_ones value 0.0;;

let rec candle_x_pow_over_fact x k =
  if k <= 0 then 1.0
  else x /. candle_float_of_int k *. candle_x_pow_over_fact x (k - 1);;

let candle_n_of_p_cos x pp cond =
  let t = candle_float_of_int 200 ** candle_float_of_int (-pp - 1) in
  let rec try_i i =
    if i > 50 then failwith "candle_n_of_p_cos"
    else if cond i then
      let r = candle_x_pow_over_fact x (2 * (i + 1)) in
      if Cake.Double.(<=) r t then i else try_i (i + 1)
    else try_i (i + 1) in
  try_i 0;;

let rec candle_range first last =
  if first > last then [] else first :: candle_range (first + 1) last;;

let candle_pi_over_two = 1.5707963267948966;;
let candle_expected_degrees =
  [(0,4,3); (1,6,5); (2,6,7); (3,8,7); (4,8,9); (5,10,9);
   (6,10,11); (7,12,11); (8,12,13); (9,14,13); (10,14,15);
   (11,16,15); (12,16,17); (13,18,17); (14,18,19); (15,18,19);
   (16,20,19); (17,20,21); (18,22,21); (19,22,23); (20,22,23)];;
let candle_observed_degrees =
  List.map
    (fun pp ->
       pp,
       candle_n_of_p_cos candle_pi_over_two pp (fun i -> i land 1 = 0),
       candle_n_of_p_cos candle_pi_over_two pp (fun i -> i land 1 = 1))
    (candle_range 0 20);;

if candle_observed_degrees <> candle_expected_degrees
then failwith "Candle atan-one normalization mismatch"
else print_endline "NONLINEAR_ATAN_ONE_CANDLE_OK";;
