let rec x_pow_over_fact x k =
  if k <= 0 then 1.0
  else x /. float_of_int k *. x_pow_over_fact x (k - 1);;

let n_of_p_cos x pp cond =
  let t = float_of_int 200 ** float_of_int (-pp - 1) in
  let rec try_i i =
    if i > 50 then failwith "n_of_p_cos"
    else if cond i then
      let r = x_pow_over_fact x (2 * (i + 1)) in
      if r <= t then i else try_i (i + 1)
    else try_i (i + 1) in
  try_i 0;;

let rec range first last =
  if first > last then [] else first :: range (first + 1) last;;

let native_pi_over_two = 2.0 *. atan 1.0;;
let literal_pi_over_two = 1.5707963267948966;;
let expected_degrees =
  [(0,4,3); (1,6,5); (2,6,7); (3,8,7); (4,8,9); (5,10,9);
   (6,10,11); (7,12,11); (8,12,13); (9,14,13); (10,14,15);
   (11,16,15); (12,16,17); (13,18,17); (14,18,19); (15,18,19);
   (16,20,19); (17,20,21); (18,22,21); (19,22,23); (20,22,23)];;
let observed_degrees =
  List.map
    (fun pp ->
       pp,
       n_of_p_cos native_pi_over_two pp (fun i -> i land 1 = 0),
       n_of_p_cos native_pi_over_two pp (fun i -> i land 1 = 1))
    (range 0 20);;

if Int64.bits_of_float native_pi_over_two <>
     Int64.bits_of_float literal_pi_over_two ||
   observed_degrees <> expected_degrees
then failwith "native atan-one oracle mismatch"
else print_endline "NONLINEAR_ATAN_ONE_OCAML_ORACLE_OK";;
