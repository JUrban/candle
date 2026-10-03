(* Focused test for the direct-state reflected-checker [Num] alias surface. *)

needs "candle/cv_compute_num_module_compat.ml";;

let candle_cv_num_compat_two = Num.num_of_int 2;;
let candle_cv_num_compat_three = Num.num_of_int 3;;
let candle_cv_num_compat_half =
  Num.div_num (Num.num_of_int 1) candle_cv_num_compat_two;;

if not
     (Num.eq_num
        (Num.add_num candle_cv_num_compat_two candle_cv_num_compat_three)
        (Num.num_of_int 5)) ||
   not
     (Num.eq_num
        (Num.mul_num candle_cv_num_compat_two candle_cv_num_compat_three)
        (Num.num_of_int 6)) ||
   not
     (Num.eq_num
        (Num.power_num candle_cv_num_compat_two candle_cv_num_compat_three)
        (Num.num_of_int 8)) ||
   Num.int_of_num candle_cv_num_compat_half <> 0 ||
   not (Num.lt_num candle_cv_num_compat_half (Num.num_of_int 1)) ||
   not (Num.le_num candle_cv_num_compat_half candle_cv_num_compat_half) ||
   not
     (Num.eq_num (Num.max_num candle_cv_num_compat_half (Num.num_of_int 1))
        (Num.num_of_int 1)) ||
   not
     (Num.eq_num (Num.min_num candle_cv_num_compat_half (Num.num_of_int 1))
        candle_cv_num_compat_half) ||
   not
     (Num.eq_num (Num.minus_num candle_cv_num_compat_two)
        (Num.num_of_int (~-2)))
then failwith "direct reflected Num compatibility mismatch";;

print_endline
  "CANDLE_CV_NUM_MODULE_COMPAT_OK representation=existing-num aliases=14";;

