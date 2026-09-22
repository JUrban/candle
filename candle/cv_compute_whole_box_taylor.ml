(* ========================================================================== *)
(* One-call exact Taylor arithmetic for a two-variable whole-box checker.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The six programs denote f, fx, fy, fxx, fxy, *)
(* and fyy.  Given only their authenticated encodings and the original box,   *)
(* the reflected computation derives midpoint/radii, evaluates every bound,   *)
(* forms the complete second-order Taylor upper bound, checks the box and      *)
(* sign conditions, and returns both verdict and upper bound.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_program.ml";;

module Candle_cv_whole_box_taylor = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;

let candle_q_half_def = new_definition
 `candle_q_half = (((1,0),1):(num#num)#num)`;;

let candle_q_two_def = new_definition
 `candle_q_two = (((2,0),0):(num#num)#num)`;;

let candle_q_midpoint_def = new_definition
 `candle_q_midpoint
    (i:((num#num)#num)#((num#num)#num)) =
    candle_q_mul candle_q_half (candle_q_add (FST i) (SND i))`;;

let candle_q_radius_def = new_definition
 `candle_q_radius
    (i:((num#num)#num)#((num#num)#num)) =
    candle_q_mul candle_q_half
      (candle_q_add (SND i) (candle_q_neg (FST i)))`;;

let candle_q_point_interval_def = new_definition
 `candle_q_point_interval (q:(num#num)#num) = (q,q)`;;

let candle_q_abs_upper_def = new_definition
 `candle_q_abs_upper
    (i:((num#num)#num)#((num#num)#num)) =
    candle_q_max (candle_q_neg (FST i)) (SND i)`;;

let candle_q_program_interval_def = new_definition
 `candle_q_program_interval env program =
    candle_q_interval_head (candle_q_interval_run env program [])`;;

let candle_q_taylor_upper_def = new_definition
 `candle_q_taylor_upper wx wy f df_x df_y ddf_xx ddf_xy ddf_yy =
    candle_q_add (SND f)
      (candle_q_add
        (candle_q_add
          (candle_q_mul wx (candle_q_abs_upper df_x))
          (candle_q_mul wy (candle_q_abs_upper df_y)))
        (candle_q_mul candle_q_half
          (candle_q_add
            (candle_q_mul wx
              (candle_q_add
                (candle_q_mul wx (candle_q_abs_upper ddf_xx))
                (candle_q_mul candle_q_two
                  (candle_q_mul wy (candle_q_abs_upper ddf_xy)))))
            (candle_q_mul wy
              (candle_q_mul wy (candle_q_abs_upper ddf_yy))))))`;;

let candle_q_whole_box_upper_def = new_definition
 `candle_q_whole_box_upper pf pfx pfy pfxx pfxy pfyy ix iy =
    candle_q_taylor_upper
      (candle_q_radius ix) (candle_q_radius iy)
      (candle_q_program_interval
        [candle_q_point_interval (candle_q_midpoint ix);
         candle_q_point_interval (candle_q_midpoint iy)] pf)
      (candle_q_program_interval
        [candle_q_point_interval (candle_q_midpoint ix);
         candle_q_point_interval (candle_q_midpoint iy)] pfx)
      (candle_q_program_interval
        [candle_q_point_interval (candle_q_midpoint ix);
         candle_q_point_interval (candle_q_midpoint iy)] pfy)
      (candle_q_program_interval [ix;iy] pfxx)
      (candle_q_program_interval [ix;iy] pfxy)
      (candle_q_program_interval [ix;iy] pfyy)`;;

let candle_q_box_valid_def = new_definition
 `candle_q_box_valid ix iy <=>
    candle_q_le (FST ix) (SND ix) /\
    candle_q_le (FST iy) (SND iy)`;;

let candle_q_whole_box_accept_def = new_definition
 `candle_q_whole_box_accept pf pfx pfy pfxx pfxy pfyy ix iy <=>
    candle_q_box_valid ix iy /\
    ~(candle_q_le candle_q_zero
       (candle_q_whole_box_upper pf pfx pfy pfxx pfxy pfyy ix iy))`;;

let candle_q_real_half = prove
 (`candle_q_real candle_q_half = inv(&2)`,
  REWRITE_TAC[candle_q_half_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_real_two = prove
 (`candle_q_real candle_q_two = &2`,
  REWRITE_TAC[candle_q_two_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_midpoint_real = prove
 (`!i. candle_q_real (candle_q_midpoint i) =
       inv(&2) * (candle_q_real (FST i) + candle_q_real (SND i))`,
  REWRITE_TAC[candle_q_midpoint_def; candle_q_real_mul;
              candle_q_real_add; candle_q_real_half]);;

let candle_q_radius_real = prove
 (`!i. candle_q_real (candle_q_radius i) =
       inv(&2) * (candle_q_real (SND i) - candle_q_real (FST i))`,
  REWRITE_TAC[candle_q_radius_def; candle_q_real_mul;
              candle_q_real_add; candle_q_real_neg;
              candle_q_real_half] THEN REAL_ARITH_TAC);;

let candle_real_abs_interval_upper = prove
 (`!lo hi x:real. lo <= x /\ x <= hi ==> abs x <= max (--lo) hi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`--lo:real`; `hi:real`] REAL_MAX_MAX) THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC);;

let candle_q_abs_upper_sound = prove
 (`!i x. candle_q_interval_contains i x
         ==> abs x <= candle_q_real (candle_q_abs_upper i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def; candle_q_abs_upper_def;
              candle_q_max_real; candle_q_real_neg] THEN
  MATCH_ACCEPT_TAC candle_real_abs_interval_upper);;

(* -------------------------------------------------------------------------- *)
(* cval implementation.                                                       *)
(* -------------------------------------------------------------------------- *)

let candle_cv_q_zero_def = new_definition
 `candle_cv_q_zero = candle_cv_q candle_q_zero`;;

let candle_cv_q_half_def = new_definition
 `candle_cv_q_half = candle_cv_q candle_q_half`;;

let candle_cv_q_two_def = new_definition
 `candle_cv_q_two = candle_cv_q candle_q_two`;;

let candle_cv_q_zero_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_zero_def; candle_cv_q_def;
                    Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                    FST; SND]))
    candle_cv_q_zero_def;;

let candle_cv_q_half_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_half_def; candle_cv_q_def;
                    Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                    FST; SND]))
    candle_cv_q_half_def;;

let candle_cv_q_two_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_two_def; candle_cv_q_def;
                    Candle_cv_linear_combination_core.candle_cv_lc_z_def;
                    FST; SND]))
    candle_cv_q_two_def;;

let candle_cv_q_midpoint_def = new_definition
 `candle_cv_q_midpoint i =
    candle_cv_q_mul candle_cv_q_half
      (candle_cv_q_add (Cexp_fst i) (Cexp_snd i))`;;

let candle_cv_q_radius_def = new_definition
 `candle_cv_q_radius i =
    candle_cv_q_mul candle_cv_q_half
      (candle_cv_q_add (Cexp_snd i) (candle_cv_q_neg (Cexp_fst i)))`;;

let candle_cv_q_point_interval_def = new_definition
 `candle_cv_q_point_interval q = Cexp_pair q q`;;

let candle_cv_q_abs_upper_def = new_definition
 `candle_cv_q_abs_upper i =
    candle_cv_q_max (candle_cv_q_neg (Cexp_fst i)) (Cexp_snd i)`;;

let candle_cv_q_program_interval_def = new_definition
 `candle_cv_q_program_interval env program =
    candle_cv_q_interval_head
      (candle_cv_q_interval_run env program
        (candle_cv_q_interval_list []))`;;

let candle_cv_q_program_interval_compute =
  CONV_RULE
    (RAND_CONV (REWRITE_CONV[candle_cv_q_interval_list_def]))
    candle_cv_q_program_interval_def;;

let candle_cv_q_taylor_upper_def = new_definition
 `candle_cv_q_taylor_upper wx wy f df_x df_y ddf_xx ddf_xy ddf_yy =
    candle_cv_q_add (Cexp_snd f)
      (candle_cv_q_add
        (candle_cv_q_add
          (candle_cv_q_mul wx (candle_cv_q_abs_upper df_x))
          (candle_cv_q_mul wy (candle_cv_q_abs_upper df_y)))
        (candle_cv_q_mul candle_cv_q_half
          (candle_cv_q_add
            (candle_cv_q_mul wx
              (candle_cv_q_add
                (candle_cv_q_mul wx (candle_cv_q_abs_upper ddf_xx))
                (candle_cv_q_mul candle_cv_q_two
                  (candle_cv_q_mul wy
                    (candle_cv_q_abs_upper ddf_xy)))))
            (candle_cv_q_mul wy
              (candle_cv_q_mul wy
                (candle_cv_q_abs_upper ddf_yy))))))`;;

let candle_cv_q_center_environment_def = new_definition
 `candle_cv_q_center_environment ix iy =
    Cexp_pair
      (candle_cv_q_point_interval (candle_cv_q_midpoint ix))
      (Cexp_pair
        (candle_cv_q_point_interval (candle_cv_q_midpoint iy))
        (Cexp_num 0))`;;

let candle_cv_q_box_environment_def = new_definition
 `candle_cv_q_box_environment ix iy =
    Cexp_pair ix (Cexp_pair iy (Cexp_num 0))`;;

let candle_cv_q_whole_box_upper_def = new_definition
 `candle_cv_q_whole_box_upper pf pfx pfy pfxx pfxy pfyy ix iy =
    candle_cv_q_taylor_upper
      (candle_cv_q_radius ix) (candle_cv_q_radius iy)
      (candle_cv_q_program_interval
        (candle_cv_q_center_environment ix iy) pf)
      (candle_cv_q_program_interval
        (candle_cv_q_center_environment ix iy) pfx)
      (candle_cv_q_program_interval
        (candle_cv_q_center_environment ix iy) pfy)
      (candle_cv_q_program_interval
        (candle_cv_q_box_environment ix iy) pfxx)
      (candle_cv_q_program_interval
        (candle_cv_q_box_environment ix iy) pfxy)
      (candle_cv_q_program_interval
        (candle_cv_q_box_environment ix iy) pfyy)`;;

let candle_cv_q_whole_box_finish_def = new_definition
 `candle_cv_q_whole_box_finish valid_x valid_y upper =
    Cexp_pair
      (Cexp_if valid_x
        (Cexp_if valid_y
          (Cexp_if (candle_cv_q_le candle_cv_q_zero upper)
            (Cexp_num 0) (Cexp_num 1))
          (Cexp_num 0))
        (Cexp_num 0))
      upper`;;

let candle_cv_q_whole_box_check_def = new_definition
 `candle_cv_q_whole_box_check pf pfx pfy pfxx pfxy pfyy ix iy =
    candle_cv_q_whole_box_finish
      (candle_cv_q_le (Cexp_fst ix) (Cexp_snd ix))
      (candle_cv_q_le (Cexp_fst iy) (Cexp_snd iy))
      (candle_cv_q_whole_box_upper pf pfx pfy pfxx pfxy pfyy ix iy)`;;

let candle_cv_q_whole_box_compute_eqs =
  candle_cv_q_interval_program_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_zero_compute;
    candle_cv_q_half_compute;
    candle_cv_q_two_compute;
    candle_cv_q_midpoint_def;
    candle_cv_q_radius_def;
    candle_cv_q_point_interval_def;
    candle_cv_q_abs_upper_def;
    candle_cv_q_program_interval_compute;
    candle_cv_q_taylor_upper_def;
    candle_cv_q_center_environment_def;
    candle_cv_q_box_environment_def;
    candle_cv_q_whole_box_upper_def;
    candle_cv_q_whole_box_finish_def;
    candle_cv_q_whole_box_check_def];;

(* -------------------------------------------------------------------------- *)
(* Representation theorems.  These ensure the one cval computation denotes   *)
(* the ordinary exact-rational algorithm above.                               *)
(* -------------------------------------------------------------------------- *)

let candle_cv_q_midpoint_correct = prove
 (`!i. candle_cv_q_midpoint (candle_cv_q_interval i) =
       candle_cv_q (candle_q_midpoint i)`,
  REWRITE_TAC[candle_cv_q_midpoint_def; candle_q_midpoint_def;
              candle_cv_q_half_def; candle_cv_q_interval_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_q_add_correct; candle_cv_q_mul_correct]);;

let candle_cv_q_radius_correct = prove
 (`!i. candle_cv_q_radius (candle_cv_q_interval i) =
       candle_cv_q (candle_q_radius i)`,
  REWRITE_TAC[candle_cv_q_radius_def; candle_q_radius_def;
              candle_cv_q_half_def; candle_cv_q_interval_def;
              cexp_fst_def; cexp_snd_def; candle_cv_q_neg_correct;
              candle_cv_q_add_correct; candle_cv_q_mul_correct]);;

let candle_cv_q_point_interval_correct = prove
 (`!q. candle_cv_q_point_interval (candle_cv_q q) =
       candle_cv_q_interval (candle_q_point_interval q)`,
  REWRITE_TAC[candle_cv_q_point_interval_def;
              candle_q_point_interval_def;
              candle_cv_q_interval_def; FST; SND]);;

let candle_cv_q_interval_snd_correct = prove
 (`!i. Cexp_snd (candle_cv_q_interval i) = candle_cv_q (SND i)`,
  REWRITE_TAC[candle_cv_q_interval_def; cexp_snd_def]);;

let candle_cv_q_abs_upper_correct = prove
 (`!i. candle_cv_q_abs_upper (candle_cv_q_interval i) =
       candle_cv_q (candle_q_abs_upper i)`,
  REWRITE_TAC[candle_cv_q_abs_upper_def; candle_q_abs_upper_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_neg_correct; candle_cv_q_max_correct]);;

let candle_cv_q_program_interval_correct = prove
 (`!env program.
     candle_cv_q_program_interval
       (candle_cv_q_interval_list env)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_interval (candle_q_program_interval env program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_program_interval_def;
              candle_q_program_interval_def;
              candle_cv_q_interval_run_correct;
              candle_cv_q_interval_head_correct]);;

let candle_cv_q_taylor_upper_correct = prove
 (`!wx wy f df_x df_y ddf_xx ddf_xy ddf_yy.
     candle_cv_q_taylor_upper
       (candle_cv_q wx) (candle_cv_q wy)
       (candle_cv_q_interval f)
       (candle_cv_q_interval df_x) (candle_cv_q_interval df_y)
       (candle_cv_q_interval ddf_xx) (candle_cv_q_interval ddf_xy)
       (candle_cv_q_interval ddf_yy) =
     candle_cv_q
       (candle_q_taylor_upper wx wy f df_x df_y ddf_xx ddf_xy ddf_yy)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_taylor_upper_def; candle_q_taylor_upper_def;
              candle_cv_q_interval_snd_correct;
              candle_cv_q_half_def; candle_cv_q_two_def;
              candle_cv_q_abs_upper_correct;
              candle_cv_q_add_correct; candle_cv_q_mul_correct]);;

let candle_cv_q_center_environment_correct = prove
 (`!ix iy.
     candle_cv_q_center_environment
       (candle_cv_q_interval ix) (candle_cv_q_interval iy) =
     candle_cv_q_interval_list
       [candle_q_point_interval (candle_q_midpoint ix);
        candle_q_point_interval (candle_q_midpoint iy)]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_center_environment_def;
              candle_cv_q_interval_list_def;
              candle_cv_q_midpoint_correct;
              candle_cv_q_point_interval_correct]);;

let candle_cv_q_box_environment_correct = prove
 (`!ix iy.
     candle_cv_q_box_environment
       (candle_cv_q_interval ix) (candle_cv_q_interval iy) =
     candle_cv_q_interval_list [ix;iy]`,
  REWRITE_TAC[candle_cv_q_box_environment_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_whole_box_upper_correct = prove
 (`!pf pfx pfy pfxx pfxy pfyy ix iy.
     candle_cv_q_whole_box_upper
       (candle_cv_q_instruction_list pf)
       (candle_cv_q_instruction_list pfx)
       (candle_cv_q_instruction_list pfy)
       (candle_cv_q_instruction_list pfxx)
       (candle_cv_q_instruction_list pfxy)
       (candle_cv_q_instruction_list pfyy)
       (candle_cv_q_interval ix) (candle_cv_q_interval iy) =
     candle_cv_q
       (candle_q_whole_box_upper pf pfx pfy pfxx pfxy pfyy ix iy)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_whole_box_upper_def;
              candle_q_whole_box_upper_def;
              candle_cv_q_radius_correct;
              candle_cv_q_center_environment_correct;
              candle_cv_q_box_environment_correct;
              candle_cv_q_program_interval_correct;
              candle_cv_q_taylor_upper_correct]);;

let candle_cv_q_whole_box_finish_correct = prove
 (`!valid_x valid_y upper.
     candle_cv_q_whole_box_finish
       (Cexp_num (if valid_x then SUC 0 else 0))
       (Cexp_num (if valid_y then SUC 0 else 0))
       (candle_cv_q upper) =
     Cexp_pair
       (Cexp_num
         (if valid_x /\ valid_y /\
             ~(candle_q_le candle_q_zero upper)
          then SUC 0 else 0))
       (candle_cv_q upper)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_whole_box_finish_def;
              candle_cv_q_zero_def; candle_cv_q_le_correct] THEN
  BOOL_CASES_TAC `valid_x:bool` THEN
  BOOL_CASES_TAC `valid_y:bool` THEN
  BOOL_CASES_TAC `candle_q_le candle_q_zero upper` THEN
  ASM_REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_whole_box_check_correct = prove
 (`!pf pfx pfy pfxx pfxy pfyy ix iy.
     candle_cv_q_whole_box_check
       (candle_cv_q_instruction_list pf)
       (candle_cv_q_instruction_list pfx)
       (candle_cv_q_instruction_list pfy)
       (candle_cv_q_instruction_list pfxx)
       (candle_cv_q_instruction_list pfxy)
       (candle_cv_q_instruction_list pfyy)
       (candle_cv_q_interval ix) (candle_cv_q_interval iy) =
     Cexp_pair
       (Cexp_num
         (if candle_q_whole_box_accept
               pf pfx pfy pfxx pfxy pfyy ix iy
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_whole_box_upper pf pfx pfy pfxx pfxy pfyy ix iy))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_whole_box_check_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct;
              candle_cv_q_whole_box_upper_correct;
              candle_cv_q_whole_box_finish_correct;
              candle_q_whole_box_accept_def; candle_q_box_valid_def;
              CONJ_ASSOC]);;

end;;
