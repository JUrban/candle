(* ========================================================================== *)
(* Generated genuine case-16594 cell-0 packed-entry fixture.                 *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Generated data are untrusted: the executable *)
(* source entry checks every value before any mathematical theorem follows.  *)
(* Program log SHA-256: 225450e4f0cef50ef1d3ab6ab18c61c6e5e5af940ea0e1801b632f367942a322 *)
(* State trace SHA-256: 6bc10f82c63fe2805e80142f6191b46cef1a3044af37e3f93e362a67c6168a74 *)
(* Fast certificate TSV SHA-256: 4f4d5cb0b550a413c8124eb4630bfdc8e9c62a1a061931be1b271e35dbb375e5 *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_dispatch_entry_sound.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_cell0_entry_fixture = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_interval_program;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_entry_sound;;

print_endline "CANDLE_CV_CASE16594_CELL0_FIXTURE_STAGE opens";;

let candle_case16594_cell0_entry_interval
    lower_positive lower_negative lower_denominator
    upper_positive upper_negative upper_denominator =
  let q positive negative denominator =
    let denominator_number = candle_case16594_cell0_num denominator in
    mk_pair
      (mk_pair
        (mk_numeral (candle_case16594_cell0_num positive),
         mk_numeral (candle_case16594_cell0_num negative)),
       mk_numeral
         (Num.sub_num denominator_number (candle_case16594_cell0_num "1"))) in
  mk_pair
    (q lower_positive lower_negative lower_denominator,
     q upper_positive upper_negative upper_denominator);;

print_endline "CANDLE_CV_CASE16594_CELL0_FIXTURE_STAGE interval-helper";;

let candle_case16594_cell0_sources =
  `[Candle_analytic_push_poly
 [Candle_q_push 1 0 0; Candle_q_push 13 0 499; Candle_q_neg;
  Candle_q_mul];
 Candle_analytic_push_poly [Candle_q_push 1 0 0];
 Candle_analytic_push_poly [Candle_q_push 3 0 0];
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly [Candle_q_push 1 0 2];
 Candle_analytic_push_poly
 [Candle_q_push 1 0 0; Candle_q_push 1 0 2; Candle_q_square;
  Candle_q_neg; Candle_q_add];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_neg;
 Candle_analytic_program_add; Candle_analytic_program_mul;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_neg;
 Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_inv;
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_load 0];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_push_poly [Candle_q_push 2 0 0];
 Candle_analytic_program_neg; Candle_analytic_program_add;
 Candle_analytic_push_poly [Candle_q_push 13 0 24];
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_mul; Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly
 [Candle_q_load 1; Candle_q_neg; Candle_q_load 2;
  Candle_q_mul; Candle_q_load 0; Candle_q_load 3;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 1;
  Candle_q_load 4; Candle_q_mul; Candle_q_load 2;
  Candle_q_load 5; Candle_q_mul; Candle_q_load 4;
  Candle_q_load 5; Candle_q_mul; Candle_q_neg; Candle_q_add;
  Candle_q_load 0; Candle_q_load 0; Candle_q_neg;
  Candle_q_load 1; Candle_q_load 2; Candle_q_load 3;
  Candle_q_neg; Candle_q_add; Candle_q_load 4;
  Candle_q_load 5; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_neg];
 Candle_analytic_push_poly
 [Candle_q_push 4 0 0; Candle_q_load 0; Candle_q_load 0;
  Candle_q_load 3; Candle_q_load 0; Candle_q_neg;
  Candle_q_load 1; Candle_q_load 2; Candle_q_load 3;
  Candle_q_neg; Candle_q_add; Candle_q_load 4;
  Candle_q_load 5; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 4; Candle_q_load 0; Candle_q_load 1;
  Candle_q_neg; Candle_q_add; Candle_q_load 2;
  Candle_q_load 3; Candle_q_load 4; Candle_q_neg;
  Candle_q_add; Candle_q_load 5; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 2;
  Candle_q_load 5; Candle_q_load 0; Candle_q_load 1;
  Candle_q_load 2; Candle_q_neg; Candle_q_add;
  Candle_q_load 3; Candle_q_load 4; Candle_q_load 5;
  Candle_q_neg; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 2; Candle_q_load 3; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 2; Candle_q_load 4; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 1; Candle_q_load 5; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 3;
  Candle_q_load 4; Candle_q_load 5; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_add;
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 0 1 0];
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 1 0 0];
 Candle_analytic_push_poly [Candle_q_push 3 0 0];
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly [Candle_q_push 1 0 2];
 Candle_analytic_push_poly
 [Candle_q_push 1 0 0; Candle_q_push 1 0 2; Candle_q_square;
  Candle_q_neg; Candle_q_add];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_neg;
 Candle_analytic_program_add; Candle_analytic_program_mul;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_neg;
 Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_inv;
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_load 1];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_push_poly [Candle_q_push 2 0 0];
 Candle_analytic_program_neg; Candle_analytic_program_add;
 Candle_analytic_push_poly [Candle_q_push 13 0 24];
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_mul; Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly
 [Candle_q_load 2; Candle_q_neg; Candle_q_load 0;
  Candle_q_mul; Candle_q_load 1; Candle_q_load 4;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 2;
  Candle_q_load 5; Candle_q_mul; Candle_q_load 0;
  Candle_q_load 3; Candle_q_mul; Candle_q_load 5;
  Candle_q_load 3; Candle_q_mul; Candle_q_neg; Candle_q_add;
  Candle_q_load 1; Candle_q_load 1; Candle_q_neg;
  Candle_q_load 2; Candle_q_load 0; Candle_q_load 4;
  Candle_q_neg; Candle_q_add; Candle_q_load 5;
  Candle_q_load 3; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_neg];
 Candle_analytic_push_poly
 [Candle_q_push 4 0 0; Candle_q_load 1; Candle_q_load 0;
  Candle_q_load 3; Candle_q_load 0; Candle_q_neg;
  Candle_q_load 1; Candle_q_load 2; Candle_q_load 3;
  Candle_q_neg; Candle_q_add; Candle_q_load 4;
  Candle_q_load 5; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 4; Candle_q_load 0; Candle_q_load 1;
  Candle_q_neg; Candle_q_add; Candle_q_load 2;
  Candle_q_load 3; Candle_q_load 4; Candle_q_neg;
  Candle_q_add; Candle_q_load 5; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 2;
  Candle_q_load 5; Candle_q_load 0; Candle_q_load 1;
  Candle_q_load 2; Candle_q_neg; Candle_q_add;
  Candle_q_load 3; Candle_q_load 4; Candle_q_load 5;
  Candle_q_neg; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 2; Candle_q_load 3; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 2; Candle_q_load 4; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 1; Candle_q_load 5; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 3;
  Candle_q_load 4; Candle_q_load 5; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_add;
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 0 1 0];
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 1 0 0];
 Candle_analytic_push_poly [Candle_q_push 3 0 0];
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly [Candle_q_push 1 0 2];
 Candle_analytic_push_poly
 [Candle_q_push 1 0 0; Candle_q_push 1 0 2; Candle_q_square;
  Candle_q_neg; Candle_q_add];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_neg;
 Candle_analytic_program_add; Candle_analytic_program_mul;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_neg;
 Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_inv;
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_load 2];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_push_poly [Candle_q_push 2 0 0];
 Candle_analytic_program_neg; Candle_analytic_program_add;
 Candle_analytic_push_poly [Candle_q_push 13 0 24];
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_mul; Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly
 [Candle_q_load 0; Candle_q_neg; Candle_q_load 1;
  Candle_q_mul; Candle_q_load 2; Candle_q_load 5;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 3; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 4; Candle_q_mul; Candle_q_load 3;
  Candle_q_load 4; Candle_q_mul; Candle_q_neg; Candle_q_add;
  Candle_q_load 2; Candle_q_load 2; Candle_q_neg;
  Candle_q_load 0; Candle_q_load 1; Candle_q_load 5;
  Candle_q_neg; Candle_q_add; Candle_q_load 3;
  Candle_q_load 4; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_neg];
 Candle_analytic_push_poly
 [Candle_q_push 4 0 0; Candle_q_load 2; Candle_q_load 0;
  Candle_q_load 3; Candle_q_load 0; Candle_q_neg;
  Candle_q_load 1; Candle_q_load 2; Candle_q_load 3;
  Candle_q_neg; Candle_q_add; Candle_q_load 4;
  Candle_q_load 5; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 4; Candle_q_load 0; Candle_q_load 1;
  Candle_q_neg; Candle_q_add; Candle_q_load 2;
  Candle_q_load 3; Candle_q_load 4; Candle_q_neg;
  Candle_q_add; Candle_q_load 5; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 2;
  Candle_q_load 5; Candle_q_load 0; Candle_q_load 1;
  Candle_q_load 2; Candle_q_neg; Candle_q_add;
  Candle_q_load 3; Candle_q_load 4; Candle_q_load 5;
  Candle_q_neg; Candle_q_add; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul; Candle_q_load 1;
  Candle_q_load 2; Candle_q_load 3; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 2; Candle_q_load 4; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 0;
  Candle_q_load 1; Candle_q_load 5; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_load 3;
  Candle_q_load 4; Candle_q_load 5; Candle_q_mul;
  Candle_q_mul; Candle_q_neg; Candle_q_add; Candle_q_add;
  Candle_q_add; Candle_q_mul; Candle_q_mul];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_add;
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 0 1 0];
 Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 1 0 0];
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_mul;
 Candle_analytic_push_poly [Candle_q_push 1 0 0];
 Candle_analytic_push_poly [Candle_q_push 3 0 0];
 Candle_analytic_program_pi_half;
 Candle_analytic_push_poly [Candle_q_push 1 0 2];
 Candle_analytic_push_poly
 [Candle_q_push 1 0 0; Candle_q_push 1 0 2; Candle_q_square;
  Candle_q_neg; Candle_q_add];
 Candle_analytic_program_sqrt
 (candle_analytic_sqrt_interval 0 0 0 100 0 0);
 Candle_analytic_program_inv; Candle_analytic_program_mul;
 Candle_analytic_program_atn; Candle_analytic_program_neg;
 Candle_analytic_program_add; Candle_analytic_program_mul;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_neg;
 Candle_analytic_program_add;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_inv;
 Candle_analytic_program_mul;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_pi_half;
 Candle_analytic_program_add; Candle_analytic_program_mul;
 Candle_analytic_program_mul; Candle_analytic_program_add;
 Candle_analytic_program_add; Candle_analytic_program_add;
 Candle_analytic_program_add; Candle_analytic_program_add]`;;

print_endline "CANDLE_CV_CASE16594_CELL0_FIXTURE_STAGE sources";;

let candle_case16594_cell0_plan_codes =
  mk_list
    (map (mk_numeral o Num.num_of_int)
      [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 4; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 5; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0],
     `:num`);;

print_endline "CANDLE_CV_CASE16594_CELL0_FIXTURE_STAGE codes";;

let candle_case16594_cell0_certificates =
  mk_list
    ([candle_case16594_cell0_entry_interval "1036597572434" "0" "1099511627776" "1036652548017" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "829278057947" "0" "1099511627776" "1295815685021" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "583091134019" "0" "1099511627776" "583122058050" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "466472907215" "0" "1099511627776" "728902572563" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "262391010308" "0" "1099511627776" "410007697068" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "373646849391" "0" "1099511627776" "373665288775" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "868738034212" "0" "1099511627776" "868758511058" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2536507354581" "0" "1099511627776" "2536562330163" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2029205883665" "0" "1099511627776" "3170702912704" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "238300041997" "0" "1099511627776" "238305206849" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "190640033598" "0" "1099511627776" "297881508562" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "17429149167" "0" "1099511627776" "28779709824" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2114445438028" "0" "1099511627776" "2114445438033" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2114445438028" "0" "1099511627776" "2114445438033" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "78435157303214" "0" "1099511627776" "78435212278797" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "62748125842571" "0" "1099511627776" "98044015348496" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "7706524815" "0" "1099511627776" "7706530217" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "6165219852" "0" "1099511627776" "9633162771" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "483787" "0" "1099511627776" "1265544" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "15413049630" "0" "1099511627776" "15413060434" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "13559178827" "0" "1099511627776" "17854162015" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "0" "858015810201" "1099511627776" "0" "858015208760" "1099511627776";
      candle_case16594_cell0_entry_interval "0" "1102675569478" "1099511627776" "0" "613355449483" "1099511627776";
      candle_case16594_cell0_entry_interval "0" "729749669492" "1099511627776" "0" "726383443455" "1099511627776";
      candle_case16594_cell0_entry_interval "669560994050" "0" "1099511627776" "669561932732" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "683366620021" "0" "1099511627776" "683366982621" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "342156370070" "0" "1099511627776" "1105848615702" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "548176119157" "0" "1099511627776" "838560487867" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "273300481798" "0" "1099511627776" "639541842076" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1036597572434" "0" "1099511627776" "1036652548017" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "829278057947" "0" "1099511627776" "1295815685021" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "583091134019" "0" "1099511627776" "583122058050" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "466472907215" "0" "1099511627776" "728902572563" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "262391010308" "0" "1099511627776" "410007697068" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "373646849391" "0" "1099511627776" "373665288775" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "868738034212" "0" "1099511627776" "868758511058" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2239012493454" "0" "1099511627776" "2239067469036" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1791209994763" "0" "1099511627776" "2798834336295" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "269961900731" "0" "1099511627776" "269968529240" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "215969520585" "0" "1099511627776" "337460661550" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "25148996295" "0" "1099511627776" "42182582694" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2114445438028" "0" "1099511627776" "2114445438033" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2114445438028" "0" "1099511627776" "2114445438033" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "69235851376868" "0" "1099511627776" "69235906352451" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "55388681101494" "0" "1099511627776" "86544882940563" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "8730483092" "0" "1099511627776" "8730490025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "6984386474" "0" "1099511627776" "10913112532" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "697276" "0" "1099511627776" "1867390" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "17460966185" "0" "1099511627776" "17460980050" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "15275097340" "0" "1099511627776" "20376923313" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "382535551631" "0" "1099511627776" "382535855389" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "168776559799" "0" "1099511627776" "596294847221" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "368133244240" "0" "1099511627776" "368133607755" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "133089495886" "0" "1099511627776" "133089707250" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "980792236111" "0" "1099511627776" "980792404297" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "25907436008" "0" "1099511627776" "323386798139" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "849622009271" "0" "1099511627776" "1074200587602" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "656525625015" "0" "1099511627776" "1049472214077" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1036597572434" "0" "1099511627776" "1036652548017" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "829278057947" "0" "1099511627776" "1295815685021" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "583091134019" "0" "1099511627776" "583122058050" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "466472907215" "0" "1099511627776" "728902572563" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "262391010308" "0" "1099511627776" "410007697068" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "373646849391" "0" "1099511627776" "373665288775" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "868738034212" "0" "1099511627776" "868758511058" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2536507354581" "0" "1099511627776" "2536562330163" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2029205883665" "0" "1099511627776" "3170702912704" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "238300041997" "0" "1099511627776" "238305206849" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "190640033598" "0" "1099511627776" "297881508562" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "17429149167" "0" "1099511627776" "28779709824" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2114445438028" "0" "1099511627776" "2114445438033" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "2114445438028" "0" "1099511627776" "2114445438033" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "78435157303214" "0" "1099511627776" "78435212278797" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "62748125842571" "0" "1099511627776" "98044015348496" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "7706524815" "0" "1099511627776" "7706530217" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "6165219852" "0" "1099511627776" "9633162771" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "483959" "0" "1099511627776" "1264793" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "15413049630" "0" "1099511627776" "15413060434" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "13563724036" "0" "1099511627776" "17846287408" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "0" "667849432612" "1099511627776" "0" "667848964471" "1099511627776";
      candle_case16594_cell0_entry_interval "0" "892086397741" "1099511627776" "0" "443611999342" "1099511627776";
      candle_case16594_cell0_entry_interval "0" "600196349886" "1099511627776" "0" "600066446062" "1099511627776";
      candle_case16594_cell0_entry_interval "405654863557" "0" "1099511627776" "405655432260" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "803183813752" "0" "1099511627776" "803184117223" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "178980922974" "0" "1099511627776" "723792382846" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "663041277028" "0" "1099511627776" "945586909291" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "399835457795" "0" "1099511627776" "813210684121" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1036597572434" "0" "1099511627776" "1036652548017" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "829278057947" "0" "1099511627776" "1295815685021" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "583091134019" "0" "1099511627776" "583122058050" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "466472907215" "0" "1099511627776" "728902572563" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "262391010308" "0" "1099511627776" "410007697068" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "1166182268038" "0" "1099511627776" "1166244116100" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "388727422678" "0" "1099511627776" "388748038701" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "373646849391" "0" "1099511627776" "373665288775" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "137432843204" "0" "1099511627776" "137447420997" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "977336978789" "0" "1099511627776" "977348497025" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "868738034212" "0" "1099511627776" "868758511058" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776";
      candle_case16594_cell0_entry_interval "349985421056" "0" "1099511627776" "349985421109" "0" "1099511627776"],
     candle_q_interval_type);;

print_endline "CANDLE_CV_CASE16594_CELL0_FIXTURE_STAGE certificates";;

let candle_case16594_cell0_packed_hessian =
  mk_list
    ([candle_case16594_cell0_entry_interval "0" "340167326561" "1000000000000" "402980253372" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "396018359135" "1000000000000" "323470285811" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "255903112051" "1000000000000" "355730967471" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "360044130376" "1000000000000" "417582188774" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "269234919217" "1000000000000" "205165705955" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "250421249594" "1000000000000" "343084068364" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "487651201511" "1000000000000" "385986375609" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "402406781360" "1000000000000" "323562241833" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "327205604265" "1000000000000" "420027970576" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "289681137531" "1000000000000" "273710959768" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "302442752292" "1000000000000" "372444240028" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "317130249734" "1000000000000" "384173654389" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "280241619424" "1000000000000" "382413793193" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "270777253736" "1000000000000" "202814185715" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "298378781701" "1000000000000" "355261468456" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "396864760997" "1000000000000" "376636657600" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "267483546693" "1000000000000" "247514732069" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "320424665311" "1000000000000" "323150118612" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "172502514236" "1000000000000" "197692527330" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "242184957480" "1000000000000" "217987523861" "0" "1000000000000";
      candle_case16594_cell0_entry_interval "0" "303107947971" "1000000000000" "308832555954" "0" "1000000000000"],
     candle_q_interval_type);;

print_endline "CANDLE_CV_CASE16594_CELL0_FIXTURE_STAGE packed-hessian";;

let _ =
  if length (dest_list candle_case16594_cell0_sources) <> 167 ||
     length (dest_list candle_case16594_cell0_plan_codes) <> 167 ||
     length (dest_list candle_case16594_cell0_certificates) <> 134 ||
     length (dest_list candle_case16594_cell0_packed_hessian) <> 21 then
    failwith "case16594 cell0 entry fixture: shape drift";;

print_endline
  "CANDLE_CV_CASE16594_CELL0_ENTRY_FIXTURE_OK DEVELOPMENT_NON_RELEASE";;

end;;
