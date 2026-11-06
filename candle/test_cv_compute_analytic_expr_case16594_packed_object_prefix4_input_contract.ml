(* ========================================================================== *)
(* Genuine case-16594 four-cell input contract from the sealed plan capture. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the bounded scale-up probe for the    *)
(* generic whole-call bridge.  Exact source boxes come from the preserved     *)
(* Flyspeck plan capture.  Packed centers, upward radii, and outer boxes are  *)
(* derived here by the same 2^40 rounding specification used by the genuine *)
(* actual-data projection, but the HOL kernel independently proves their     *)
(* geometric contract.                                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_whole_input_data_sound.ml";;
needs "candle/test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_prefix4_input_contract = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_packed_geometry_sound;;
open Candle_cv_analytic_expr_packed_source_object_whole_success_sound;;
open Candle_cv_analytic_expr_packed_source_object_whole_input_data_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_correspondence;;

let candle_case16594_prefix4_scale =
  Num.num_of_string "1099511627776";;

let candle_case16594_prefix4_two = Num.num_of_int 2;;

let candle_case16594_prefix4_fixture_path =
  "/project/flyspeck-candle-runs/cv-case16594-native-inputs-full-v4-dev-001/case16594-native-jobs-full.tsv";;

let candle_case16594_prefix4_scaled_q integer =
  candle_q_term
    (Num.div_num integer candle_case16594_prefix4_scale);;

let candle_case16594_prefix4_split delimiter text =
  let limit = String.length text in
  let rec fields first position result =
    if position = limit then
      rev (String.sub text first (position - first) :: result)
    else if String.get text position = delimiter then
      fields (position + 1) (position + 1)
        (String.sub text first (position - first) :: result)
    else fields first (position + 1) result in
  fields 0 0 [];;

let candle_case16594_prefix4_nth index items =
  let rec nth remaining = function
    | [] -> failwith "case16594 prefix4 input contract: field index"
    | head :: tail -> if remaining = 0 then head else nth (remaining - 1) tail in
  nth index items;;

let rec candle_case16594_prefix4_strip_line_end text =
  let size = String.length text in
  if size = 0 then text else
  let final = String.get text (size - 1) in
  if final = '\n' || final = '\r' then
    candle_case16594_prefix4_strip_line_end (String.sub text 0 (size - 1))
  else text;;

let candle_case16594_prefix4_rational raw_text =
  let text = candle_case16594_prefix4_strip_line_end raw_text in
  match candle_case16594_prefix4_split '/' text with
  | [numerator] -> Num.num_of_string numerator
  | [numerator;denominator] ->
      Num.div_num
        (Num.num_of_string numerator) (Num.num_of_string denominator)
  | _ -> failwith "case16594 prefix4 input contract: rational syntax";;

let candle_case16594_prefix4_vector field =
  map candle_case16594_prefix4_rational
    (candle_case16594_prefix4_split ',' field);;

let candle_case16594_prefix4_read_cells () =
  let channel = Stdlib.open_in candle_case16594_prefix4_fixture_path in
  let rec read index result =
    if index = 4 then (Stdlib.close_in channel; rev result) else
    let line = Stdlib.input_line channel in
    let fields = candle_case16594_prefix4_split '\t' line in
    if length fields <> 5 ||
       int_of_string (candle_case16594_prefix4_nth 0 fields) <> index then
      failwith "case16594 prefix4 input contract: fixture row drift";
    let lower = candle_case16594_prefix4_vector
      (candle_case16594_prefix4_nth 3 fields)
    and upper = candle_case16594_prefix4_vector
      (candle_case16594_prefix4_nth 4 fields) in
    if length lower <> 6 || length upper <> 6 then
      failwith "case16594 prefix4 input contract: fixture box width drift";
    read (index + 1) ((lower,upper) :: result) in
  read 0 [];;

let candle_case16594_prefix4_pack_coordinate lower upper =
  let midpoint =
    Num.div_num (Num.add_num lower upper) candle_case16594_prefix4_two
  and radius =
    Num.div_num (Num.sub_num upper lower) candle_case16594_prefix4_two in
  let center_lower =
    Num.floor_num
      (Num.mul_num midpoint candle_case16594_prefix4_scale)
  and center_upper =
    Num.ceiling_num
      (Num.mul_num midpoint candle_case16594_prefix4_scale)
  and radius_upper =
    Num.ceiling_num
      (Num.mul_num radius candle_case16594_prefix4_scale) in
  let outer_lower =
    Num.floor_num
      (Num.mul_num lower candle_case16594_prefix4_scale)
  and outer_upper =
    Num.ceiling_num
      (Num.mul_num upper candle_case16594_prefix4_scale) in
  (mk_pair (candle_q_term lower,candle_q_term upper),
   mk_pair
     (candle_case16594_prefix4_scaled_q center_lower,
      candle_case16594_prefix4_scaled_q center_upper),
   mk_pair
     (candle_case16594_prefix4_scaled_q outer_lower,
      candle_case16594_prefix4_scaled_q outer_upper),
   candle_case16594_prefix4_scaled_q radius_upper);;

let candle_case16594_prefix4_pack_cell (lower,upper) =
  if length lower <> 6 || length upper <> 6 then
    failwith "case16594 prefix4 input contract: cell shape drift";
  let coordinates =
    List.map2 candle_case16594_prefix4_pack_coordinate
      lower upper in
  let source_boxes =
    mk_list (map (fun (source,_,_,_) -> source) coordinates,
      candle_q_interval_type)
  and center_boxes =
    mk_list (map (fun (_,center,_,_) -> center) coordinates,
      candle_q_interval_type)
  and outer_boxes =
    mk_list (map (fun (_,_,outer,_) -> outer) coordinates,
      candle_q_interval_type)
  and radii =
    mk_list (map (fun (_,_,_,radius) -> radius) coordinates,
      `:((num#num)#num)`) in
  radii,mk_pair (outer_boxes,mk_pair (center_boxes,source_boxes));;

let candle_case16594_prefix4_cells =
  candle_case16594_prefix4_read_cells ();;

let candle_case16594_prefix4_geometry =
  map candle_case16594_prefix4_pack_cell candle_case16594_prefix4_cells;;

let candle_case16594_prefix4_radii_batches =
  mk_list
    (map fst candle_case16594_prefix4_geometry,
     `:((num#num)#num)list`);;

let candle_case16594_prefix4_jobs =
  mk_list
    (map snd candle_case16594_prefix4_geometry,
     `:((((num#num)#num)#((num#num)#num))list #
       (((((num#num)#num)#((num#num)#num))list) #
        ((((num#num)#num)#((num#num)#num))list)))`);;

let _ =
  let first_radii,first_job = hd candle_case16594_prefix4_geometry in
  let first_outer,first_center_source = dest_pair first_job in
  let first_center,first_source = dest_pair first_center_source in
  if not (aconv first_radii candle_case16594_cell0_radii) ||
     not (aconv first_outer candle_case16594_cell0_outer_boxes) ||
     not (aconv first_center candle_case16594_cell0_center_boxes) ||
     not (aconv first_source candle_case16594_cell0_source_boxes) then
    failwith "case16594 prefix4 input contract: cell0 packer seam drift";;

let candle_case16594_prefix4_forall_lt_six = prove
 (`(!k. k < 6 ==> P k) <=>
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5`,
  EQ_TAC THENL
   [DISCH_THEN (LABEL_TAC "bounded") THEN
    REPEAT CONJ_TAC THEN
    USE_THEN "bounded" MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 2` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 4` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 5` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let candle_case16594_prefix4_forall_lt_length_six = prove
 (`(!k. k < SUC (SUC (SUC (SUC (SUC (SUC 0))))) ==> P k) <=>
    P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5`,
  REWRITE_TAC[ARITH_RULE
    `SUC (SUC (SUC (SUC (SUC (SUC 0))))) = 6`;
    candle_case16594_prefix4_forall_lt_six]);;

let candle_case16594_prefix4_job_geometry_goal =
  let builder =
    `\radii_batches jobs.
       ALL2
         (\radii job.
            LENGTH (SND (SND job)) = 6 /\
            LENGTH (FST (SND job)) = 6 /\
            LENGTH (FST job) = 6 /\
            LENGTH radii = 6 /\
            candle_q_packed_source_correspondence
              (SND (SND job)) (FST (SND job)) (FST job) radii /\
            candle_q_packed_source_correspondence
              (FST job) (FST (SND job)) (FST job) radii)
         radii_batches jobs` in
  list_mk_comb
    (builder,
     [candle_case16594_prefix4_radii_batches;
      candle_case16594_prefix4_jobs]);;

let candle_case16594_prefix4_job_geometry_tactic =
  REWRITE_TAC
    [ALL2;
     candle_q_packed_source_correspondence_def;
     candle_q_packed_center_contains_source_midpoint_def;
     candle_q_packed_radii_cover_source_def;
     candle_q_packed_outer_covers_source_def;
     candle_case16594_prefix4_forall_lt_six;
     candle_case16594_prefix4_forall_lt_length_six;
     candle_q_box_valid_list_def; candle_q_radius_list_def;
     candle_q_interval_contains_def; candle_q_le_real;
     LENGTH; ALL; FST; SND] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC
    [candle_q_midpoint_real; candle_q_radius_real;
     candle_q_real_def; candle_q_den_def; candle_lc_zreal_def;
     FST; SND] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  TRY (REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  TRY ARITH_TAC;;

let candle_case16594_prefix4_job_geometry = prove
 (candle_case16594_prefix4_job_geometry_goal,
  candle_case16594_prefix4_job_geometry_tactic);;

let candle_case16594_prefix4_input_contract_goal =
  let certificate_batches =
    mk_var ("certificate_batches",`:A list`) in
  let builder =
    `\radii_batches jobs (certificate_batches:A list).
       LENGTH certificate_batches = 4
       ==>
       candle_q_packed_object_whole_input_contract
         (MAP2
           (\radii certificates. (radii,certificates))
           radii_batches certificate_batches)
         jobs` in
  mk_forall
    (certificate_batches,
     list_mk_comb
       (builder,
        [candle_case16594_prefix4_radii_batches;
         candle_case16594_prefix4_jobs;
         certificate_batches]));;

let candle_case16594_prefix4_input_contract_tactic =
  BETA_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_attach_certificates_input_contract THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    MATCH_ACCEPT_TAC (BETA_RULE candle_case16594_prefix4_job_geometry)];;

let candle_case16594_prefix4_input_contract = prove
 (candle_case16594_prefix4_input_contract_goal,
  candle_case16594_prefix4_input_contract_tactic);;

if hyp candle_case16594_prefix4_job_geometry <> [] ||
   hyp candle_case16594_prefix4_input_contract <> [] then
  failwith "case16594 prefix4 input contract: assumptions";;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_PREFIX4_INPUT_CONTRACT_OK cells=4 certificate_payload=parametric assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
