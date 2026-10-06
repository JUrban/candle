(* ========================================================================== *)
(* Logical meaning of the reflected tame-graph structural validators.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer proves that the cval validators,    *)
(* when run on the typed encodings, implement one ordinary HOL predicate.     *)
(* It deliberately does not yet claim canonical graph ordering, archive       *)
(* membership, or graph isomorphism.                                           *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_data.ml";;

module Candle_cv_tame_graph_data_sound = struct

open Candle_cv_flyspeck_lists_core;;
open Candle_cv_tame_graph_data;;

let candle_tame_cv_bool_def = new_definition
 `candle_tame_cv_bool value = Cexp_num (if value then 1 else 0)`;;

let candle_tame_cv_if_correct = prove
 (`!condition yes no.
     Cexp_if (candle_tame_cv_bool condition) yes no =
     if condition then yes else no`,
  GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN
  REWRITE_TAC[candle_tame_cv_bool_def; cexp_if_def;
              ARITH_RULE `1 = SUC 0`]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE cv-if";;

let candle_tame_cv_num_eq_correct = prove
 (`!left right.
     Cexp_eq (Cexp_num left) (Cexp_num right) =
     candle_tame_cv_bool (left = right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_eq_def; candle_tame_cv_bool_def;
              injectivity "cval"; ARITH_RULE `1 = SUC 0`]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE cv-eq";;

let candle_tame_cv_num_less_correct = prove
 (`!left right.
     Cexp_less (Cexp_num left) (Cexp_num right) =
     candle_tame_cv_bool (left < right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_less_def; candle_tame_cv_bool_def;
              ARITH_RULE `1 = SUC 0`]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE cv-less";;

let candle_tame_num_member_logical_def = define
 `(candle_tame_num_member_logical needle ([]:num list) = F) /\
  (candle_tame_num_member_logical needle (CONS head tail) =
     if needle = head then T
     else candle_tame_num_member_logical needle tail)`;;

let candle_tame_num_list_valid_aux_logical_def = define
 `(candle_tame_num_list_valid_aux_logical
     bound seen ([]:num list) = T) /\
  (candle_tame_num_list_valid_aux_logical
     bound seen (CONS head tail) =
     if head < bound then
       if candle_tame_num_member_logical head seen then F
       else candle_tame_num_list_valid_aux_logical
              bound (CONS head seen) tail
     else F)`;;

let candle_tame_num_list_valid_logical_def = new_definition
 `candle_tame_num_list_valid_logical bound values <=>
    candle_tame_num_list_valid_aux_logical bound [] values`;;

let candle_tame_fgraph_valid_logical_def = define
 `(candle_tame_fgraph_valid_logical bound ([]:(num list)list) = T) /\
  (candle_tame_fgraph_valid_logical bound (CONS face faces) =
     if face = [] then F
     else if candle_tame_num_list_valid_logical bound face then
       candle_tame_fgraph_valid_logical bound faces
     else F)`;;

let candle_tame_nonempty_fgraph_valid_logical_def = new_definition
 `candle_tame_nonempty_fgraph_valid_logical bound graph <=>
    ~(graph = []) /\ candle_tame_fgraph_valid_logical bound graph`;;

let candle_tame_vertex_map_valid_aux_logical_def = define
 `(candle_tame_vertex_map_valid_aux_logical
     source_bound target_bound seen_sources seen_targets
     ([]:(num#num)list) = T) /\
  (candle_tame_vertex_map_valid_aux_logical
     source_bound target_bound seen_sources seen_targets
     (CONS entry entries) =
     if FST entry < source_bound then
       if SND entry < target_bound then
         if candle_tame_num_member_logical (FST entry) seen_sources then F
         else if candle_tame_num_member_logical (SND entry) seen_targets then F
         else candle_tame_vertex_map_valid_aux_logical
                source_bound target_bound
                (CONS (FST entry) seen_sources)
                (CONS (SND entry) seen_targets) entries
       else F
     else F)`;;

let candle_tame_vertex_map_valid_logical_def = new_definition
 `candle_tame_vertex_map_valid_logical
    source_bound target_bound mapping <=>
    candle_tame_vertex_map_valid_aux_logical
      source_bound target_bound [] [] mapping`;;

let candle_cv_tame_num_member_correct = prove
 (`!needle values:num list.
     candle_cv_tame_num_member
       (Cexp_num needle) (candle_cv_num_list values) =
     candle_tame_cv_bool
       (candle_tame_num_member_logical needle values)`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[candle_cv_num_list_def;
                candle_cv_tame_num_member_def;
                candle_tame_num_member_logical_def;
                candle_tame_cv_bool_def];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[candle_cv_num_list_def;
                    candle_cv_tame_num_member_def;
                    candle_tame_num_member_logical_def;
                    candle_tame_cv_if_correct;
                    candle_tame_cv_num_eq_correct] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[candle_tame_cv_bool_def; cexp_if_def;
                    ARITH_RULE `1 = SUC 0`]]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE member";;

let candle_cv_tame_num_list_valid_aux_correct = prove
 (`!bound seen values:num list.
     candle_cv_tame_num_list_valid_aux
       (Cexp_num bound) (candle_cv_num_list seen)
       (candle_cv_num_list values) =
     candle_tame_cv_bool
       (candle_tame_num_list_valid_aux_logical bound seen values)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`seen:num list`,`seen:num list`) THEN
  SPEC_TAC(`values:num list`,`values:num list`) THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_list_def;
                candle_cv_tame_num_list_valid_aux_def;
                candle_tame_num_list_valid_aux_logical_def;
                candle_tame_cv_bool_def; cexp_eq_def;
                injectivity "cval"; ARITH_RULE `1 = SUC 0`];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_list_def;
                candle_cv_tame_num_list_valid_aux_def;
                candle_tame_num_list_valid_aux_logical_def;
                cexp_ispair_def; candle_tame_cv_if_correct;
                candle_tame_cv_num_less_correct;
                candle_cv_tame_num_member_correct] THEN
    ONCE_REWRITE_TAC
      [GSYM (CONJUNCT2 candle_cv_num_list_def)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[cexp_if_def] THEN
    ASM_CASES_TAC `a0 < bound` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `candle_tame_num_member_logical a0 seen` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
      `candle_tame_num_list_valid_aux_logical
         bound (CONS a0 seen) a1` THEN
    ASM_REWRITE_TAC[candle_tame_cv_bool_def]]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE num-list-aux";;

let candle_cv_tame_num_list_valid_correct = prove
 (`!bound values:num list.
     candle_cv_tame_num_list_valid
       (Cexp_num bound) (candle_cv_num_list values) =
     candle_tame_cv_bool
       (candle_tame_num_list_valid_logical bound values)`,
  REWRITE_TAC[candle_cv_tame_num_list_valid_def;
              candle_tame_num_list_valid_logical_def] THEN
  ONCE_REWRITE_TAC[GSYM (CONJUNCT1 candle_cv_num_list_def)] THEN
  REWRITE_TAC[candle_cv_tame_num_list_valid_aux_correct]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE num-list";;

let candle_tame_cv_num_list_ispair = prove
 (`!values:num list.
     Cexp_ispair (candle_cv_num_list values) =
     candle_tame_cv_bool (~(values = []))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_num_list_def; cexp_ispair_def;
              candle_tame_cv_bool_def; NOT_CONS_NIL;
              ARITH_RULE `1 = SUC 0`]);;

let candle_cv_tame_fgraph_valid_correct = prove
 (`!bound graph:(num list)list.
     candle_cv_tame_fgraph_valid
       (Cexp_num bound) (candle_cv_num_lists graph) =
     candle_tame_cv_bool
       (candle_tame_fgraph_valid_logical bound graph)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_num_lists_def;
                candle_cv_tame_fgraph_valid_def;
                candle_tame_fgraph_valid_logical_def;
                candle_tame_cv_bool_def; cexp_eq_def;
                injectivity "cval"; ARITH_RULE `1 = SUC 0`];
    ASM_REWRITE_TAC[candle_cv_num_lists_def;
                    candle_cv_tame_fgraph_valid_def;
                    candle_tame_fgraph_valid_logical_def;
                    cexp_ispair_def; candle_tame_cv_num_list_ispair;
                    candle_cv_tame_num_list_valid_correct;
                    candle_tame_cv_if_correct] THEN
    ASM_CASES_TAC `h:num list = []` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `candle_tame_num_list_valid_logical bound h` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `candle_tame_fgraph_valid_logical bound t` THEN
    ASM_REWRITE_TAC[candle_tame_cv_bool_def]]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE fgraph";;

let candle_cv_tame_nonempty_fgraph_valid_correct = prove
 (`!bound graph:(num list)list.
     candle_cv_tame_nonempty_fgraph_valid
       (Cexp_num bound) (candle_cv_num_lists graph) =
     candle_tame_cv_bool
       (candle_tame_nonempty_fgraph_valid_logical bound graph)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_tame_nonempty_fgraph_valid_def;
                candle_tame_nonempty_fgraph_valid_logical_def;
                candle_cv_num_lists_def; candle_tame_cv_bool_def;
                cexp_if_def; cexp_ispair_def];
    REWRITE_TAC[candle_cv_tame_nonempty_fgraph_valid_def;
                candle_tame_nonempty_fgraph_valid_logical_def;
                candle_cv_num_lists_def;
                candle_cv_tame_fgraph_valid_correct;
                NOT_CONS_NIL; cexp_if_def; cexp_ispair_def;
                ARITH_RULE `1 = SUC 0`]]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE nonempty-fgraph";;

let candle_cv_tame_vertex_map_valid_aux_correct = prove
 (`!source_bound target_bound seen_sources seen_targets mapping.
     candle_cv_tame_vertex_map_valid_aux
       (Cexp_num source_bound) (Cexp_num target_bound)
       (candle_cv_num_list seen_sources) (candle_cv_num_list seen_targets)
       (candle_cv_num_pair_list mapping) =
     candle_tame_cv_bool
       (candle_tame_vertex_map_valid_aux_logical
         source_bound target_bound seen_sources seen_targets mapping)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`seen_targets:num list`,`seen_targets:num list`) THEN
  SPEC_TAC(`seen_sources:num list`,`seen_sources:num list`) THEN
  SPEC_TAC(`mapping:(num#num)list`,`mapping:(num#num)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_pair_list_def;
                candle_cv_tame_vertex_map_valid_aux_def;
                candle_tame_vertex_map_valid_aux_logical_def;
                candle_tame_cv_bool_def; cexp_eq_def;
                injectivity "cval"; ARITH_RULE `1 = SUC 0`];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_pair_list_def;
                candle_cv_tame_vertex_map_valid_aux_def;
                candle_tame_vertex_map_valid_aux_logical_def;
                cexp_ispair_def; cexp_fst_def; cexp_snd_def;
                candle_tame_cv_if_correct;
                candle_tame_cv_num_less_correct;
                candle_cv_tame_num_member_correct; FST; SND] THEN
    ONCE_REWRITE_TAC[GSYM (CONJUNCT2 candle_cv_num_list_def)] THEN
    ONCE_REWRITE_TAC[GSYM (CONJUNCT2 candle_cv_num_list_def)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[cexp_if_def] THEN
    ASM_CASES_TAC `FST (a0:num#num) < source_bound` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `SND (a0:num#num) < target_bound` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
      `candle_tame_num_member_logical (FST (a0:num#num)) seen_sources` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
      `candle_tame_num_member_logical (SND (a0:num#num)) seen_targets` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
      `candle_tame_vertex_map_valid_aux_logical
         source_bound target_bound
         (CONS (FST (a0:num#num)) seen_sources)
         (CONS (SND (a0:num#num)) seen_targets) a1` THEN
    ASM_REWRITE_TAC[candle_tame_cv_bool_def]]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE vertex-map-aux";;

let candle_cv_tame_vertex_map_valid_correct = prove
 (`!source_bound target_bound mapping.
     candle_cv_tame_vertex_map_valid
       (Cexp_num source_bound) (Cexp_num target_bound)
       (candle_cv_num_pair_list mapping) =
     candle_tame_cv_bool
       (candle_tame_vertex_map_valid_logical
         source_bound target_bound mapping)`,
  REWRITE_TAC[candle_cv_tame_vertex_map_valid_def;
              candle_tame_vertex_map_valid_logical_def] THEN
  ONCE_REWRITE_TAC[GSYM (CONJUNCT1 candle_cv_num_list_def)] THEN
  ONCE_REWRITE_TAC[GSYM (CONJUNCT1 candle_cv_num_list_def)] THEN
  REWRITE_TAC[candle_cv_tame_vertex_map_valid_aux_correct]);;

let _ = print_endline "CANDLE_TAME_DATA_SOUND_PHASE vertex-map";;

end;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_DATA_SOUND_OK DEVELOPMENT_NON_RELEASE";;
