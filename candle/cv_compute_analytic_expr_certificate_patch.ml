(* ========================================================================== *)
(* Logical certificate-data patching for stable analytic source programs.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Square-root intervals are numerical            *)
(* certificates, not mathematical source syntax.  The state-passing patchers  *)
(* below consume them in the exact postorder used by analytic compilation.    *)
(* They are total; a later checked boundary must additionally require that the *)
(* returned remainder is empty and that the supplied certificate count is     *)
(* exact.                                                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_erasure.ml";;
needs "candle/cv_compute_analytic_expr_program.ml";;

module Candle_cv_analytic_expr_certificate_patch = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_certificate_erasure;;

let candle_analytic_sqrt_with_interval_def = new_definition
 `candle_analytic_sqrt_with_interval
    (i:((num#num)#num)#((num#num)#num)) a =
    Candle_analytic_sqrt
      (FST (FST (FST i))) (SND (FST (FST i))) (SND (FST i))
      (FST (FST (SND i))) (SND (FST (SND i))) (SND (SND i)) a`;;

let candle_analytic_patch_sqrt_finish_def = define
 `(candle_analytic_patch_sqrt_finish lp ln ld up un ud a
      ([]:(((num#num)#num)#((num#num)#num))list) =
     ([],Candle_analytic_sqrt lp ln ld up un ud a)) /\
  (candle_analytic_patch_sqrt_finish lp ln ld up un ud a
      (CONS i intervals) =
     (intervals,candle_analytic_sqrt_with_interval i a))`;;

let candle_analytic_patch_sqrt_certificates_def = define
 `(candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_poly p) =
     (intervals,Candle_analytic_poly p)) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_neg a) =
     let patched = candle_analytic_patch_sqrt_certificates intervals a in
     (FST patched,Candle_analytic_neg (SND patched))) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_add a b) =
     let patched_a = candle_analytic_patch_sqrt_certificates intervals a in
     let patched_b =
       candle_analytic_patch_sqrt_certificates (FST patched_a) b in
     (FST patched_b,Candle_analytic_add (SND patched_a) (SND patched_b))) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_mul a b) =
     let patched_a = candle_analytic_patch_sqrt_certificates intervals a in
     let patched_b =
       candle_analytic_patch_sqrt_certificates (FST patched_a) b in
     (FST patched_b,Candle_analytic_mul (SND patched_a) (SND patched_b))) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_square a) =
     let patched = candle_analytic_patch_sqrt_certificates intervals a in
     (FST patched,Candle_analytic_square (SND patched))) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_inv a) =
     let patched = candle_analytic_patch_sqrt_certificates intervals a in
     (FST patched,Candle_analytic_inv (SND patched))) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     let patched = candle_analytic_patch_sqrt_certificates intervals a in
     candle_analytic_patch_sqrt_finish lp ln ld up un ud
       (SND patched) (FST patched)) /\
  (candle_analytic_patch_sqrt_certificates intervals
      (Candle_analytic_atn a) =
     let patched = candle_analytic_patch_sqrt_certificates intervals a in
     (FST patched,Candle_analytic_atn (SND patched))) /\
  (candle_analytic_patch_sqrt_certificates intervals
      Candle_analytic_pi_half =
     (intervals,Candle_analytic_pi_half))`;;

let candle_analytic_sqrt_count_def = define
 `(candle_analytic_sqrt_count (Candle_analytic_poly p) = 0) /\
  (candle_analytic_sqrt_count (Candle_analytic_neg a) =
     candle_analytic_sqrt_count a) /\
  (candle_analytic_sqrt_count (Candle_analytic_add a b) =
     candle_analytic_sqrt_count a + candle_analytic_sqrt_count b) /\
  (candle_analytic_sqrt_count (Candle_analytic_mul a b) =
     candle_analytic_sqrt_count a + candle_analytic_sqrt_count b) /\
  (candle_analytic_sqrt_count (Candle_analytic_square a) =
     candle_analytic_sqrt_count a) /\
  (candle_analytic_sqrt_count (Candle_analytic_inv a) =
     candle_analytic_sqrt_count a) /\
  (candle_analytic_sqrt_count
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     SUC (candle_analytic_sqrt_count a)) /\
  (candle_analytic_sqrt_count (Candle_analytic_atn a) =
     candle_analytic_sqrt_count a) /\
  (candle_analytic_sqrt_count Candle_analytic_pi_half = 0)`;;

let candle_analytic_patch_sqrt_finish_erasure = prove
 (`!intervals lp ln ld up un ud a.
     candle_analytic_erase_sqrt_certificates
       (SND
         (candle_analytic_patch_sqrt_finish lp ln ld up un ud a
           intervals)) =
     candle_analytic_erase_sqrt_certificates
       (Candle_analytic_sqrt lp ln ld up un ud a)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_analytic_patch_sqrt_finish_def;
              candle_analytic_sqrt_with_interval_def;
              candle_analytic_erase_sqrt_certificates_def; FST; SND]);;

let candle_analytic_patch_sqrt_certificates_erasure = prove
 (`!e intervals.
     candle_analytic_erase_sqrt_certificates
       (SND (candle_analytic_patch_sqrt_certificates intervals e)) =
     candle_analytic_erase_sqrt_certificates e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC
    [candle_analytic_patch_sqrt_certificates_def;
     candle_analytic_patch_sqrt_finish_erasure;
     candle_analytic_erase_sqrt_certificates_def;
     LET_DEF; LET_END_DEF; FST; SND]);;

let candle_analytic_instruction_patch_sqrt_def = define
 `(candle_analytic_instruction_patch_sqrt intervals
      (Candle_analytic_push_poly p) =
     (intervals,Candle_analytic_push_poly p)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_neg =
     (intervals,Candle_analytic_program_neg)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_add =
     (intervals,Candle_analytic_program_add)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_mul =
     (intervals,Candle_analytic_program_mul)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_square =
     (intervals,Candle_analytic_program_square)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_inv =
     (intervals,Candle_analytic_program_inv)) /\
  (candle_analytic_instruction_patch_sqrt
      ([]:(((num#num)#num)#((num#num)#num))list)
      (Candle_analytic_program_sqrt s) =
     ([],Candle_analytic_program_sqrt s)) /\
  (candle_analytic_instruction_patch_sqrt (CONS i intervals)
      (Candle_analytic_program_sqrt s) =
     (intervals,Candle_analytic_program_sqrt i)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_atn =
     (intervals,Candle_analytic_program_atn)) /\
  (candle_analytic_instruction_patch_sqrt intervals
      Candle_analytic_program_pi_half =
     (intervals,Candle_analytic_program_pi_half))`;;

let candle_analytic_program_patch_sqrt_def = define
 `(candle_analytic_program_patch_sqrt intervals [] =
     (intervals,[])) /\
  (candle_analytic_program_patch_sqrt intervals (CONS instruction program) =
     let patched_instruction =
       candle_analytic_instruction_patch_sqrt intervals instruction in
     let patched_program =
       candle_analytic_program_patch_sqrt
         (FST patched_instruction) program in
     (FST patched_program,
      CONS (SND patched_instruction) (SND patched_program)))`;;

let candle_analytic_program_patch_sqrt_append = prove
 (`!left right intervals.
     candle_analytic_program_patch_sqrt intervals (APPEND left right) =
     let patched_left =
       candle_analytic_program_patch_sqrt intervals left in
     let patched_right =
       candle_analytic_program_patch_sqrt (FST patched_left) right in
     (FST patched_right,APPEND (SND patched_left) (SND patched_right))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_program_patch_sqrt_def; APPEND;
                  LET_DEF; LET_END_DEF; FST; SND]);;

let candle_analytic_instruction_patch_sqrt_finish = prove
 (`!intervals lp ln ld up un ud a.
     (FST
       (candle_analytic_instruction_patch_sqrt intervals
         (Candle_analytic_program_sqrt
           (candle_analytic_sqrt_interval lp ln ld up un ud))),
      APPEND (candle_analytic_compile a)
        [SND
          (candle_analytic_instruction_patch_sqrt intervals
            (Candle_analytic_program_sqrt
              (candle_analytic_sqrt_interval lp ln ld up un ud)))]) =
     (FST
       (candle_analytic_patch_sqrt_finish lp ln ld up un ud a intervals),
      candle_analytic_compile
        (SND
          (candle_analytic_patch_sqrt_finish lp ln ld up un ud a
            intervals)))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC
    [candle_analytic_instruction_patch_sqrt_def;
     candle_analytic_patch_sqrt_finish_def;
     candle_analytic_sqrt_with_interval_def;
     candle_analytic_sqrt_interval_def;
     candle_analytic_compile_def; APPEND; FST; SND]);;

let candle_analytic_program_patch_sqrt_compile = prove
 (`!e intervals.
     candle_analytic_program_patch_sqrt intervals
       (candle_analytic_compile e) =
     let patched =
       candle_analytic_patch_sqrt_certificates intervals e in
     (FST patched,candle_analytic_compile (SND patched))`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_finish;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_append;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_analytic_patch_sqrt_certificates_def;
       candle_analytic_compile_def;
       candle_analytic_program_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       LET_DEF; LET_END_DEF; APPEND; FST; SND]] THEN
  PRINT_GOAL_TAC);;

end;;
