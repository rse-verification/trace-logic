(* The examples of the evaluation of the tool in thesis Section 5.4
   (Table 5.1) that the tool decides correctly: Examples 5.5, 5.6, 5.8,
   5.10 and 5.12. The accepted examples are verified end to end, both in
   the structure with all states and in the structure with the states over
   the program variables (the Z3 form); for the rejected Example 5.6, the
   verification condition fails for every fuel, and the program indeed
   violates its specification. *)

Theory vcEval
Ancestors
  arithmetic pred_set list rich_list alist combin traces tracesSem
  verifChop verifEff verifNorm verifTc verifPred verifFtc verifExamples
  folString folRec vcContract vcPcc vcGen vcSound vcXs vcExamples
Libs
  intLib

(* ------------------------------------------------------------------------ *)
(* From the shallow conditions to the generated formulas                    *)
(* ------------------------------------------------------------------------ *)

(* If the shallow verification conditions hold, the generated formulas hold
   in M_D for every D. *)
Theorem vc_fols_of_shallow:
  !tbl ct n S0 phi.
    (!g. tc (cpre ct) (cpost ct) 1 (norm S0) g ==>
         ftc (norm_lk (ALOOKUP tbl)) (cpre ct) (cpost ct) n 1 (norm S0) phi
             [] g) /\
    (!m b. MEM (m, b) tbl ==>
           !g. cpre ct m (g 1) ==>
               pcc (cpre ct) (cpost ct) (cpost ct m) (g 1) 1 (norm b) g) ==>
    !D f v. MEM f (vc_fols tbl ct n S0 phi) ==> sholds (rec_model D) v f
Proof
  rw[vc_fols_def, MEM_MAP]
  >- (rw[sholds_vc_main] >> irule (cj 1 ftc_ftc_dom) >> metis_tac[])
  >- (PairCases_on `y` >> rw[sholds_pcc_valid_fol] >> metis_tac[])
QED

(* the same for the formulas with Id and Sb over xs *)
Theorem vc_fols_xs_of_shallow:
  !xs tbl ct n S0 phi.
    (!g. tc (cpre ct) (cpost ct) 1 (norm S0) g ==>
         ftc (norm_lk (ALOOKUP tbl)) (cpre ct) (cpost ct) n 1 (norm S0) phi
             [] g) /\
    (!m b. MEM (m, b) tbl ==>
           !g. cpre ct m (g 1) ==>
               pcc (cpre ct) (cpost ct) (cpost ct m) (g 1) 1 (norm b) g) ==>
    !f v. MEM f (vc_fols_xs xs tbl ct n S0 phi) /\
          (!x. v x IN (rec_model (xs_states xs)).SDom) ==>
          sholds (rec_model (xs_states xs)) v f
Proof
  rw[vc_fols_xs_def, MEM_MAP] >> rw[sholds_expand_atoms] >>
  metis_tac[vc_fols_of_shallow]
QED

(* ------------------------------------------------------------------------ *)
(* Notation                                                                 *)
(* ------------------------------------------------------------------------ *)

Overload fId = ``f_rel R_Id``
Overload fstate = ``\b. f_state (p_b b)``
Overload ax = ``a_var "x"``
Overload ay = ``a_var "y"``
Overload az = ``a_var "z"``

(* b1 \/ b2 and the contract connectives, from negation and conjunction *)
Definition bor_def:
  bor b1 b2 = b_neg (b_and (b_neg b1) (b_neg b2))
End

Definition timp_def:
  timp q1 q2 = tb_neg (tb_and q1 (tb_neg q2))
End

(* x = 0 *)
Overload bx0 = ``b_eq ax (a_num 0)``

(* the specification of Examples 5.5 and 5.6:
   Id ^ (mu X_m. Id ^ (Sb^0_x \/ Sb^(x-1)_x ^ Id ^ X_m)) ^ (x = 0) *)
Definition phi55_def:
  phi55 = f_chop fId (f_chop (f_mu "m" psi31) (fstate bx0))
End

(* m(); skip *)
Definition S55_def:
  S55 = S_seq (S_call "m") S_skip
End

(* ------------------------------------------------------------------------ *)
(* Example 5.5                                                              *)
(* ------------------------------------------------------------------------ *)

(* the procedure m and contract <true, x = 0> are those of Example 4.31 *)

(* The trace constraints have the shape of the SMT assertion in the thesis:
   (and (=> true (= (x state3) 0)) (and (id state1 state2) (id state3
   state4))), up to the order of the conjuncts. *)
Theorem ex55_tc_shape:
  tc_fol (ct_all q431) 1 (norm S55) =
  SAnd (SAnd (Id_sform (svar 1) (svar 2))
             (SImp STrue
                   (SPred "=" [SFn "sel_x" [SV "s3"]; SFn "0" []])))
       (Id_sform (svar 3) (svar 4))
Proof
  EVAL_TAC
QED

Theorem ex55_vc:
  !g. tc (cpre (ct_all q431)) (cpost (ct_all q431)) 1 (norm S55) g ==>
      ftc (norm_lk m_tbl) (cpre (ct_all q431)) (cpost (ct_all q431)) 20 1
          (norm S55) (distr (expand phi55)) [] g
Proof
  rw[cpre_ct_all, cpost_q431, norm_lk_m_tbl] >>
  pop_assum mp_tac >> EVAL_TAC >> rw[] >> fs[] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] >> intLib.ARITH_TAC
QED

Theorem ex55_pcc:
  !m b. MEM (m, b) [("m", m_body)] ==>
        !g. cpre (ct_all q431) m (g 1) ==>
            pcc (cpre (ct_all q431)) (cpost (ct_all q431))
                (cpost (ct_all q431) m) (g 1) 1 (norm b) g
Proof
  rw[cpre_ct_all, cpost_q431] >> EVAL_TAC >> rw[] >> rw[APPLY_UPDATE_THM]
QED

Theorem ex55:
  !relI. Str m_tbl (K {}) S55 SUBSET fsem relI phi55
Proof
  rw[m_tbl_alist] >>
  once_rewrite_tac[GSYM fsem_expand] >> once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_fols_sound >> conj_tac
  >- (qexistsl_tac [`ct_all q431`, `20`] >> rw[] >>
      irule vc_fols_of_shallow >>
      qexistsl_tac [`S55`, `ct_all q431`, `20`, `distr (expand phi55)`,
                    `[("m", m_body)]`] >>
      rw[ex55_pcc, GSYM m_tbl_alist, ex55_vc])
  >- EVAL_TAC
QED

Theorem ex55_xs:
  !relI. Str m_tbl (K {}) S55 SUBSET fsem relI phi55
Proof
  rw[m_tbl_alist] >>
  once_rewrite_tac[GSYM fsem_expand] >> once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_fols_xs_sound >> rw[]
  >- EVAL_TAC
  >- (qexistsl_tac [`ct_all q431`, `20`, `["x"]`] >> rw[] >>
      TRY (rw[ct_over_def, ct_all_def, q431_def] >> EVAL_TAC >> rw[] >>
           NO_TAC) >>
      TRY (EVAL_TAC >> rw[] >> NO_TAC) >>
      irule vc_fols_xs_of_shallow >> conj_tac >- rw[] >>
      qexistsl_tac [`S55`, `ct_all q431`, `20`, `distr (expand phi55)`,
                    `[("m", m_body)]`] >>
      rw[ex55_pcc, GSYM m_tbl_alist, ex55_vc])
QED

(* ------------------------------------------------------------------------ *)
(* Example 5.6                                                              *)
(* ------------------------------------------------------------------------ *)

(* m { if x <= 0 then skip else (x := x - 1; m()) } *)
Definition m56_body_def:
  m56_body =
    S_ifelse (b_leq ax (a_num 0)) S_skip
             (S_seq (S_assign "x" (a_minus ax (a_num 1))) (S_call "m"))
End

(* <x >= 0, x = 0> *)
Definition ct56_def:
  ct56 (m:string) = SOME (b_leq (a_num 0) ax, q431)
End

(* Unfold ftc with a fuel variable n by a case split on n, until no such
   ftc is left (as in verifExamples). *)
val ftc_tm = prim_mk_const {Thy = "verifFtc", Name = "ftc"};

fun fuel_var t =
  let val (f, args) = strip_comb t
  in
    if same_const f ftc_tm andalso length args = 9 andalso
       is_var (el 4 args)
    then SOME (el 4 args) else NONE
  end;

val fuel_tac : tactic = fn (asl, w) =>
  let val n = valOf (fuel_var (find_term (isSome o fuel_var) w))
  in
    (Cases_on `^n` >> CONV_TAC EVAL >> asm_simp_tac std_ss []) (asl, w)
  end;

(* the call needs the precondition x >= 0, for any fuel *)
Theorem ex56_ftc_fails[local]:
  !g n. ~(0 <= g 2 "x") ==>
        ~ftc (norm_lk (ALOOKUP [("m", m56_body)])) (cpre ct56) (cpost ct56) n 1
             (norm S55) (distr (expand phi55)) [] g
Proof
  rewrite_tac[EVAL ``distr (expand phi55)``, EVAL ``norm S55``] >>
  rpt gen_tac >> strip_tac >> rpt fuel_tac
QED

(* The tool rejects Example 5.6 correctly: the main verification condition
   does not hold, for any fuel ... *)
Theorem ex56_rejected:
  !n. ?v. ~sholds (rec_model UNIV) v
             (vc_main (ALOOKUP [("m", m56_body)]) ct56 n S55
                      (distr (expand phi55)))
Proof
  rw[sholds_vc_main, ftc_dom_univ] >>
  qexists_tac `K (("x" =+ -1) (K 0))` >> rw[ex56_ftc_fails, APPLY_UPDATE_THM]
  >- (EVAL_TAC >> rw[APPLY_UPDATE_THM])
QED

(* traces in which some state satisfies P *)
Theorem chop_some_state:
  !A B t P. t IN chop A B /\ (!u. u IN B ==> ?s. MEM s u /\ P s) ==>
            ?s. MEM s t /\ P s
Proof
  rw[IN_chop] >> first_x_assum drule >> strip_tac >> qexists_tac `s` >>
  rw[] >> Cases_on `t2` >> fs[] >> rw[] >> metis_tac[MEM_LAST_NOT_NIL]
QED

(* ... and the program indeed violates the specification: the trace from
   a state with x = -1 never reaches x = 0 *)
Theorem ex56_violation:
  ?t. t IN Str (ALOOKUP [("m", m56_body)]) (K {}) S55 /\
      !relI. t NOTIN fsem relI phi55
Proof
  qabbrev_tac `s = ("x" =+ -1) (K 0) : state` >>
  qexists_tac `[s; s; s; s; s]` >> rw[]
  >- (`ALOOKUP [("m", m56_body)] "m" = SOME m56_body` by EVAL_TAC >>
      `[s; s; s; s] IN Str (ALOOKUP [("m", m56_body)]) (K {}) (S_call "m")`
        by (drule Str_call >> disch_then (qspec_then `K {}` SUBST1_TAC) >>
            rw[dup_def, Str_def, m56_body_def, Str0_def, restrict_def,
               b_eval_def, a_eval_def, Abbr `s`, APPLY_UPDATE_THM]) >>
      fs[Str_def, S55_def, Str0_def, IN_chop] >>
      qexistsl_tac [`[s; s; s; s]`, `[s; s]`] >> rw[])
  >- (strip_tac >> fs[phi55_def, fsem_chop] >>
      `!u. u IN fsem relI (fstate bx0) ==> ?s'. MEM s' u /\ s' "x" = 0`
        by (rw[fsem_def, f_sem_def, p_sem_def, b_eval_def, a_eval_def] >>
            metis_tac[MEM]) >>
      `!u. u IN chop (fsem relI (f_mu "m" psi31)) (fsem relI (fstate bx0))
           ==> ?s'. MEM s' u /\ s' "x" = 0`
        by (rpt strip_tac >>
            qspecl_then [`fsem relI (f_mu "m" psi31)`,
                         `fsem relI (fstate bx0)`, `u`,
                         `\s. s "x" = 0`] mp_tac chop_some_state >>
            rw[]) >>
      `?s'. MEM s' [s; s; s; s; s] /\ s' "x" = 0`
        by (qspecl_then [`fsem relI fId`,
                         `chop (fsem relI (f_mu "m" psi31))
                               (fsem relI (fstate bx0))`,
                         `[s; s; s; s; s]`, `\s. s "x" = 0`]
              mp_tac chop_some_state >> rw[]) >>
      fs[Abbr `s`] >> rw[] >> fs[APPLY_UPDATE_THM])
QED

(* ------------------------------------------------------------------------ *)
(* Examples 5.8 and 5.10                                                    *)
(* ------------------------------------------------------------------------ *)

(* n { if x >= 0 then skip else (x := x + 1; n()) }; the thesis writes
   xl + 1 for x + 1 *)
Definition n58_body_def:
  n58_body =
    S_ifelse (b_leq (a_num 0) ax) S_skip
             (S_seq (S_assign "x" (a_plus ax (a_num 1))) (S_call "n"))
End

(* m is the procedure of Example 5.6 *)
Definition tbl58_def:
  tbl58 = [("m", m56_body); ("n", n58_body)]
End

(* x = 0 /\ y = y0 /\ z = z0 *)
Definition q58_def:
  q58 = tb_and (tb_eq (ta_var "x") (ta_num 0))
               (tb_and (tb_eq (ta_var "y") (ta_old "y"))
                       (tb_eq (ta_var "z") (ta_old "z")))
End

(* <x >= 0, q58> for m and <x <= 0, q58> for n *)
Definition ct58_def:
  ct58 (m:string) =
    if m = "m" then SOME (b_leq (a_num 0) ax, q58)
    else if m = "n" then SOME (b_leq ax (a_num 0), q58)
    else NONE
End

(* if x < 0 then n() else m() *)
Overload call58 = ``S_ifelse (b_neg (b_leq (a_num 0) ax)) (S_call "n")
                             (S_call "m")``

(* (if x < 0 then n() else m()); z := x; x := y;
   (if x < 0 then n() else m()); y := z; skip *)
Definition S58_def:
  S58 = S_seq call58
          (S_seq (S_assign "z" ax)
             (S_seq (S_assign "x" ay)
                (S_seq call58 (S_seq (S_assign "y" az) S_skip))))
End

Overload ftrue = ``fstate b_true``
(* x = 0 /\ y = 0 *)
Overload fxy0 = ``fstate (b_and bx0 (b_eq ay (a_num 0)))``

(* Example 5.10: true ^ true ^ Sb^z_y ^ (x = 0 /\ y = 0) *)
Definition phi510_def:
  phi510 = f_chop ftrue (f_chop ftrue (f_chop (f_rel (R_Sb az "y")) fxy0))
End

Theorem not_le_0[local]:
  !x:int. ~(0 <= x) ==> x <= 0
Proof
  intLib.ARITH_TAC
QED

Theorem ex58_pcc:
  !m b. MEM (m, b) tbl58 ==>
        !g. cpre ct58 m (g 1) ==>
            pcc (cpre ct58) (cpost ct58) (cpost ct58 m) (g 1) 1 (norm b) g
Proof
  rw[tbl58_def] >> pop_assum mp_tac >> EVAL_TAC >> rw[] >>
  fs[APPLY_UPDATE_THM] >> rfs[APPLY_UPDATE_THM] >>
  TRY (intLib.ARITH_TAC >> NO_TAC) >>
  NO_TAC
QED

Theorem ex510_vc:
  !g. tc (cpre ct58) (cpost ct58) 1 (norm S58) g ==>
      ftc (norm_lk (ALOOKUP tbl58)) (cpre ct58) (cpost ct58) 40 1
          (norm S58) (distr (expand phi510)) [] g
Proof
  EVAL_TAC >> rw[] >> fs[] >> rfs[APPLY_UPDATE_THM] >>
  imp_res_tac not_le_0 >> res_tac >>
  NTAC 3 (fs[APPLY_UPDATE_THM] >> rfs[APPLY_UPDATE_THM]) >>
  TRY (intLib.ARITH_TAC >> NO_TAC) >> NO_TAC
QED

(* the end-to-end results, in both versions *)
val e2e_tac = fn (S, ct, n, phi, tbl, vc, pcc) =>
  rw[] >>
  once_rewrite_tac[GSYM fsem_expand] >> once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_fols_sound >> conj_tac
  >- (qexistsl_tac [ct, n] >> rw[] >>
      irule vc_fols_of_shallow >>
      qexistsl_tac [S, ct, n, phi, tbl] >> rw[pcc, vc])
  >- EVAL_TAC;

val e2e_xs_tac = fn (xs, S, ct, n, phi, tbl, vc, pcc, ctdefs) =>
  rw[] >>
  once_rewrite_tac[GSYM fsem_expand] >> once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_fols_xs_sound >> rw[] >>
  TRY (EVAL_TAC >> NO_TAC) >>
  qexistsl_tac [ct, n, xs] >> rw[] >>
  TRY (fs(ct_over_def :: ctdefs) >> rw[] >> EVAL_TAC >> rw[] >> NO_TAC) >>
  TRY (EVAL_TAC >> rw[] >> NO_TAC) >>
  irule vc_fols_xs_of_shallow >> conj_tac >- rw[] >>
  qexistsl_tac [S, ct, n, phi, tbl] >> rw[pcc, vc];

Theorem ex510:
  !relI. Str (ALOOKUP tbl58) (K {}) S58 SUBSET fsem relI phi510
Proof
  e2e_tac (`S58`, `ct58`, `40`, `distr (expand phi510)`, `tbl58`,
           ex510_vc, ex58_pcc)
QED

Theorem ex510_xs:
  !relI. Str (ALOOKUP tbl58) (K {}) S58 SUBSET fsem relI phi510
Proof
  e2e_xs_tac (`["x"; "y"; "z"]`, `S58`, `ct58`, `40`,
              `distr (expand phi510)`, `tbl58`, ex510_vc, ex58_pcc,
              [ct58_def, q58_def, tbl58_def])
QED

(* Example 5.8: true ^ true ^ true ^ (x = 0 /\ y = 0) *)
Definition phi58_def:
  phi58 = f_chop ftrue (f_chop ftrue (f_chop ftrue fxy0))
End

Theorem ex58_vc:
  !g. tc (cpre ct58) (cpost ct58) 1 (norm S58) g ==>
      ftc (norm_lk (ALOOKUP tbl58)) (cpre ct58) (cpost ct58) 40 1
          (norm S58) (distr (expand phi58)) [] g
Proof
  EVAL_TAC >> rw[] >> fs[] >> rfs[APPLY_UPDATE_THM] >>
  Cases_on `0 <= g 1 "x"` >> Cases_on `0 <= g 4 "y"` >>
  imp_res_tac not_le_0 >> res_tac >>
  NTAC 2 (fs[APPLY_UPDATE_THM] >> rfs[APPLY_UPDATE_THM]) >>
  full_simp_tac (srw_ss() ++ intSimps.INT_ARITH_ss) [APPLY_UPDATE_THM] >>
  NO_TAC
QED

Theorem ex58:
  !relI. Str (ALOOKUP tbl58) (K {}) S58 SUBSET fsem relI phi58
Proof
  e2e_tac (`S58`, `ct58`, `40`, `distr (expand phi58)`, `tbl58`,
           ex58_vc, ex58_pcc)
QED

Theorem ex58_xs:
  !relI. Str (ALOOKUP tbl58) (K {}) S58 SUBSET fsem relI phi58
Proof
  e2e_xs_tac (`["x"; "y"; "z"]`, `S58`, `ct58`, `40`,
              `distr (expand phi58)`, `tbl58`, ex58_vc, ex58_pcc,
              [ct58_def, q58_def, tbl58_def])
QED

(* ------------------------------------------------------------------------ *)
(* Example 5.12                                                             *)
(* ------------------------------------------------------------------------ *)

(* if x <= y then (y := y - x; gcd()) else (x := x - y; gcd()) *)
Definition gcd_step_def:
  gcd_step =
    S_ifelse (b_leq ax ay)
             (S_seq (S_assign "y" (a_minus ay ax)) (S_call "gcd"))
             (S_seq (S_assign "x" (a_minus ax ay)) (S_call "gcd"))
End

(* gcd { if x = y \/ x = 0 \/ y = 0 then skip else gcd_step } *)
Definition gcd_body_def:
  gcd_body =
    S_ifelse (bor (b_eq ax ay) (bor (b_eq ax (a_num 0)) (b_eq ay (a_num 0))))
             S_skip gcd_step
End

(* x0 > 0, y0 > 0 *)
Overload x0pos = ``tb_neg (tb_leq (ta_old "x") (ta_num 0))``
Overload y0pos = ``tb_neg (tb_leq (ta_old "y") (ta_num 0))``

(* <x >= 0 /\ y >= 0,
    x <= x0 /\ y <= y0 /\ (x0 > 0 ==> y <= x0) /\ (y0 > 0 ==> x <= y0)> *)
Definition ct512_def:
  ct512 (m:string) =
    SOME (b_and (b_leq (a_num 0) ax) (b_leq (a_num 0) ay),
          tb_and (tb_leq (ta_var "x") (ta_old "x"))
            (tb_and (tb_leq (ta_var "y") (ta_old "y"))
               (tb_and (timp x0pos (tb_leq (ta_var "y") (ta_old "x")))
                       (timp y0pos (tb_leq (ta_var "x") (ta_old "y"))))))
End

Definition tbl512_def:
  tbl512 = [("gcd", gcd_body)]
End

(* if x < 0 \/ y < 0 then skip else gcd() *)
Definition S512_def:
  S512 = S_ifelse (bor (b_neg (b_leq (a_num 0) ax))
                       (b_neg (b_leq (a_num 0) ay)))
                  S_skip (S_call "gcd")
End

(* (x = x /\ y = y) *)
Definition phi512_def:
  phi512 = fstate (b_and (b_eq ax ax) (b_eq ay ay))
End

Theorem ex512_pcc:
  !m b. MEM (m, b) tbl512 ==>
        !g. cpre ct512 m (g 1) ==>
            pcc (cpre ct512) (cpost ct512) (cpost ct512 m) (g 1) 1 (norm b) g
Proof
  rw[tbl512_def] >> pop_assum mp_tac >> EVAL_TAC >> rw[] >>
  fs[APPLY_UPDATE_THM] >> rfs[APPLY_UPDATE_THM] >>
  full_simp_tac (srw_ss() ++ intSimps.INT_ARITH_ss) [APPLY_UPDATE_THM] >>
  NO_TAC
QED

Theorem ex512_vc:
  !g. tc (cpre ct512) (cpost ct512) 1 (norm S512) g ==>
      ftc (norm_lk (ALOOKUP tbl512)) (cpre ct512) (cpost ct512) 20 1
          (norm S512) (distr (expand phi512)) [] g
Proof
  EVAL_TAC >> rw[] >> fs[] >> rfs[APPLY_UPDATE_THM] >>
  full_simp_tac (srw_ss() ++ intSimps.INT_ARITH_ss) [APPLY_UPDATE_THM] >>
  NO_TAC
QED

Theorem ex512:
  !relI. Str (ALOOKUP tbl512) (K {}) S512 SUBSET fsem relI phi512
Proof
  e2e_tac (`S512`, `ct512`, `20`, `distr (expand phi512)`, `tbl512`,
           ex512_vc, ex512_pcc)
QED

Theorem ex512_xs:
  !relI. Str (ALOOKUP tbl512) (K {}) S512 SUBSET fsem relI phi512
Proof
  e2e_xs_tac (`["x"; "y"]`, `S512`, `ct512`, `20`, `distr (expand phi512)`,
              `tbl512`, ex512_vc, ex512_pcc,
              [ct512_def, tbl512_def, timp_def])
QED
