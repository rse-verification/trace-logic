(* Examples for the verification conditions, on the procedure
   m { if x <= 0 then x := 0 else (x := x - 1; m()) } of thesis Examples
   3.1, 4.31 and 4.32 (see verifExamples). *)

Theory vcExamples
Ancestors
  combin pred_set list traces tracesSem verifEff verifNorm verifPred verifFtc
  verifExamples folString folRec vcContract vcPcc vcGen vcSound vcXs
Libs
  intLib

(* ------------------------------------------------------------------------ *)
(* Procedure contracts by the procedure contract condition                  *)
(* ------------------------------------------------------------------------ *)

(* Example 3.1: <true, x = 0 /\ y = y0> *)
Definition ct31_def:
  ct31 m =
    if m = "m" then
      SOME (b_true, tb_and (tb_eq (ta_var "x") (ta_num 0))
                           (tb_eq (ta_var "y") (ta_old "y")))
    else NONE
End

Theorem ct31_pcc_valid:
  !m. pcc_valid m_tbl (cpre ct31) (cpost ct31) m
Proof
  rw[pcc_valid_def, m_tbl_def, AllCaseEqs()] >- EVAL_TAC >>
  EVAL_TAC >> rw[] >> rw[APPLY_UPDATE_THM]
QED

(* Lemma 4.36 gives the conformance of m, with the contract of Example 3.1
   (pre31, post31 in verifExamples) *)
Theorem ct31_conforms:
  conforms m_tbl (cpre ct31) (cpost ct31) /\
  cpre ct31 "m" = pre31 "m" /\ cpost ct31 "m" = post31 "m"
Proof
  rw[pcc_conforms, ct31_pcc_valid] >>
  rw[FUN_EQ_THM, cpre_def, cpost_def, ct31_def, pre31_def, post31_def] >>
  EVAL_TAC
QED

(* the contract condition rejects the wrong contract <true, y = y0 + 1> *)
Definition ct_wrong_def:
  ct_wrong m =
    if m = "m" then
      SOME (b_true, tb_eq (ta_var "y") (ta_plus (ta_old "y") (ta_num 1)))
    else NONE
End

Theorem ct_wrong_not_pcc_valid:
  ~pcc_valid m_tbl (cpre ct_wrong) (cpost ct_wrong) "m"
Proof
  rw[pcc_valid_def, m_tbl_def] >> disj2_tac >>
  qexists_tac `\i. if i <= 2 then (K 0) else ("x" =+ 0) (K 0)` >>
  EVAL_TAC >> rw[FUN_EQ_THM, APPLY_UPDATE_THM]
QED

(* ------------------------------------------------------------------------ *)
(* End to end, through first-order logic                                    *)
(* ------------------------------------------------------------------------ *)

(* the same contract for every procedure name, as in verifExamples *)
Definition ct_all_def:
  ct_all q (m:string) = SOME (b_true, q)
End

Theorem cpre_ct_all:
  !q. cpre (ct_all q) = pre31
Proof
  rw[FUN_EQ_THM, cpre_def, ct_all_def, pre31_def, b_eval_def]
QED

Theorem cpost_ct_all:
  !q. cpost (ct_all q) = \m s0 s. tb_eval q s0 s
Proof
  rw[FUN_EQ_THM, cpost_def, ct_all_def]
QED

(* x = 0 /\ y = y0 *)
Definition q31_def:
  q31 = tb_and (tb_eq (ta_var "x") (ta_num 0)) (tb_eq (ta_var "y") (ta_old "y"))
End

(* x = 0 *)
Definition q431_def:
  q431 = tb_eq (ta_var "x") (ta_num 0)
End

(* x = 0 /\ z = z0 *)
Definition q432_def:
  q432 = tb_and (tb_eq (ta_var "x") (ta_num 0)) (tb_eq (ta_var "z") (ta_old "z"))
End

Theorem cpost_q31:
  cpost (ct_all q31) = post31
Proof
  rw[cpost_ct_all, FUN_EQ_THM, post31_def, q31_def] >> EVAL_TAC
QED

Theorem cpost_q431:
  cpost (ct_all q431) = post431
Proof
  rw[cpost_ct_all, FUN_EQ_THM, post431_def, q431_def] >> EVAL_TAC
QED

Theorem cpost_q432:
  cpost (ct_all q432) = post432
Proof
  rw[cpost_ct_all, FUN_EQ_THM, post432_def, q432_def] >> EVAL_TAC
QED

Theorem norm_lk_m_tbl:
  norm_lk m_tbl = m_tbl
Proof
  rw[FUN_EQ_THM, norm_lk_def, m_tbl_def] >> rw[] >> EVAL_TAC
QED

Theorem m_tbl_alist:
  m_tbl = ALOOKUP [("m", m_body)]
Proof
  rw[m_tbl_def]
QED

(* the contract condition of m holds in M for all three contracts *)
Theorem pcc_valid_fol_m:
  !q v. MEM q [q31; q431; q432] ==>
        sholds (rec_model UNIV) v (pcc_valid_fol (ct_all q) "m" (norm m_body))
Proof
  rw[sholds_pcc_valid_fol, cpre_ct_all, cpost_q31, cpost_q431,
     cpost_q432] >>
  EVAL_TAC >> rw[] >> rw[APPLY_UPDATE_THM]
QED

(* Example 3.1: the verification conditions hold in M *)
Theorem ex31_vc_fols:
  !f v. MEM f (vc_fols [("m", m_body)] (ct_all q31) 20 S31 phi31) ==>
        sholds (rec_model UNIV) v f
Proof
  rw[vc_fols_def]
  >- (rw[sholds_vc_main, cpre_ct_all, cpost_q31, GSYM m_tbl_alist,
         norm_lk_m_tbl, ftc_dom_univ] >>
      `norm S31 = S31` by EVAL_TAC >> fs[ex31_vc])
  >- rw[pcc_valid_fol_m]
QED

(* hence, by end-to-end soundness, the specification holds *)
Theorem ex31_fol:
  !relI. Str m_tbl (K {}) S31 SUBSET fsem relI phi31
Proof
  rw[m_tbl_alist] >> irule vc_fols_sound >> conj_tac
  >- (qexistsl_tac [`ct_all q31`, `20`] >> rw[ex31_vc_fols])
  >- EVAL_TAC
QED

(* Example 4.32: with the contract x = 0, the main verification condition
   does not hold in M, for any fuel *)
Theorem ex432_fol_weak_fails:
  !n. ?v. ~sholds (rec_model UNIV) v
             (vc_main m_tbl (ct_all q431) n S432 (distr (expand phi431)))
Proof
  rw[sholds_vc_main, cpre_ct_all, cpost_q431, norm_lk_m_tbl,
     ftc_dom_univ] >>
  `norm S432 = S432` by EVAL_TAC >> rw[] >>
  strip_assume_tac ex432_weak_fails >> metis_tac[]
QED

(* with the contract x = 0 /\ z = z0, the verification conditions hold *)
Theorem ex432_fol:
  !relI. Str m_tbl (K {}) S432 SUBSET fsem relI phi431
Proof
  rw[m_tbl_alist] >>
  once_rewrite_tac[GSYM fsem_expand] >> once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_fols_sound >> conj_tac
  >- (qexistsl_tac [`ct_all q432`, `30`] >> rw[] >> fs[vc_fols_def]
      >- (rw[sholds_vc_main, cpre_ct_all, cpost_q432, GSYM m_tbl_alist,
             norm_lk_m_tbl, ftc_dom_univ] >>
          `norm S432 = S432` by EVAL_TAC >> fs[ex432_vc])
      >- rw[pcc_valid_fol_m])
  >- EVAL_TAC
QED

(* ------------------------------------------------------------------------ *)
(* Example 3.1 over the states of the program variables x and y             *)
(* ------------------------------------------------------------------------ *)

(* the verification conditions, with Id and Sb over x and y, hold in M with
   State denoting the states over x and y *)
Theorem ex31_xs_vc:
  !f v. MEM f (vc_fols_xs ["x"; "y"] [("m", m_body)] (ct_all q31) 20 S31
                          phi31) /\
        (!x. v x IN (rec_model (xs_states ["x"; "y"])).SDom) ==>
        sholds (rec_model (xs_states ["x"; "y"])) v f
Proof
  rw[vc_fols_xs_def, MEM_MAP] >> rw[sholds_expand_atoms] >>
  fs[vc_fols_def]
  >- (rw[sholds_vc_main, cpre_ct_all, cpost_q31, GSYM m_tbl_alist,
         norm_lk_m_tbl] >>
      irule (cj 1 ftc_ftc_dom) >>
      `norm S31 = S31` by EVAL_TAC >> fs[ex31_vc])
  >- (rw[sholds_pcc_valid_fol] >>
      qspecl_then [`q31`, `ARB`] mp_tac pcc_valid_fol_m >>
      rw[sholds_pcc_valid_fol])
QED

Theorem ex31_xs:
  !relI. Str m_tbl (K {}) S31 SUBSET fsem relI phi31
Proof
  rw[m_tbl_alist] >> irule vc_fols_xs_sound >> rw[]
  >- EVAL_TAC
  >- (qexistsl_tac [`ct_all q31`, `20`, `["x"; "y"]`] >> rw[ex31_xs_vc] >>
      EVAL_TAC >> rw[ct_over_def, ct_all_def] >> EVAL_TAC >> rw[])
QED
