(* The conversion of a Rec program and a trace formula specification to
   first-order formulas, and its end-to-end soundness: if the formulas hold
   in the structure M of thesis Definition 4.2, then every trace of the
   program satisfies the specification. The thesis states no such result;
   its Algorithms 1 and 2 describe the conversion informally. *)

Theory vcSound
Ancestors
  arithmetic pred_set list alist combin string_num traces tracesSem
  verifEff verifNorm verifTc verifPred verifFtc folLang folModels
  folString folRec vcContract vcPcc vcGen

(* ------------------------------------------------------------------------ *)
(* The conversion                                                           *)
(* ------------------------------------------------------------------------ *)

(* the verification condition of Lemma 4.30 for S and phi, as one closed
   formula: forall s(1) ... s(N). tc_1(S') ==> ftc_1(S', phi, []), with S'
   and the procedure bodies normalized *)
Definition vc_main_def:
  vc_main (lk:lookup) (ct:ctable) n S0 phi =
    sforall_from 1 (SUC (stb (norm S0)))
      (SImp (tc_fol ct 1 (norm S0))
            (ftc_fol (norm_lk lk) ct n 1 (norm S0) phi []))
End

(* the verification conditions for the program <S, T> with procedure table
   tbl, contracts ct, specification phi and fuel n: the main condition and
   the procedure contract condition of each procedure (Lemma 4.36) *)
Definition vc_fols_def:
  vc_fols (tbl:(string # S) list) (ct:ctable) n S0 phi =
    vc_main (ALOOKUP tbl) ct n S0 phi ::
    MAP (\(m, body). pcc_valid_fol ct m (norm body)) tbl
End

(* ------------------------------------------------------------------------ *)
(* Soundness                                                                *)
(* ------------------------------------------------------------------------ *)

Theorem sholds_vc_main:
  !D lk ct n S0 phi v.
    sholds (rec_model D) v (vc_main lk ct n S0 phi) <=>
    !g. (!j. 1 <= j /\ j <= stb (norm S0) + 1 ==> g j IN D) /\
        tc (cpre ct) (cpost ct) 1 (norm S0) g ==>
        ftc_dom D (norm_lk lk) (cpre ct) (cpost ct) n 1 (norm S0) phi [] g
Proof
  rw[vc_main_def, sholds_sforall_from, sholds_def] >>
  `!h. vagree 1 (1 + stb (norm S0))
         (upd_from 1 (SUC (stb (norm S0))) h v) h`
    by metis_tac[vagree_upd_from] >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb (norm S0))) h v)
         (tc_fol ct 1 (norm S0)) <=> tc (cpre ct) (cpost ct) 1 (norm S0) h`
    by (gen_tac >> irule tc_fol_sem >> metis_tac[ADD_COMM]) >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb (norm S0))) h v)
         (ftc_fol (norm_lk lk) ct n 1 (norm S0) phi []) <=>
       ftc_dom D (norm_lk lk) (cpre ct) (cpost ct) n 1 (norm S0) phi [] h`
    by (gen_tac >> irule (cj 1 ftc_fol_sem) >> metis_tac[ADD_COMM]) >>
  fs[] >> EQ_TAC >> rw[] >> first_x_assum irule >> rw[] >>
  first_x_assum irule >> decide_tac
QED

(* End-to-end soundness: if the verification conditions hold in M under
   every valuation, the program satisfies the specification. *)
Theorem vc_fols_sound:
  !tbl ct n S0 phi relI.
    fv_f phi = [] /\
    (!f v. MEM f (vc_fols tbl ct n S0 phi) ==>
           sholds (rec_model UNIV) v f) ==>
    Str (ALOOKUP tbl) (K {}) S0 SUBSET fsem relI phi
Proof
  rpt gen_tac >> strip_tac >>
  fs[vc_fols_def, MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
  irule vc_sound >> rw[] >>
  qexistsl_tac [`n`, `cpost ct`, `cpre ct`] >> conj_tac
  >- (qpat_x_assum `!v. sholds _ _ (vc_main _ _ _ _ _)` mp_tac >>
      rw[sholds_vc_main, ftc_dom_univ])
  >- (irule pcc_conforms_norm >>
      rw[pcc_valid_def, norm_lk_def] >- rw[nf_norm] >>
      rename1 `ALOOKUP tbl m = SOME b` >>
      `MEM (m, b) tbl` by metis_tac[ALOOKUP_MEM] >>
      qpat_x_assum `!v y. MEM y tbl ==> _`
        (qspecl_then [`ARB`, `(m, b)`] mp_tac) >>
      rw[sholds_pcc_valid_fol])
QED

(* ------------------------------------------------------------------------ *)
(* In terms of folcompactness                                               *)
(* ------------------------------------------------------------------------ *)

(* satisfaction in the folcompactness model of M is truth in M under every
   valuation into the domain *)
Theorem satisfies_sholds:
  !M f. smodel2model M satisfies {sform2form f} <=>
        !v. (!x. v x IN M.SDom) ==> sholds M v f
Proof
  rw[satisfies_def, sholds_holds, valuation_def, smodel2model_def] >>
  EQ_TAC >> rw[] >>
  TRY (first_x_assum irule >> rw[] >> NO_TAC) >>
  first_x_assum (qspec_then `v o s2n` mp_tac) >>
  `v o s2n o n2s = v` by rw[FUN_EQ_THM, n2s_s2n] >>
  rw[] >> first_x_assum irule >> rw[]
QED

Theorem rec_model_univ_dom:
  (rec_model UNIV).SDom = UNIV
Proof
  rw[EXTENSION]
QED

(* End-to-end soundness, with the verification conditions translated to
   folcompactness formulas and checked in the translated model of M *)
Theorem vc_fols_sound_fol:
  !tbl ct n S0 phi relI.
    fv_f phi = [] /\
    (!f. MEM f (vc_fols tbl ct n S0 phi) ==>
         smodel2model (rec_model UNIV) satisfies {sform2form f}) ==>
    Str (ALOOKUP tbl) (K {}) S0 SUBSET fsem relI phi
Proof
  rpt strip_tac >> irule vc_fols_sound >> rw[] >>
  qexistsl_tac [`ct`, `n`] >> rpt strip_tac >> res_tac >>
  fs[satisfies_sholds, rec_model_univ_dom]
QED
