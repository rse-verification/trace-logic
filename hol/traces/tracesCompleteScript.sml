(* Relative completeness of the proof calculus (Theorem 5.7, Corollary 5.8),
   for programs whose calls are all declared and an oracle that answers
   yes for every valid entailment. *)

Theory tracesComplete
Ancestors
  pred_set list alist combin pair ott traces tracesSem tracesSos tracesSound
  tracesStf

val calc_rule = let
  val rules = CONJUNCTS calc_defs_rules |> map (SIMP_RULE std_ss [clause_name_def])
in fn n => List.nth (rules, n) end;

val [skip_rule, assign_rule, seq_rule, if_rule, unfold_rule, cons_rule,
     call_rule, ax_rule] = List.tabulate (8, calc_rule);

(* ------------------------------------------------------------------------ *)
(* Assumptions                                                              *)
(* ------------------------------------------------------------------------ *)

(* the entailment oracle answers yes for every valid entailment *)
Definition ent_complete_def:
  ent_complete relI (E:f -> f -> bool) =
    !f1 f2. fsem relI f1 SUBSET fsem relI f2 ==> E f1 f2
End

Theorem sem_ent_complete:
  !relI. ent_complete relI (sem_ent relI)
Proof
  rw[ent_complete_def, sem_ent_def]
QED

(* every procedure called in S is declared in the table *)
Definition calls_declared_def:
  (calls_declared tbl (S_seq S1 S2) =
     (calls_declared tbl S1 /\ calls_declared tbl S2)) /\
  (calls_declared tbl (S_ifelse b S1 S2) =
     (calls_declared tbl S1 /\ calls_declared tbl S2)) /\
  (calls_declared tbl (S_call m) = (ALOOKUP tbl m <> NONE)) /\
  (calls_declared tbl _ = T)
End

(* ... and so is every procedure called in a body of the table *)
Definition tbl_declared_def:
  tbl_declared tbl =
    !m body. ALOOKUP tbl m = SOME body ==> calls_declared tbl body
End

(* ------------------------------------------------------------------------ *)
(* The antecedent Gamma_D of Theorem 5.7                                    *)
(* ------------------------------------------------------------------------ *)

(* Gamma_D = { Y_m : phi_m | m in D }, with phi_m = mu X_m. stf({m}, S_m) *)
Definition stf_ctx_def:
  stf_ctx tbl D =
    {(Y, f) | Y IN D /\
              ?body. ALOOKUP tbl Y = SOME body /\ f = f_mu Y (stf tbl [Y] body)}
End

Theorem stf_ctx_empty:
  !tbl. stf_ctx tbl {} = {}
Proof
  rw[stf_ctx_def, EXTENSION]
QED

Theorem G_dom_stf_ctx:
  !tbl D. (!m. m IN D ==> ALOOKUP tbl m <> NONE) ==> G_dom (stf_ctx tbl D) = D
Proof
  rw[G_dom_def, stf_ctx_def, EXTENSION, EXISTS_PROD] >>
  Cases_on `ALOOKUP tbl x` >> metis_tac[]
QED

Theorem stf_ctx_insert:
  !tbl D m body. ALOOKUP tbl m = SOME body ==>
    stf_ctx tbl (m INSERT D) =
    (m, f_mu m (stf tbl [m] body)) INSERT stf_ctx tbl D
Proof
  rw[stf_ctx_def, EXTENSION, FORALL_PROD] >> metis_tac[optionTheory.SOME_11]
QED

Theorem subst_calls_empty:
  !S0. subst_calls {} S0 = S0
Proof
  Induct >> rw[subst_calls_def]
QED

(* ------------------------------------------------------------------------ *)
(* Entailments used by rule (Cons)                                          *)
(* ------------------------------------------------------------------------ *)

Theorem chop_cons:
  !A B t. t IN chop A B ==> ?s r. t = s::r
Proof
  rw[chop_def] >> Cases_on `l1` >> rw[]
QED

(* the two premises of rule (If) when the formula has the shape produced by
   stf for conditionals: (b /\ Id ^ F1) \/ (~b /\ Id ^ F2) *)
Theorem if_then_ent:
  !relI b F1 F2.
    sem_ent relI (f_chop (f_rel R_Id) F1)
      (f_or (f_state (p_b (b_neg b)))
            (f_or (f_and (f_state (p_b b)) (f_chop (f_rel R_Id) F1))
                  (f_and (f_state (p_b (b_neg b))) (f_chop (f_rel R_Id) F2))))
Proof
  rw[sem_ent_def, fsem_eqs, SUBSET_DEF, p_sem_def, b_eval_def] >>
  imp_res_tac chop_cons >> rw[] >> metis_tac[]
QED

Theorem if_else_ent:
  !relI b F1 F2.
    sem_ent relI (f_chop (f_rel R_Id) F2)
      (f_or (f_state (p_b b))
            (f_or (f_and (f_state (p_b b)) (f_chop (f_rel R_Id) F1))
                  (f_and (f_state (p_b (b_neg b))) (f_chop (f_rel R_Id) F2))))
Proof
  rw[sem_ent_def, fsem_eqs, SUBSET_DEF, p_sem_def, b_eval_def] >>
  imp_res_tac chop_cons >> rw[] >> metis_tac[]
QED

(* phi_m and stf(S_m) have the same semantics, Str[[S_m]] *)
Theorem fsem_stf_mu:
  !tbl m body relI.
    tbl_var_free tbl /\ ALOOKUP tbl m = SOME body ==>
    fsem relI (f_mu m (stf tbl [m] body)) = fsem relI (stf tbl [] body)
Proof
  rw[] >> `var_free body` by metis_tac[tbl_var_free_def] >>
  `fsem relI (stf tbl [] body) = Str (ALOOKUP tbl) (K {}) body`
    by metis_tac[stf_Str] >>
  rw[fsem_def] >>
  `Str (ALOOKUP tbl) (K {}) body = Str (ovr (set []) (ALOOKUP tbl)) (K {}) body`
    by rw[ovr_empty] >>
  pop_assum SUBST1_TAC >> irule stf_mu_sem >> rw[]
QED

(* ------------------------------------------------------------------------ *)
(* Theorem 5.7, generalized to any set D of declared procedures             *)
(* ------------------------------------------------------------------------ *)

Theorem CARD_DIFF_INSERT_LESS:
  !A D m. FINITE A /\ m IN A /\ m NOTIN D ==>
          CARD (A DIFF (m INSERT D)) < CARD (A DIFF D)
Proof
  rw[] >> irule CARD_PSUBSET >> rw[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
  metis_tac[]
QED

Theorem ALOOKUP_MEM_FST:
  !tbl m body. ALOOKUP tbl m = SOME body ==> MEM m (MAP FST tbl)
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >> rw[MEM_MAP] >> qexists_tac `(m,body)` >>
  rw[]
QED

(* Gamma_D |- S[skip;Y_m/m()]_{m in D} : stf(S). The induction is on the
   number of declared procedures outside D, then on S. In the call case for
   m outside D, rule (Call) adds Y_m : phi_m, the induction hypothesis
   gives the body S_m the formula stf(S_m), and rule (Cons) turns it into
   phi_m. Rule (Unfold) is not needed. *)
Theorem stf_derivable_ctx:
  !n tbl E relI D S0.
    CARD (set (MAP FST tbl) DIFF D) = n /\
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    (!m. m IN D ==> ALOOKUP tbl m <> NONE) /\
    var_free S0 /\ calls_declared tbl S0 ==>
    calc tbl E (stf_ctx tbl D) (subst_calls D S0) (stf tbl [] S0)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  ntac 2 (pop_assum mp_tac) >> qid_spec_tac `S0` >> Induct >>
  rw[var_free_def, calls_declared_def, subst_calls_def, stf_def]
  >- irule skip_rule
  >- irule assign_rule
  >- (irule seq_rule >> rw[])
  >- (irule if_rule >> conj_tac >> match_mp_tac cons_rule
      >- (qexists_tac `f_chop (f_rel R_Id) (stf tbl [] S0)` >>
          conj_tac
          >- (irule seq_rule >> rw[] >> irule skip_rule) >>
          fs[ent_complete_def] >> first_x_assum irule >>
          metis_tac[if_then_ent, sem_ent_def])
      >- (qexists_tac `f_chop (f_rel R_Id) (stf tbl [] S0')` >>
          conj_tac
          >- (irule seq_rule >> rw[] >> irule skip_rule) >>
          fs[ent_complete_def] >> first_x_assum irule >>
          metis_tac[if_else_ent, sem_ent_def])) >>
  (* calls *)
  qmatch_goalsub_rename_tac `ALOOKUP tbl m` >>
  Cases_on `ALOOKUP tbl m` >> fs[] >> TRY (res_tac >> fs[] >> NO_TAC) >>
  rename1 `ALOOKUP tbl m = SOME body`
  >- ((* m in D: skip;Y_m : Id ^ phi_m by (Seq), (Skip) and (Ax) *)
      irule seq_rule >> conj_tac >- irule skip_rule >>
      irule ax_rule >> rw[stf_ctx_def]) >>
  (* m not in D: rule (Call) with contract phi_m *)
  irule call_rule >> simp[] >>
  `G_dom (stf_ctx tbl D) = D` by metis_tac[G_dom_stf_ctx] >>
  `(m, f_mu m (stf tbl [m] body)) INSERT stf_ctx tbl D =
   stf_ctx tbl (m INSERT D)` by metis_tac[stf_ctx_insert] >>
  `G_dom (stf_ctx tbl (m INSERT D)) = m INSERT D`
    by (irule G_dom_stf_ctx >> rw[] >> fs[]) >>
  simp[] >>
  match_mp_tac cons_rule >> qexists_tac `stf tbl [] body` >> conj_tac
  >- (first_x_assum (qspec_then `CARD (set (MAP FST tbl) DIFF (m INSERT D))`
                       mp_tac) >>
      impl_tac
      >- (rw[] >> irule CARD_DIFF_INSERT_LESS >> rw[] >>
          metis_tac[ALOOKUP_MEM_FST]) >>
      disch_then irule >> rw[] >> fs[] >>
      metis_tac[tbl_declared_def, tbl_var_free_def]) >>
  fs[ent_complete_def] >> first_x_assum irule >>
  metis_tac[fsem_stf_mu, SUBSET_REFL]
QED

(* Theorem 5.7 as stated in the paper: Gamma contains phi_m for all declared
   procedures m *)
Theorem stf_derivable_all:
  !tbl E relI S0.
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    var_free S0 /\ calls_declared tbl S0 ==>
    calc tbl E (stf_ctx tbl (set (MAP FST tbl)))
         (subst_calls (set (MAP FST tbl)) S0) (stf tbl [] S0)
Proof
  rw[] >> irule stf_derivable_ctx >> rw[ALOOKUP_NONE] >> metis_tac[]
QED

(* ... and with empty antecedent: |- S : stf(S) *)
Theorem stf_derivable:
  !tbl E relI S0.
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    var_free S0 /\ calls_declared tbl S0 ==>
    calc tbl E {} S0 (stf tbl [] S0)
Proof
  rw[] >>
  `calc tbl E (stf_ctx tbl {}) (subst_calls {} S0) (stf tbl [] S0)`
    suffices_by rw[stf_ctx_empty, subst_calls_empty] >>
  irule stf_derivable_ctx >> rw[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------ *)
(* Corollary 5.8                                                            *)
(* ------------------------------------------------------------------------ *)

(* relative completeness: every valid judgment S : phi is derivable *)
Theorem calc_complete:
  !tbl E relI S0 f.
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    var_free S0 /\ calls_declared tbl S0 /\
    valid relI (ALOOKUP tbl) {} S0 f ==>
    calc tbl E {} S0 f
Proof
  rw[] >> match_mp_tac cons_rule >> qexists_tac `stf tbl [] S0` >> conj_tac
  >- (irule stf_derivable >> metis_tac[]) >>
  fs[ent_complete_def] >> metis_tac[stf_strongest]
QED

(* ... with validity with respect to the SOS *)
Theorem calc_complete_sos:
  !tbl E relI S0 f.
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    var_free S0 /\ calls_declared tbl S0 /\
    Ssos tbl S0 SUBSET fsem relI f ==>
    calc tbl E {} S0 f
Proof
  rw[] >> irule calc_complete >> rw[] >>
  metis_tac[stf_strongest, stf_Ssos]
QED

(* soundness and relative completeness, with semantic entailment as oracle *)
Theorem calc_sound_complete:
  !tbl relI S0 f.
    tbl_var_free tbl /\ tbl_declared tbl /\
    var_free S0 /\ calls_declared tbl S0 ==>
    (calc tbl (sem_ent relI) {} S0 f <=> valid relI (ALOOKUP tbl) {} S0 f)
Proof
  rw[EQ_IMP_THM]
  >- metis_tac[calc_sound, sem_ent_sound]
  >- metis_tac[calc_complete, sem_ent_complete]
QED

Theorem calc_sound_complete_sos:
  !tbl relI S0 f.
    tbl_var_free tbl /\ tbl_declared tbl /\
    var_free S0 /\ calls_declared tbl S0 ==>
    (calc tbl (sem_ent relI) {} S0 f <=> Ssos tbl S0 SUBSET fsem relI f)
Proof
  rw[calc_sound_complete] >> metis_tac[stf_strongest, stf_Ssos]
QED

(* ------------------------------------------------------------------------ *)
(* Theorem 5.7 along the proof of Appendix A.4                              *)
(* ------------------------------------------------------------------------ *)

(* In the call case for m outside Gamma, the paper applies (Call), then
   (Unfold) on phi_m, and then proceeds by the statement rules on S_m and
   stf({m}, S_m)[phi_m/X_m], up to the calls in S_m. *)

(* stf(X, S) has free variables only in X *)
Theorem stf_fv:
  !tbl X S0.
    tbl_var_free tbl /\ tbl_declared tbl /\ var_free S0 /\
    calls_declared tbl S0 ==>
    !Y. MEM Y (fv_f (stf tbl X S0)) ==> MEM Y X
Proof
  ho_match_mp_tac stf_ind >>
  rw[stf_def, fv_f_def, var_free_def, calls_declared_def] >>
  TRY (metis_tac[]) >>
  Cases_on `ALOOKUP tbl m` >> fs[] >>
  Cases_on `MEM m X` >> fs[fv_f_def, list_minus_thm] >>
  metis_tac[tbl_var_free_def, tbl_declared_def, MEM]
QED

(* closedness, the side condition of (Unfold) *)
Theorem stf_mu_closed:
  !tbl p bp.
    tbl_var_free tbl /\ tbl_declared tbl /\ ALOOKUP tbl p = SOME bp ==>
    fv_f (f_mu p (stf tbl [p] bp)) = []
Proof
  rw[fv_f_def] >>
  `!Y. MEM Y (fv_f (stf tbl [p] bp)) ==> MEM Y [p]`
    by metis_tac[stf_fv, tbl_var_free_def, tbl_declared_def] >>
  Cases_on `list_minus (fv_f (stf tbl [p] bp)) [p]` >> rw[] >>
  `MEM h (list_minus (fv_f (stf tbl [p] bp)) [p])` by fs[] >>
  fs[list_minus_thm] >> res_tac >> fs[]
QED

Theorem subst_f_Id_chop:
  !g X f. subst_f g X (f_chop (f_rel R_Id) f) =
          f_chop (f_rel R_Id) (subst_f g X f)
Proof
  rw[subst_f_def]
QED

Theorem fsem_Id_chop_mono:
  !relI f1 f2. fsem relI f1 SUBSET fsem relI f2 ==>
    fsem relI (f_chop (f_rel R_Id) f1) SUBSET fsem relI (f_chop (f_rel R_Id) f2)
Proof
  rw[fsem_eqs] >> irule chop_mono >> rw[]
QED

(* the (Cons) step at a call of n in S_m: phi_n entails the formula that
   unfolding phi_m gives the call (stf_unfold_mu) *)
Theorem unfold_mu_ent:
  !tbl p bp n bn relI.
    tbl_var_free tbl /\ ALOOKUP tbl p = SOME bp /\ ALOOKUP tbl n = SOME bn /\
    n <> p /\ fv_f (f_mu p (stf tbl [p] bp)) = [] ==>
    fsem relI (f_mu n (stf tbl [n] bn)) SUBSET
    fsem relI (subst_f (f_mu p (stf tbl [p] bp)) p (f_mu n (stf tbl [n; p] bn)))
Proof
  rw[] >> qspecl_then [`tbl`, `p`, `bp`, `n`, `bn`, `relI`] mp_tac stf_unfold_mu >>
  rw[]
QED

(* The statement rules on S and stf({p}, S)[phi_p/X_p], for p in D. A call
   of n <> p is closed by (Cons) from phi_n: with (Ax) if n is in D, and
   otherwise from n() : stf(n()), which is the hypothesis on calls. *)
Theorem stf_walk:
  !tbl E relI D p bp S0.
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    (!n. n IN D ==> ALOOKUP tbl n <> NONE) /\
    p IN D /\ ALOOKUP tbl p = SOME bp /\
    (!n. n NOTIN D /\ ALOOKUP tbl n <> NONE ==>
         calc tbl E (stf_ctx tbl D) (S_call n) (stf tbl [] (S_call n))) /\
    var_free S0 /\ calls_declared tbl S0 ==>
    calc tbl E (stf_ctx tbl D) (subst_calls D S0)
      (subst_f (f_mu p (stf tbl [p] bp)) p (stf tbl [p] S0))
Proof
  rpt gen_tac >> strip_tac >>
  `fv_f (f_mu p (stf tbl [p] bp)) = []` by metis_tac[stf_mu_closed] >>
  qabbrev_tac `phi = f_mu p (stf tbl [p] bp)` >>
  ntac 4 (pop_assum mp_tac) >> qid_spec_tac `S0` >> Induct >>
  rw[var_free_def, calls_declared_def]
  >- (rw[subst_calls_def, stf_def, subst_f_def] >> irule skip_rule)
  >- (rw[subst_calls_def, stf_def, subst_f_def] >> irule assign_rule)
  >- (rw[subst_calls_def, stf_def, subst_f_def] >> irule seq_rule >> rw[])
  >- (simp[subst_calls_def, stf_def, subst_f_def] >>
      irule if_rule >> conj_tac >> match_mp_tac cons_rule
      >- (qexists_tac `f_chop (f_rel R_Id) (subst_f phi p (stf tbl [p] S0))` >>
          conj_tac
          >- (irule seq_rule >> rw[] >> irule skip_rule) >>
          fs[ent_complete_def] >> first_x_assum irule >>
          metis_tac[if_then_ent, sem_ent_def])
      >- (qexists_tac `f_chop (f_rel R_Id) (subst_f phi p (stf tbl [p] S0'))` >>
          conj_tac
          >- (irule seq_rule >> rw[] >> irule skip_rule) >>
          fs[ent_complete_def] >> first_x_assum irule >>
          metis_tac[if_else_ent, sem_ent_def])) >>
  (* calls *)
  qmatch_goalsub_rename_tac `stf tbl [p] (S_call n)` >>
  Cases_on `ALOOKUP tbl n` >> fs[] >> rename1 `ALOOKUP tbl n = SOME bn` >>
  Cases_on `n = p`
  >- ((* the recursive call: skip;Y_p : Id ^ phi_p by (Ax), no (Cons) *)
      fs[] >> rw[subst_calls_def, stf_def, subst_f_def] >>
      irule seq_rule >> conj_tac >- irule skip_rule >>
      irule ax_rule >> rw[stf_ctx_def, Abbr `phi`]) >>
  simp[stf_def, subst_f_Id_chop] >>
  Cases_on `n IN D` >> simp[subst_calls_def]
  >- ((* n in D: (Cons) from Y_n : phi_n *)
      irule seq_rule >> conj_tac >- irule skip_rule >>
      match_mp_tac cons_rule >> qexists_tac `f_mu n (stf tbl [n] bn)` >>
      conj_tac >- (irule ax_rule >> rw[stf_ctx_def]) >>
      fs[ent_complete_def] >> first_x_assum irule >>
      qunabbrev_tac `phi` >> irule unfold_mu_ent >> rw[]) >>
  (* n not in D: (Cons) from n() : stf(n()) *)
  match_mp_tac cons_rule >> qexists_tac `stf tbl [] (S_call n)` >>
  conj_tac >- (first_x_assum irule >> rw[]) >>
  fs[ent_complete_def] >> first_x_assum irule >>
  simp[stf_def] >> irule fsem_Id_chop_mono >>
  qunabbrev_tac `phi` >> irule unfold_mu_ent >> rw[]
QED

(* Theorem 5.7, generalized as stf_derivable_ctx, with the proof of the
   paper: in the call case for m outside D, (Call), (Unfold) and stf_walk *)
Theorem stf_derivable_ctx_unfold:
  !n tbl E relI D S0.
    CARD (set (MAP FST tbl) DIFF D) = n /\
    ent_complete relI E /\ tbl_var_free tbl /\ tbl_declared tbl /\
    (!m. m IN D ==> ALOOKUP tbl m <> NONE) /\
    var_free S0 /\ calls_declared tbl S0 ==>
    calc tbl E (stf_ctx tbl D) (subst_calls D S0) (stf tbl [] S0)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  ntac 2 (pop_assum mp_tac) >> qid_spec_tac `S0` >> Induct >>
  rw[var_free_def, calls_declared_def, subst_calls_def, stf_def]
  >- irule skip_rule
  >- irule assign_rule
  >- (irule seq_rule >> rw[])
  >- (irule if_rule >> conj_tac >> match_mp_tac cons_rule
      >- (qexists_tac `f_chop (f_rel R_Id) (stf tbl [] S0)` >>
          conj_tac
          >- (irule seq_rule >> rw[] >> irule skip_rule) >>
          fs[ent_complete_def] >> first_x_assum irule >>
          metis_tac[if_then_ent, sem_ent_def])
      >- (qexists_tac `f_chop (f_rel R_Id) (stf tbl [] S0')` >>
          conj_tac
          >- (irule seq_rule >> rw[] >> irule skip_rule) >>
          fs[ent_complete_def] >> first_x_assum irule >>
          metis_tac[if_else_ent, sem_ent_def])) >>
  (* calls *)
  qmatch_goalsub_rename_tac `ALOOKUP tbl m` >>
  Cases_on `ALOOKUP tbl m` >> fs[] >> TRY (res_tac >> fs[] >> NO_TAC) >>
  rename1 `ALOOKUP tbl m = SOME body`
  >- (irule seq_rule >> conj_tac >- irule skip_rule >>
      irule ax_rule >> rw[stf_ctx_def]) >>
  (* m not in D: (Call) with contract phi_m, then (Unfold) *)
  irule call_rule >> simp[] >>
  `G_dom (stf_ctx tbl D) = D` by metis_tac[G_dom_stf_ctx] >>
  `(m, f_mu m (stf tbl [m] body)) INSERT stf_ctx tbl D =
   stf_ctx tbl (m INSERT D)` by metis_tac[stf_ctx_insert] >>
  `G_dom (stf_ctx tbl (m INSERT D)) = m INSERT D`
    by (irule G_dom_stf_ctx >> rw[] >> fs[]) >>
  simp[] >>
  match_mp_tac unfold_rule >> conj_tac
  >- (irule stf_mu_closed >> rw[]) >>
  (* the calls outside m INSERT D, by the induction hypothesis *)
  `!n. n NOTIN m INSERT D /\ ALOOKUP tbl n <> NONE ==>
       calc tbl E (stf_ctx tbl (m INSERT D)) (S_call n)
            (stf tbl [] (S_call n))`
    by (rpt strip_tac >>
        first_x_assum (qspec_then `CARD (set (MAP FST tbl) DIFF (m INSERT D))`
                         mp_tac) >>
        impl_tac
        >- (rw[] >> irule CARD_DIFF_INSERT_LESS >> rw[] >>
            metis_tac[ALOOKUP_MEM_FST]) >>
        disch_then (qspecl_then [`tbl`, `E`, `relI`, `m INSERT D`, `S_call n`]
                      mp_tac) >>
        `subst_calls (m INSERT D) (S_call n) = S_call n`
          by fs[subst_calls_def] >>
        simp[] >> disch_then irule >>
        fs[var_free_def, calls_declared_def] >> rw[] >> fs[]) >>
  irule stf_walk >> rw[] >> fs[] >>
  metis_tac[tbl_declared_def, tbl_var_free_def]
QED
