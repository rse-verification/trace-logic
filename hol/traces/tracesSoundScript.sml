(* Soundness of the proof calculus (Theorem 5.6), with respect to a corrected
   version of Definition 5.4. *)

Theory tracesSound
Ancestors
  pred_set list alist combin pair ott traces tracesSem tracesSos

(* ------------------------------------------------------------------------ *)
(* Validity of judgments and sequents                                       *)
(* ------------------------------------------------------------------------ *)

(* Procedures m with Y_m = m in the domain D of the antecedent are
   interpreted as their continuation skip;Y_m, i.e., as #I(Y_m); the other
   procedures are interpreted by the least fixed point relative to these. *)
Definition ovr_def:
  ovr D (lk:lookup) = \m. if m IN D then SOME (S_var m) else lk m
End

Theorem ovr_empty:
  !lk. ovr {} lk = lk
Proof
  rw[ovr_def, FUN_EQ_THM]
QED

(* all judgments Y : phi in G are valid in the interpretation iv *)
Definition G_holds_def:
  G_holds relI (G:G) iv = !Y f. (Y,f) IN G ==> iv Y SUBSET fsem relI f
End

(* corrected Definition 5.4: G |= S : phi *)
Definition valid_def:
  valid relI lk G S0 f =
    !iv. G_holds relI G iv ==>
         Str (ovr (G_dom G) lk) iv S0 SUBSET fsem relI f
End

(* the entailment oracle only answers yes for valid entailments *)
Definition ent_sound_def:
  ent_sound relI (E:f -> f -> bool) =
    !f1 f2. E f1 f2 ==> fsem relI f1 SUBSET fsem relI f2
End

(* semantic entailment, which is trivially a sound oracle *)
Definition sem_ent_def:
  sem_ent relI f1 f2 = (fsem relI f1 SUBSET fsem relI f2)
End

Theorem sem_ent_sound:
  !relI. ent_sound relI (sem_ent relI)
Proof
  rw[ent_sound_def, sem_ent_def]
QED

Theorem G_dom_insert:
  !Y f G. G_dom ((Y,f) INSERT G) = Y INSERT G_dom G
Proof
  rw[G_dom_def]
QED

Theorem G_holds_insert:
  !relI Y f G iv.
    G_holds relI ((Y,f) INSERT G) iv <=>
    iv Y SUBSET fsem relI f /\ G_holds relI G iv
Proof
  rw[G_holds_def] >> metis_tac[]
QED

Theorem fsem_eqs:
  (!relI p. fsem relI (f_state p) = {t | ?s r. t = s::r /\ p_sem p s}) /\
  (!relI R. fsem relI (f_rel R) = {t | ?s s'. t = [s;s'] /\ R_sem relI R s s'}) /\
  (!relI f1 f2. fsem relI (f_and f1 f2) = fsem relI f1 INTER fsem relI f2) /\
  (!relI f1 f2. fsem relI (f_or f1 f2) = fsem relI f1 UNION fsem relI f2) /\
  (!relI f1 f2. fsem relI (f_chop f1 f2) = chop (fsem relI f1) (fsem relI f2))
Proof
  rw[fsem_def, f_sem_def]
QED

(* ------------------------------------------------------------------------ *)
(* Local soundness of the rules                                             *)
(* ------------------------------------------------------------------------ *)

Theorem skip_sound:
  !relI lk G. valid relI lk G S_skip (f_rel R_Id)
Proof
  rw[valid_def, Str_def, Str0_def, fsem_eqs, R_sem_def, SUBSET_DEF]
QED

Theorem assign_sound:
  !relI lk G x a. valid relI lk G (S_assign x a) (f_rel (R_Sb a x))
Proof
  rw[valid_def, Str_def, Str0_def, fsem_eqs, R_sem_def, SUBSET_DEF]
QED

Theorem seq_sound:
  !relI lk G S1 S2 f1 f2.
    valid relI lk G S1 f1 /\ valid relI lk G S2 f2 ==>
    valid relI lk G (S_seq S1 S2) (f_chop f1 f2)
Proof
  rw[valid_def, Str_def, Str0_def, fsem_eqs] >> metis_tac[chop_mono]
QED

(* Proposition A.9 is folded into this proof *)
Theorem if_sound:
  !relI lk G b S1 S2 f.
    valid relI lk G (S_seq S_skip S1) (f_or (f_state (p_b (b_neg b))) f) /\
    valid relI lk G (S_seq S_skip S2) (f_or (f_state (p_b b)) f) ==>
    valid relI lk G (S_ifelse b S1 S2) f
Proof
  rw[valid_def] >>
  rpt (first_x_assum (qspec_then `iv` mp_tac)) >> rw[] >>
  fs[Str_def, Str0_def, Str0_seq_skip, fsem_eqs, SUBSET_DEF, restrict_def,
     dup_def, p_sem_def, b_eval_def] >>
  metis_tac[CONS_11]
QED

Theorem unfold_sound:
  !relI lk G S0 X f.
    fv_f (f_mu X f) = [] /\ valid relI lk G S0 (subst_f (f_mu X f) X f) ==>
    valid relI lk G S0 (f_mu X f)
Proof
  rw[valid_def] >> metis_tac[fsem_unfold]
QED

Theorem cons_sound:
  !relI lk G S0 f f'.
    valid relI lk G S0 f' /\ fsem relI f' SUBSET fsem relI f ==>
    valid relI lk G S0 f
Proof
  rw[valid_def] >> metis_tac[SUBSET_TRANS]
QED

Theorem ax_sound:
  !relI lk G Y f. (Y,f) IN G ==> valid relI lk G (S_var Y) f
Proof
  rw[valid_def, G_holds_def, Str_def, Str0_def]
QED

Theorem weak_sound:
  !relI lk G G' S0 f.
    valid relI lk G S0 f /\ G SUBSET G' /\ G_dom G = G_dom G' ==>
    valid relI lk G' S0 f
Proof
  rw[valid_def] >>
  `G_holds relI G iv` by (fs[G_holds_def, SUBSET_DEF] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem cut_sound:
  !relI lk G S0 f Y f'.
    Y IN G_dom G /\ valid relI lk G (S_var Y) f' /\
    valid relI lk ((Y,f') INSERT G) S0 f ==>
    valid relI lk G S0 f
Proof
  rw[valid_def, G_dom_insert, G_holds_insert] >>
  `Y INSERT G_dom G = G_dom G` by metis_tac[ABSORPTION] >>
  fs[Str_def, Str0_def] >> metis_tac[]
QED

Theorem andR_sound:
  !relI lk G S0 f1 f2.
    valid relI lk G S0 f1 /\ valid relI lk G S0 f2 ==>
    valid relI lk G S0 (f_and f1 f2)
Proof
  rw[valid_def, fsem_eqs, SUBSET_INTER]
QED

Theorem andL_sound:
  !relI lk G Y f1 f2 S0 f.
    valid relI lk ((Y,f2) INSERT (Y,f1) INSERT G) S0 f ==>
    valid relI lk ((Y,f_and f1 f2) INSERT G) S0 f
Proof
  rw[valid_def, G_dom_insert, G_holds_insert, fsem_eqs, SUBSET_INTER] >>
  fs[INSERT_INSERT]
QED

Theorem consL_sound:
  !relI lk G Y f f' S0 f''.
    valid relI lk ((Y,f) INSERT G) S0 f'' /\ fsem relI f' SUBSET fsem relI f ==>
    valid relI lk ((Y,f') INSERT G) S0 f''
Proof
  rw[valid_def, G_dom_insert, G_holds_insert] >> metis_tac[SUBSET_TRANS]
QED

(* ------------------------------------------------------------------------ *)
(* The (Call) rule                                                          *)
(* ------------------------------------------------------------------------ *)

Theorem rho0_ovr:
  !D lk iv n. n IN D ==> rho0 (ovr D lk) iv n = dup (iv n)
Proof
  rw[] >>
  `rho0 (ovr D lk) iv n = H (ovr D lk) iv (rho0 (ovr D lk) iv) n`
    by metis_tac[rho0_fixpoint] >>
  rw[H_def, ovr_def, Str0_def]
QED

(* the substitution of skip;Y_m for m() in rule (Call) preserves the
   semantics once the procedures are interpreted as their continuations *)
Theorem subst_calls_Str0:
  !S0 ms rho iv. (!n. n IN ms ==> rho n = dup (iv n)) ==>
                 Str0 rho iv (subst_calls ms S0) = Str0 rho iv S0
Proof
  Induct >> rw[subst_calls_def, Str0_def, Str0_seq_skip]
QED

(* fixed-point induction for rule (Call), done on the whole system of
   procedures at once (instead of appealing to Bekic's principle) *)
Theorem call_fixpoint_induction:
  !lk D m body iv g.
    m NOTIN D /\ lk m = SOME body /\
    (!n b. lk n = SOME b ==> var_free b) /\
    Str0 (rho0 (ovr (m INSERT D) lk) ((m =+ g) iv)) iv body SUBSET g ==>
    rho0 (ovr D lk) iv m SUBSET dup g
Proof
  rw[] >>
  qabbrev_tac `r = rho0 (ovr (m INSERT D) lk) ((m =+ g) iv)` >>
  `!n. r n = H (ovr (m INSERT D) lk) ((m =+ g) iv) r n`
    by metis_tac[rho0_fixpoint] >>
  `ileq (H (ovr D lk) iv r) r`
    by (simp[ileq_def] >> qx_gen_tac `n` >>
        qpat_x_assum `!n. r n = _` (qspec_then `n` SUBST1_TAC) >>
        Cases_on `n = m`
        >- (fs[H_def, ovr_def, Str0_def, APPLY_UPDATE_THM] >>
            irule dup_mono >> rw[]) >>
        Cases_on `n IN D`
        >- fs[H_def, ovr_def, Str0_def, APPLY_UPDATE_THM] >>
        fs[H_def, ovr_def] >> CASE_TAC >> rw[] >>
        `var_free x` by metis_tac[] >>
        metis_tac[Str0_var_free, SUBSET_REFL, dup_mono]) >>
  `ileq (rho0 (ovr D lk) iv) r` by metis_tac[rho0_least] >>
  `r m = dup ((m =+ g) iv m)`
    by (qunabbrev_tac `r` >> irule rho0_ovr >> rw[]) >>
  fs[ileq_def, APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem call_sound:
  !relI tbl G m body f.
    tbl_var_free tbl /\ ALOOKUP tbl m = SOME body /\ m NOTIN G_dom G /\
    valid relI (ALOOKUP tbl) ((m,f) INSERT G)
      (subst_calls (G_dom ((m,f) INSERT G)) body) f ==>
    valid relI (ALOOKUP tbl) G (S_call m) (f_chop (f_rel R_Id) f)
Proof
  rw[valid_def, fsem_Id_chop, G_dom_insert] >>
  rw[Str_def, Str0_def] >>
  irule call_fixpoint_induction >>
  fs[tbl_var_free_def] >> rw[] >- metis_tac[] >>
  qabbrev_tac `iv' = (m =+ fsem relI f) iv` >>
  `G_holds relI ((m,f) INSERT G) iv'`
    by (rw[G_holds_insert, Abbr `iv'`, APPLY_UPDATE_THM] >>
        fs[G_holds_def, G_dom_def, APPLY_UPDATE_THM] >> rw[] >>
        metis_tac[IN_IMAGE, FST]) >>
  first_x_assum drule >> rw[Str_def] >>
  `!n. n IN m INSERT G_dom G ==>
       rho0 (ovr (m INSERT G_dom G) (ALOOKUP tbl)) iv' n = dup (iv' n)`
    by metis_tac[rho0_ovr] >>
  qabbrev_tac `r = rho0 (ovr (m INSERT G_dom G) (ALOOKUP tbl)) iv'` >>
  `Str0 r iv' (subst_calls (m INSERT G_dom G) body) = Str0 r iv' body`
    by (irule subst_calls_Str0 >> metis_tac[IN_INSERT]) >>
  `Str0 r iv' body = Str0 r iv body` by metis_tac[Str0_var_free] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------ *)
(* Soundness                                                                *)
(* ------------------------------------------------------------------------ *)

(* every derivable sequent is valid (in the corrected sense) *)
Theorem calc_sound:
  !tbl E G S0 f.
    calc tbl E G S0 f ==>
    !relI. ent_sound relI E /\ tbl_var_free tbl ==>
           valid relI (ALOOKUP tbl) G S0 f
Proof
  ho_match_mp_tac calc_defs_ind >> rw[clause_name_def] >>
  fs[ent_sound_def] >>
  metis_tac[skip_sound, assign_sound, seq_sound, if_sound, unfold_sound,
            cons_sound, call_sound, ax_sound, weak_sound, cut_sound,
            andR_sound, andL_sound, consL_sound]
QED

(* Theorem 5.6 for sequents with empty antecedent, as used in the paper:
   a derivable judgment S : phi is valid in every interpretation of the
   statement variables *)
Theorem calc_sound_empty:
  !tbl E relI S0 f iv.
    ent_sound relI E /\ tbl_var_free tbl /\ calc tbl E {} S0 f ==>
    Str (ALOOKUP tbl) iv S0 SUBSET fsem relI f
Proof
  rw[] >> drule calc_sound >> rw[] >> first_x_assum drule_all >>
  rw[valid_def, G_holds_def, G_dom_def, ovr_empty]
QED

(* ... and, via Theorem 3.2, every SOS trace of a statement without
   statement variables satisfies the derived formula *)
Theorem calc_sound_sos:
  !tbl E relI S0 f.
    ent_sound relI E /\ tbl_var_free tbl /\ var_free S0 /\
    calc tbl E {} S0 f ==>
    Ssos tbl S0 SUBSET fsem relI f
Proof
  metis_tac[calc_sound_empty, Str_eq_Ssos]
QED

(* ------------------------------------------------------------------------ *)
(* Definition 5.4 as stated in the paper does not make every derivable      *)
(* sequent valid when the antecedent is non-empty                           *)
(* ------------------------------------------------------------------------ *)

Definition valid_orig_def:
  valid_orig relI lk G S0 f =
    !iv. G_holds relI G iv ==> Str lk iv S0 SUBSET fsem relI f
End

Theorem valid_orig_empty:
  !relI lk S0 f. valid_orig relI lk {} S0 f <=> valid relI lk {} S0 f
Proof
  rw[valid_orig_def, valid_def, G_dom_def, ovr_empty]
QED

val calc_rule = let
  val rules = CONJUNCTS calc_defs_rules |> map (SIMP_RULE std_ss [clause_name_def])
in fn n => List.nth (rules, n) end;

(* T = { m {m1()}, m1 {skip} }, Gamma = { Y_m1 : false } *)
Theorem original_validity_counterexample:
  tbl_var_free [("m", S_call "m1"); ("m1", S_skip)] /\
  calc [("m", S_call "m1"); ("m1", S_skip)] (\f1 f2. F)
       {("m1", f_state (p_b b_false))}
       (S_call "m")
       (f_chop (f_rel R_Id) (f_chop (f_rel R_Id) (f_state (p_b b_false)))) /\
  !relI. ~valid_orig relI (ALOOKUP [("m", S_call "m1"); ("m1", S_skip)])
           {("m1", f_state (p_b b_false))} (S_call "m")
           (f_chop (f_rel R_Id) (f_chop (f_rel R_Id) (f_state (p_b b_false))))
Proof
  rpt conj_tac
  >- (rw[tbl_var_free_def, ALOOKUP_def] >>
      pop_assum mp_tac >> rw[] >> rw[var_free_def])
  >- (irule (calc_rule 6) >> rw[ALOOKUP_def, G_dom_def, subst_calls_def] >>
      irule (calc_rule 2) >> conj_tac
      >- irule (calc_rule 0)
      >- (irule (calc_rule 7) >> rw[]))
  >- (rw[valid_orig_def] >> qexists_tac `K {}` >>
      `Str (ALOOKUP [("m", S_call "m1"); ("m1", S_skip)]) (K {}) (S_call "m") =
       dup (Str (ALOOKUP [("m", S_call "m1"); ("m1", S_skip)]) (K {}) (S_call "m1"))`
        by (irule Str_call >> rw[ALOOKUP_def]) >>
      `Str (ALOOKUP [("m", S_call "m1"); ("m1", S_skip)]) (K {}) (S_call "m1") =
       dup (Str (ALOOKUP [("m", S_call "m1"); ("m1", S_skip)]) (K {}) S_skip)`
        by (irule Str_call >> rw[ALOOKUP_def]) >>
      ASM_REWRITE_TAC [] >>
      rw[G_holds_def, fsem_Id_chop, fsem_eqs, p_sem_def, b_eval_def, SUBSET_DEF,
         dup_def, Str_def, Str0_def] >>
      qexists_tac `[K 0; K 0; K 0; K 0]` >> rw[])
QED

