(* The finite-trace calculus ftc (thesis Definition 4.28), its soundness
   (thesis Theorem 4.29) and the verification condition (thesis Lemma
   4.30). *)

Theory verifFtc
Ancestors
  arithmetic pred_set list rich_list combin ott traces tracesSem verifChop
  verifEff verifNorm verifTc verifPred

(* ------------------------------------------------------------------------ *)
(* Definition 4.28                                                          *)
(* ------------------------------------------------------------------------ *)

(* ftc_i(S, phi, X) and its helper ftc'_i(S, phi, X) as predicates on
   state sequences g. X lists the pairs (m, mu Y. psi) of procedures m and
   the fixed-point formulas that already have a side condition for m. A
   call m() may be specified by any fixed-point formula mu Y. psi, as in
   thesis Examples 5.8 to 5.12, where a call consumes the fixed point that
   expand introduces for a state formula. The thesis's definition is
   partial; here both functions take fuel n, spent at each step, and are
   false when it runs out. Chop is not distributed over conjunction. *)
Definition ftc_def:
  (ftc (lk:lookup) pre post 0 (i:num) S0 phi (X:(string # f) list)
       (g:num -> state) = F) /\
  (ftc lk pre post (SUC n) i S0 phi X g =
     case phi of
       f_mu Y psi => ftc lk pre post n i S0 (subst_f (f_mu Y psi) Y psi) X g
     | f_chop (f_mu Y psi) phi2 =>
         ftc lk pre post n i S0
             (distr (f_chop (subst_f (f_mu Y psi) Y psi) phi2)) X g
     | f_or phi1 phi2 =>
         (ftc lk pre post n i S0 phi1 X g \/ ftc lk pre post n i S0 phi2 X g)
     | f_and phi1 phi2 =>
         (ftc lk pre post n i S0 phi1 X g /\ ftc lk pre post n i S0 phi2 X g)
     | _ => ftc0 lk pre post n i S0 phi X g) /\
  (ftc0 lk pre post n i S_skip phi X g = pred n i phi g) /\
  (ftc0 lk pre post n i (S_assign x a) phi X g = pred n i phi g) /\
  (ftc0 lk pre post n i (S_ifelse b S1 S2) phi X g =
     case phi of
       f_chop phi1 phi2 =>
         (pred n i phi1 g /\
          (b_eval b (g i) ==> ftc lk pre post n (i + 1) S1 phi2 X g) /\
          (~b_eval b (g i) ==> ftc lk pre post n (i + 1) S2 phi2 X g))
     | _ => F) /\
  (ftc0 lk pre post n i (S_call m) phi X g =
     case phi of
       f_chop phi1 (f_mu Y psi) =>
         (pre m (g (i + 1)) /\ pred n i phi1 g /\
          if MEM (m, f_mu Y psi) X then T
          else
            case lk m of
              SOME body =>
                !h. tc pre post 1 body h /\ pre m (h 1) ==>
                    ftc lk pre post n 1 body (subst_f (f_mu Y psi) Y psi)
                        ((m, f_mu Y psi)::X) h
            | NONE => F)
     | _ => F) /\
  (ftc0 lk pre post n i (S_seq S1 S2) phi X g =
     case (S1, phi) of
       (S_skip, f_chop phi1 phi2) =>
         (pred n i phi1 g /\ ftc lk pre post n (i + 1) S2 phi2 X g)
     | (S_assign x a, f_chop phi1 phi2) =>
         (pred n i phi1 g /\ ftc lk pre post n (i + 1) S2 phi2 X g)
     | (S_call m, f_chop phi1 (f_chop phi2 phi3)) =>
         (ftc lk pre post n i (S_call m) (f_chop phi1 phi2) X g /\
          ftc lk pre post n (i + 2) S2 phi3 X g)
     | _ => F) /\
  (ftc0 lk pre post n i (S_var Y) phi X g = F)
Termination
  WF_REL_TAC `measure (\x. case x of
                 INL (lk,pre,post,n,i,S0,phi,X,g) => 2 * n
               | INR (lk,pre,post,n,i,S0,phi,X,g) => 2 * n + 1)` >>
  rw[]
End

(* ------------------------------------------------------------------------ *)
(* Theorem 4.29                                                             *)
(* ------------------------------------------------------------------------ *)

(* the side conditions recorded in X hold for the body traces shorter
   than L *)
Definition good_def:
  good (lk:lookup) (pre:string -> state -> bool) relI (L:num) X =
    !m mu body t.
      MEM (m, mu) X /\ lk m = SOME body /\ t IN Str lk (K {}) body /\
      LENGTH t < L /\ pre m (HD t) ==>
      t IN fsem relI mu
End

Theorem good_mono:
  !lk pre relI L L' X. good lk pre relI L X /\ L' <= L ==>
                       good lk pre relI L' X
Proof
  rw[good_def] >> first_x_assum irule >> rw[] >> metis_tac[]
QED

Theorem good_nil:
  !lk pre relI L. good lk pre relI L []
Proof
  rw[good_def]
QED

Theorem fuse_length:
  !l1 l2. 2 <= LENGTH l1 /\ 2 <= LENGTH l2 ==>
          LENGTH l1 <= LENGTH (l1 ++ TL l2) /\
          LENGTH l2 <= LENGTH (l1 ++ TL l2)
Proof
  rw[LENGTH_TL]
QED

Theorem eff_cases_seq:
  !lk S1 S2 t u.
    eff lk (S_seq S1 S2) t u <=>
    ?t1 t2 u1 u2. eff lk S1 t1 u1 /\ eff lk S2 t2 u2 /\ LAST t1 = HD t2 /\
                  t = t1 ++ TL t2 /\ u = u1 ++ TL u2
Proof
  rw[Once eff_cases] >> metis_tac[]
QED

(* the hypotheses of the soundness theorem *)
Definition sound_hyps_def:
  sound_hyps lk pre post =
    (conforms lk pre post /\ !m body. lk m = SOME body ==> nf body)
End

(* the claim of the soundness theorem, for fuel n *)
Definition ftc_claim_def:
  ftc_claim lk pre post relI n =
    !i S0 phi X g t u.
      ftc lk pre post n i S0 phi X g /\ eff lk S0 t u /\ agree i u g /\
      fv_f phi = [] /\ good lk pre relI (LENGTH t) X ==>
      t IN fsem relI phi
End

(* the case of a first call m(): the side condition and the claim for
   less fuel give the specification of all body traces *)
Theorem side_condition_sound:
  !lk pre post relI n m Y psi body X L.
    sound_hyps lk pre post /\ ftc_claim lk pre post relI n /\
    lk m = SOME body /\ fv_f (f_mu Y psi) = [] /\
    good lk pre relI L X /\
    (!h. tc pre post 1 body h /\ pre m (h 1) ==>
         ftc lk pre post n 1 body (subst_f (f_mu Y psi) Y psi)
             ((m, f_mu Y psi)::X) h) ==>
    !t. t IN Str lk (K {}) body /\ LENGTH t < L /\ pre m (HD t) ==>
        t IN fsem relI (f_mu Y psi)
Proof
  rpt gen_tac >> strip_tac >>
  `!k t. LENGTH t = k /\ t IN Str lk (K {}) body /\ LENGTH t < L /\
         pre m (HD t) ==> t IN fsem relI (f_mu Y psi)`
    suffices_by metis_tac[] >>
  completeInduct_on `k` >> rw[] >>
  drule Str_eff >> strip_tac >>
  qspecl_then [`u`, `1`] strip_assume_tac agree_exists >>
  `tc pre post 1 body g`
    by (fs[sound_hyps_def] >> metis_tac[eff_tc]) >>
  `pre m (g 1)`
    by (imp_res_tac eff_HD >> Cases_on `u` >> fs[agree_def]) >>
  `ftc lk pre post n 1 body (subst_f (f_mu Y psi) Y psi)
       ((m, f_mu Y psi)::X) g`
    by metis_tac[] >>
  `good lk pre relI (LENGTH t) ((m, f_mu Y psi)::X)`
    by (simp[good_def] >> rpt strip_tac >> fs[good_def] >> rw[] >>
        fs[] >> metis_tac[LESS_TRANS]) >>
  fs[ftc_claim_def] >>
  `t IN fsem relI (subst_f (f_mu Y psi) Y psi)`
    by (first_x_assum irule >> rw[closed_unfold] >> metis_tac[]) >>
  metis_tac[fsem_unfold]
QED

Theorem ftc0_sound:
  !lk pre post relI n.
    sound_hyps lk pre post /\ ftc_claim lk pre post relI n ==>
    !i S0 phi X g t u.
      ftc0 lk pre post n i S0 phi X g /\ eff lk S0 t u /\ agree i u g /\
      fv_f phi = [] /\ good lk pre relI (LENGTH t) X ==>
      t IN fsem relI phi
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `S0`
  >- ((* skip *)
      rw[ftc_def] >> fs[Once eff_cases] >> rw[] >> fs[agree_def] >>
      metis_tac[pred_sound])
  >- ((* assignment *)
      rw[ftc_def] >> fs[Once eff_cases] >> rw[] >> fs[agree_def] >>
      metis_tac[pred_sound])
  >- ((* sequence *)
      rename1 `S_seq S1 S2` >> strip_tac >>
      fs[eff_cases_seq] >> rw[] >>
      imp_res_tac eff_props >>
      `u1 <> [] /\ u2 <> [] /\ t1 <> [] /\ t2 <> []`
        by (Cases_on `u1` >> Cases_on `u2` >> Cases_on `t1` >>
            Cases_on `t2` >> fs[]) >>
      `LAST u1 = HD u2` by metis_tac[] >>
      drule_all agree_fuse >> strip_tac >>
      `good lk pre relI (LENGTH t1) X /\ good lk pre relI (LENGTH t2) X`
        by metis_tac[good_mono, fuse_length] >>
      Cases_on `S1` >> fs[ftc_def] >>
      Cases_on `phi` >> fs[fv_f_def, fsem_chop]
      >- ((* skip; S2 *)
          qpat_x_assum `eff _ S_skip _ _`
            (strip_assume_tac o ONCE_REWRITE_RULE [eff_cases]) >>
          fs[] >> rw[] >> fs[agree_def] >>
          Cases_on `t2` >> fs[] >> irule chop_intro_pair >> rw[]
          >- metis_tac[pred_sound]
          >- (fs[ftc_claim_def] >> first_x_assum irule >> rw[] >>
              metis_tac[]))
      >- ((* x := a; S2 *)
          qpat_x_assum `eff _ (S_assign _ _) _ _`
            (strip_assume_tac o ONCE_REWRITE_RULE [eff_cases]) >>
          fs[] >> rw[] >> fs[agree_def] >>
          Cases_on `t2` >> fs[] >> irule chop_intro_pair >> rw[]
          >- metis_tac[pred_sound]
          >- (fs[ftc_claim_def] >> first_x_assum irule >> rw[] >>
              metis_tac[]))
      >- ((* m(); S2 *)
          qmatch_goalsub_rename_tac `chop (fsem _ f1) (fsem _ f23)` >>
          Cases_on `f23` >> fs[fv_f_def] >>
          rename1 `ftc _ _ _ _ _ (S_call m) (f_chop f1 f2) X g` >>
          rename1 `ftc _ _ _ _ _ S2 f3 X g` >>
          `LENGTH u1 = 3`
            by (qpat_x_assum `eff _ (S_call _) _ _`
                  (strip_assume_tac o ONCE_REWRITE_RULE [eff_cases]) >>
                fs[]) >>
          fs[GSYM fsem_chop, ftc_claim_def] >>
          `t1 IN fsem relI (f_chop f1 f2)`
            by (first_x_assum irule >> rw[fv_f_def] >> metis_tac[]) >>
          `t2 IN fsem relI f3`
            by (first_x_assum irule >> rw[] >> metis_tac[]) >>
          fs[fsem_chop, GSYM chop_assoc] >>
          irule chop_intro >> rw[]))
  >- ((* conditional *)
      rename1 `S_ifelse b S1 S2` >> strip_tac >>
      Cases_on `phi` >> fs[ftc_def, fv_f_def, fsem_chop] >>
      fs[Once eff_cases] >> rw[] >> fs[agree_def] >> rw[] >>
      irule chop_intro_pair >> fs[ftc_claim_def] >> rw[] >>
      TRY (metis_tac[pred_sound]) >>
      `good lk pre relI (SUC (LENGTH r)) X`
        by (irule good_mono >> qexists_tac `SUC (SUC (LENGTH r))` >> rw[]) >>
      `agree (i + 1) (g (i + 1)::q) g` by rw[agree_def] >>
      first_x_assum irule >> rw[] >> metis_tac[])
  >- ((* call *)
      rename1 `S_call m` >> strip_tac >>
      Cases_on `phi` >> fs[ftc_def] >>
      rename1 `f_chop f1 f2` >> Cases_on `f2` >> fs[fv_f_def, fsem_chop] >>
      rw[] >> rename1 `f_mu Y psi` >>
      qpat_x_assum `eff _ (S_call _) _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [eff_cases]) >>
      fs[] >> rw[] >>
      drule Str_call_cases >> strip_tac >> rw[] >> fs[agree_def] >>
      irule chop_intro_pair >> rw[] >>
      TRY (metis_tac[pred_sound] >> NO_TAC) >>
      Cases_on `MEM (m, f_mu Y psi) X` >> fs[]
      >- (fs[good_def] >> first_x_assum irule >> rw[] >> metis_tac[]) >>
      irule side_condition_sound >> rw[fv_f_def] >>
      qexistsl_tac [`SUC (SUC (LENGTH r))`, `X`, `body`, `lk`, `m`, `n`,
                    `post`, `pre`] >>
      rw[])
  >- ((* statement variable *)
      rw[ftc_def])
QED

Theorem ftc_claim_all:
  !lk pre post relI n. sound_hyps lk pre post ==> ftc_claim lk pre post relI n
Proof
  rpt gen_tac >> strip_tac >> Induct_on `n`
  >- rw[ftc_claim_def, ftc_def] >>
  `!i S0 phi X g t u.
      ftc0 lk pre post n i S0 phi X g /\ eff lk S0 t u /\ agree i u g /\
      fv_f phi = [] /\ good lk pre relI (LENGTH t) X ==>
      t IN fsem relI phi` by metis_tac[ftc0_sound] >>
  simp[ftc_claim_def] >> rpt gen_tac >>
  Cases_on `phi` >> simp[Once ftc_def] >> rpt strip_tac >>
  TRY (metis_tac[] >> NO_TAC) >>
  TRY (fs[ftc_claim_def, fv_f_def, fsem_and, fsem_or] >> metis_tac[] >>
       NO_TAC)
  >~ [`fsem relI (f_chop f1 f2)`]
  >- (Cases_on `f1` >> fs[] >>
      TRY (metis_tac[] >> NO_TAC) >>
      rename1 `f_chop (f_mu Y psi) f2` >>
      fs[fv_f_def] >>
      `fv_f (f_mu Y psi) = []` by rw[fv_f_def] >>
      `fv_f (distr (f_chop (subst_f (f_mu Y psi) Y psi) f2)) = []`
        by (irule closed_distr >> rw[fv_f_def, closed_unfold]) >>
      fs[ftc_claim_def] >> first_x_assum drule_all >>
      rw[fsem_distr, fsem_chop] >> metis_tac[fsem_unfold])
  >~ [`fsem relI (f_mu Y psi)`]
  >- (`fv_f (subst_f (f_mu Y psi) Y psi) = []` by rw[closed_unfold] >>
      fs[ftc_claim_def] >> first_x_assum drule_all >>
      metis_tac[fsem_unfold])
QED

(* Theorem 4.29: if every procedure conforms with its contract and the
   procedure bodies are in normal form, then for every trace t of S with
   effective trace u satisfying ftc_i(S, phi, []) at position i, t is in
   ||phi||. The thesis's hypotheses that phi is normalized and that ftc
   is well-defined are not needed: any fuel n is sound. *)
Theorem ftc_sound:
  !lk pre post relI n i S0 phi g t u.
    conforms lk pre post /\ (!m body. lk m = SOME body ==> nf body) /\
    fv_f phi = [] /\ eff lk S0 t u /\ agree i u g /\
    ftc lk pre post n i S0 phi [] g ==>
    t IN fsem relI phi
Proof
  rw[] >>
  `ftc_claim lk pre post relI n`
    by (irule ftc_claim_all >> rw[sound_hyps_def] >> metis_tac[]) >>
  fs[ftc_claim_def] >> first_x_assum irule >>
  rw[] >> qexistsl_tac [`S0`, `[]`, `g`, `i`, `u`] >> rw[good_nil]
QED

(* ------------------------------------------------------------------------ *)
(* Lemma 4.30                                                               *)
(* ------------------------------------------------------------------------ *)

(* Lemma 4.30, for any statement and procedure table: the verification
   condition tc(S) ==> ftc(S, phi), stated for the normalized statement
   and procedure bodies, implies that every trace of S is in ||phi||. *)
Theorem vc_sound:
  !lk pre post relI n S0 phi.
    conforms lk pre post /\ fv_f phi = [] /\
    (!g. tc pre post 1 (norm S0) g ==>
         ftc (norm_lk lk) pre post n 1 (norm S0) phi [] g) ==>
    Str lk (K {}) S0 SUBSET fsem relI phi
Proof
  rw[SUBSET_DEF] >>
  `x IN Str (norm_lk lk) (K {}) (norm S0)` by rw[Str_norm] >>
  drule Str_eff >> strip_tac >>
  qspecl_then [`u`, `1`] strip_assume_tac agree_exists >>
  `conforms (norm_lk lk) pre post` by rw[conforms_norm_lk] >>
  `tc pre post 1 (norm S0) g` by metis_tac[eff_tc, nf_norm] >>
  irule ftc_sound >> rw[] >>
  metis_tac[norm_lk_nf]
QED

(* Lemma 4.30 as in the thesis, for statements and procedure bodies that
   are already in normal form *)
Theorem vc_sound_nf:
  !lk pre post relI n S0 phi.
    conforms lk pre post /\ (!m body. lk m = SOME body ==> nf body) /\
    nf S0 /\ fv_f phi = [] /\
    (!g. tc pre post 1 S0 g ==> ftc lk pre post n 1 S0 phi [] g) ==>
    Str lk (K {}) S0 SUBSET fsem relI phi
Proof
  rw[SUBSET_DEF] >>
  drule Str_eff >> strip_tac >>
  qspecl_then [`u`, `1`] strip_assume_tac agree_exists >>
  `tc pre post 1 S0 g` by metis_tac[eff_tc] >>
  irule ftc_sound >> rw[] >> metis_tac[]
QED
