(* Theorem 4.29 and Lemma 4.30 fail with the thesis's distr (Definition
   4.23), which also distributes chop over conjunction. The thesis writes
   chop sequences without brackets (e.g. in Example 4.25), so distr_thesis
   regroups chops to the right. *)

Theory verifFtcThesis
Ancestors
  arithmetic pred_set list combin traces tracesSem verifChop verifEff
  verifNorm verifTc verifPred

(* ------------------------------------------------------------------------ *)
(* Definitions 4.20, 4.23 and 4.26 as in the thesis                         *)
(* ------------------------------------------------------------------------ *)

(* expand(phi). The thesis asks for a fresh X'; the formula mu X'. (true \/
   true^X') is closed, so any name will do. *)
Definition expand_def:
  (expand (f_state p) =
     f_or (f_state p)
          (f_chop (f_state p)
                  (f_mu "X'" (f_or (f_state (p_b b_true))
                                   (f_chop (f_state (p_b b_true))
                                           (f_recvar "X'")))))) /\
  (expand (f_and f1 f2) = f_and (expand f1) (expand f2)) /\
  (expand (f_or f1 f2) = f_or (expand f1) (expand f2)) /\
  (expand (f_chop f1 f2) = f_chop (expand f1) (expand f2)) /\
  (expand (f_mu X f) = f_mu X (expand f)) /\
  (expand f = f)
End

(* a weight under which re-grouping a chop to the right decreases *)
Definition chopw_def:
  (chopw (f_chop f1 f2) = 2 * chopw f1 + chopw f2 + 1) /\
  (chopw (f_and f1 f2) = chopw f1 + chopw f2 + 1) /\
  (chopw (f_or f1 f2) = chopw f1 + chopw f2 + 1) /\
  (chopw (f_mu X f) = chopw f + 1) /\
  (chopw _ = 1:num)
End

(* distr(phi) of Definition 4.23, with the case for conjunction, reading
   phi1^phi2^phi3 as phi1^(phi2^phi3) *)
Definition distr_thesis_def:
  (distr_thesis (f_chop (f_or f1 f2) f3) =
     f_or (distr_thesis (f_chop f1 f3)) (distr_thesis (f_chop f2 f3))) /\
  (distr_thesis (f_chop (f_and f1 f2) f3) =
     f_and (distr_thesis (f_chop f1 f3)) (distr_thesis (f_chop f2 f3))) /\
  (distr_thesis (f_chop (f_chop f1 f2) f3) =
     distr_thesis (f_chop f1 (f_chop f2 f3))) /\
  (distr_thesis (f_chop f1 f2) =
     f_chop (distr_thesis f1) (distr_thesis f2)) /\
  (distr_thesis (f_and f1 f2) = f_and (distr_thesis f1) (distr_thesis f2)) /\
  (distr_thesis (f_or f1 f2) = f_or (distr_thesis f1) (distr_thesis f2)) /\
  (distr_thesis (f_mu X f) = f_mu X (distr_thesis f)) /\
  (distr_thesis f = f)
Termination
  WF_REL_TAC `measure chopw` >> rw[chopw_def]
End

(* Definition 4.26 *)
Definition normalised_def:
  normalised phi = ?phi0. phi = distr_thesis (expand phi0)
End

(* ------------------------------------------------------------------------ *)
(* Definition 4.28 with the thesis's distr                                  *)
(* ------------------------------------------------------------------------ *)

(* ftc and ftc0 of verifFtc, with distr_thesis in place of distr *)
Definition ftc_thesis_def:
  (ftc_thesis (lk:lookup) pre post 0 (i:num) S0 phi
              (X:(string # f) list) (g:num -> state) = F) /\
  (ftc_thesis lk pre post (SUC n) i S0 phi X g =
     case phi of
       f_mu Y psi =>
         ftc_thesis lk pre post n i S0 (subst_f (f_mu Y psi) Y psi) X g
     | f_chop (f_mu Y psi) phi2 =>
         ftc_thesis lk pre post n i S0
             (distr_thesis (f_chop (subst_f (f_mu Y psi) Y psi) phi2)) X g
     | f_or phi1 phi2 =>
         (ftc_thesis lk pre post n i S0 phi1 X g \/
          ftc_thesis lk pre post n i S0 phi2 X g)
     | f_and phi1 phi2 =>
         (ftc_thesis lk pre post n i S0 phi1 X g /\
          ftc_thesis lk pre post n i S0 phi2 X g)
     | _ => ftc0_thesis lk pre post n i S0 phi X g) /\
  (ftc0_thesis lk pre post n i S_skip phi X g = pred n i phi g) /\
  (ftc0_thesis lk pre post n i (S_assign x a) phi X g = pred n i phi g) /\
  (ftc0_thesis lk pre post n i (S_ifelse b S1 S2) phi X g =
     case phi of
       f_chop phi1 phi2 =>
         (pred n i phi1 g /\
          (b_eval b (g i) ==> ftc_thesis lk pre post n (i + 1) S1 phi2 X g) /\
          (~b_eval b (g i) ==> ftc_thesis lk pre post n (i + 1) S2 phi2 X g))
     | _ => F) /\
  (ftc0_thesis lk pre post n i (S_call m) phi X g =
     case phi of
       f_chop phi1 (f_mu Y psi) =>
         (Y = m /\ pre m (g (i + 1)) /\ pred n i phi1 g /\
          if MEM (m, psi) X then T
          else
            case lk m of
              SOME body =>
                !h. tc pre post 1 body h /\ pre m (h 1) ==>
                    ftc_thesis lk pre post n 1 body
                               (subst_f (f_mu m psi) m psi) ((m, psi)::X) h
            | NONE => F)
     | _ => F) /\
  (ftc0_thesis lk pre post n i (S_seq S1 S2) phi X g =
     case (S1, phi) of
       (S_skip, f_chop phi1 phi2) =>
         (pred n i phi1 g /\ ftc_thesis lk pre post n (i + 1) S2 phi2 X g)
     | (S_assign x a, f_chop phi1 phi2) =>
         (pred n i phi1 g /\ ftc_thesis lk pre post n (i + 1) S2 phi2 X g)
     | (S_call m, f_chop phi1 (f_chop phi2 phi3)) =>
         (ftc_thesis lk pre post n i (S_call m) (f_chop phi1 phi2) X g /\
          ftc_thesis lk pre post n (i + 2) S2 phi3 X g)
     | _ => F) /\
  (ftc0_thesis lk pre post n i (S_var Y) phi X g = F)
Termination
  WF_REL_TAC `measure (\x. case x of
                 INL (lk,pre,post,n,i,S0,phi,X,g) => 2 * n
               | INR (lk,pre,post,n,i,S0,phi,X,g) => 2 * n + 1)` >>
  rw[]
End

(* ------------------------------------------------------------------------ *)
(* The counterexample                                                       *)
(* ------------------------------------------------------------------------ *)

Overload fId = ``f_rel R_Id``
Overload ftrue = ``f_state (p_b b_true)``

(* skip; skip; skip *)
Overload skip3 = ``S_seq S_skip (S_seq S_skip S_skip)``

(* (mu Y. Id /\ Id^Id)^true, before normalisation *)
Overload phi0 = ``f_chop (f_mu "Y" (f_and fId (f_chop fId fId))) ftrue``

(* mu Y. Id /\ Id^Id has no traces: Id has traces of length 2 only,
   Id^Id of length 3 only *)
Theorem phi0_empty:
  !relI. fsem relI (distr_thesis (expand phi0)) = {}
Proof
  rw[expand_def, distr_thesis_def] >>
  `fsem relI (f_mu "Y" (f_and fId (f_chop fId fId))) = {}`
    by (rw[fsem_def, f_sem_def] >> irule (iffLR SUBSET_EMPTY) >>
        irule mu_sem_least >>
        rw[f_sem_def, EXTENSION, IN_chop] >>
        CCONTR_TAC >> fs[] >> rw[] >> fs[]) >>
  rw[fsem_chop, EXTENSION, IN_chop] >>
  fs[EXTENSION, fsem_def]
QED

Theorem ftc_thesis_skip3:
  !lk pre post g.
    g 2 = g 1 /\ g 3 = g 2 /\ g 4 = g 3 ==>
    ftc_thesis lk pre post 10 1 skip3 (distr_thesis (expand phi0)) [] g
Proof
  rw[expand_def, distr_thesis_def] >>
  EVAL_TAC >> rw[]
QED

(* Theorem 4.29 fails: all its hypotheses hold, but the trace of
   skip; skip; skip is not in the semantics of the formula *)
Theorem ftc_thesis_unsound:
  ?lk pre post n S0 phi t u g.
    conforms lk pre post /\ (!m body. lk m = SOME body ==> nf body) /\
    nf S0 /\ fv_f phi = [] /\ normalised phi /\
    eff lk S0 t u /\ agree 1 u g /\
    ftc_thesis lk pre post n 1 S0 phi [] g /\
    !relI. t NOTIN fsem relI phi
Proof
  qabbrev_tac `s = (K 0):state` >>
  qexistsl_tac [`K NONE`, `\m s. T`, `\m s s'. T`, `10`, `skip3`,
                `distr_thesis (expand phi0)`, `[s; s; s; s]`, `[s; s; s; s]`,
                `K s`] >>
  rw[nf_def, atomic_def, normalised_def, phi0_empty]
  >- (rw[conforms_def] >> CCONTR_TAC >> fs[] >>
      drule Str_call_cases >> rw[])
  >- (EVAL_TAC >> rw[])
  >- metis_tac[]
  >- (`eff (K NONE) S_skip [s; s] [s; s]` by rw[eff_rules] >>
      `eff (K NONE) (S_seq S_skip S_skip) ([s; s] ++ TL [s; s])
           ([s; s] ++ TL [s; s])` by (irule (cj 3 eff_rules) >> rw[]) >>
      `eff (K NONE) skip3 ([s; s] ++ TL ([s; s] ++ TL [s; s]))
           ([s; s] ++ TL ([s; s] ++ TL [s; s]))`
        by (irule (cj 3 eff_rules) >> fs[]) >>
      fs[])
  >- rw[agree_def]
  >- rw[ftc_thesis_skip3]
QED

(* Lemma 4.30 fails: ftc holds on every state sequence that satisfies tc,
   but skip; skip; skip has traces and the formula has none *)
Theorem vc_thesis_unsound:
  ?lk pre post n S0 phi.
    conforms lk pre post /\ (!m body. lk m = SOME body ==> nf body) /\
    nf S0 /\ fv_f phi = [] /\ normalised phi /\
    (!g. tc pre post 1 S0 g ==> ftc_thesis lk pre post n 1 S0 phi [] g) /\
    !relI. ~(Str lk (K {}) S0 SUBSET fsem relI phi)
Proof
  qexistsl_tac [`K NONE`, `\m s. T`, `\m s s'. T`, `10`, `skip3`,
                `distr_thesis (expand phi0)`] >>
  rw[nf_def, atomic_def, normalised_def, phi0_empty]
  >- (rw[conforms_def] >> CCONTR_TAC >> fs[] >>
      drule Str_call_cases >> rw[])
  >- (EVAL_TAC >> rw[])
  >- metis_tac[]
  >- (irule ftc_thesis_skip3 >> fs[tc_def])
  >- (rw[SUBSET_EMPTY, EXTENSION] >>
      qexists_tac `[K 0; K 0; K 0; K 0]` >>
      rw[Str_def, Str0_def, IN_chop] >>
      qexistsl_tac [`[K 0; K 0]`, `[K 0; K 0; K 0]`] >> rw[] >>
      qexistsl_tac [`[K 0; K 0]`, `[K 0; K 0]`] >> rw[])
QED
