(* The procedure contract condition pcc (thesis Definition 4.34) and the
   conformance of procedures with their contracts (thesis Lemmas 4.35 and
   4.36). Lemma 4.36 is proved directly, by induction on the length of
   traces, for all procedures at once, instead of by the thesis's encoding
   of all procedures as one procedure. *)

Theory vcPcc
Ancestors
  arithmetic pred_set list rich_list combin traces tracesSem verifEff
  verifNorm verifTc

(* ------------------------------------------------------------------------ *)
(* Definition 4.34                                                          *)
(* ------------------------------------------------------------------------ *)

(* pcc_i(S, phi) as a predicate on state sequences g, for S in normal form.
   The thesis's phi(s(1), s(j)) is phi s0 (g j): the initial state s0 is a
   parameter, which is g 1 when pcc is used. Cases the thesis leaves
   undefined are false. *)
Definition pcc_def:
  (pcc (pre:string -> state -> bool) (post:string -> state -> state -> bool)
       (phi:state -> state -> bool) (s0:state) (i:num) (S_assign x a)
       (g:num -> state) =
     (g (i + 1) = (x =+ a_eval a (g i)) (g i) ==> phi s0 (g (i + 1)))) /\
  (pcc pre post phi s0 i S_skip g =
     (g (i + 1) = g i ==> phi s0 (g (i + 1)))) /\
  (pcc pre post phi s0 i (S_ifelse b S1 S2) g =
     (g (i + 1) = g i ==>
      (b_eval b (g i) ==> pcc pre post phi s0 (i + 1) S1 g) /\
      (~b_eval b (g i) ==> pcc pre post phi s0 (i + 1) S2 g))) /\
  (pcc pre post phi s0 i (S_call m) g =
     (g (i + 1) = g i /\
      (pre m (g (i + 1)) ==> post m (g (i + 1)) (g (i + 2))) ==>
      phi s0 (g (i + 2)))) /\
  (pcc pre post phi s0 i (S_seq (S_assign x a) S2) g =
     (g (i + 1) = (x =+ a_eval a (g i)) (g i) ==>
      pcc pre post phi s0 (i + 1) S2 g)) /\
  (pcc pre post phi s0 i (S_seq S_skip S2) g =
     (g (i + 1) = g i ==> pcc pre post phi s0 (i + 1) S2 g)) /\
  (pcc pre post phi s0 i (S_seq (S_call m) S2) g =
     (g (i + 1) = g i /\
      (pre m (g (i + 1)) ==> post m (g (i + 1)) (g (i + 2))) ==>
      pcc pre post phi s0 (i + 2) S2 g)) /\
  (pcc pre post phi s0 i (S_seq S1 S2) g = F) /\
  (pcc pre post phi s0 i (S_var Y) g = F)
End

(* ------------------------------------------------------------------------ *)
(* Soundness of pcc for one trace                                           *)
(* ------------------------------------------------------------------------ *)

(* Lemma 4.16 (eff_tc), assuming conformance only for calls whose traces
   are not longer than a bound L *)
Theorem eff_tc_below:
  !lk pre post L.
    (!m t'. t' IN Str lk (K {}) (S_call m) /\ LENGTH t' <= L /\
            pre m (HD t') ==> post m (HD t') (LAST t')) ==>
    !S0 t u. eff lk S0 t u ==>
             LENGTH t <= L ==>
             !i g. nf S0 /\ agree i u g ==> tc pre post i S0 g
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac eff_strongind >>
  rw[tc_def, agree_def, nf_def]
  >- ((* sequence *)
      rename1 `agree i (u1 ++ TL u2) g` >> rename1 `atomic S1` >>
      rename1 `LAST t1 = HD t2` >>
      imp_res_tac eff_props >>
      `u1 <> [] /\ u2 <> [] /\ t1 <> [] /\ t2 <> []`
        by (Cases_on `u1` >> Cases_on `u2` >> Cases_on `t1` >>
            Cases_on `t2` >> fs[]) >>
      `LENGTH t1 <= L /\ LENGTH t2 <= L`
        by (fs[LENGTH_APPEND, LENGTH_TL] >> Cases_on `t2` >> fs[]) >>
      `LAST u1 = HD u2` by metis_tac[] >>
      drule_all agree_fuse >> strip_tac >>
      Cases_on `S1` >> fs[atomic_def, nf_def, tc_def]
      >- (qpat_x_assum `eff _ S_skip _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >> fs[agree_def])
      >- (qpat_x_assum `eff _ (S_assign _ _) _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >> fs[agree_def])
      >- (qpat_x_assum `eff _ (S_call _) _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >> fs[agree_def] >>
          first_x_assum irule >> rw[])
      >- fs[Once eff_cases])
QED

(* if the trace constraints and the procedure contract condition hold on
   an effective trace, then phi holds for the initial and final states *)
Theorem pcc_sound:
  !lk pre post phi s0 S0 t u.
    eff lk S0 t u ==>
    !i g. nf S0 /\ agree i u g /\ tc pre post i S0 g /\
          pcc pre post phi s0 i S0 g ==> phi s0 (LAST u)
Proof
  ntac 5 gen_tac >> ho_match_mp_tac eff_strongind >>
  rw[tc_def, nf_def, pcc_def, LAST_CONS]
  >~ [`agree i (u1 ++ TL u2) g`]
  >- (rename1 `atomic S1` >>
      imp_res_tac eff_props >>
      `u1 <> [] /\ u2 <> []`
        by (Cases_on `u1` >> Cases_on `u2` >> fs[]) >>
      `LAST u1 = HD u2` by metis_tac[] >>
      drule_all agree_fuse >> strip_tac >>
      `LAST (u1 ++ TL u2) = LAST u2` by metis_tac[fuse_props] >>
      Cases_on `S1` >> fs[atomic_def, nf_def, tc_def, pcc_def]
      >- (qpat_x_assum `eff _ S_skip _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >>
          fs[agree_def] >> first_x_assum irule >> rfs[] >> metis_tac[])
      >- (qpat_x_assum `eff _ (S_assign _ _) _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >>
          fs[agree_def] >> first_x_assum irule >> rfs[] >> metis_tac[])
      >- (qpat_x_assum `eff _ (S_call _) _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >>
          fs[agree_def] >> first_x_assum irule >> rfs[] >> metis_tac[])) >>
  TRY (fs[agree_def] >> rfs[] >> NO_TAC) >>
  first_x_assum irule >> rw[] >> qexistsl_tac [`g`, `i + 1`] >>
  fs[agree_def] >> rfs[]
QED

(* ------------------------------------------------------------------------ *)
(* Lemmas 4.35 and 4.36                                                     *)
(* ------------------------------------------------------------------------ *)

(* m |= <Pre_m, Post_m> (Definition 4.6, for one procedure) *)
Definition conforms_proc_def:
  conforms_proc lk pre post m <=>
    !t. t IN Str lk (K {}) (S_call m) /\ pre m (HD t) ==>
        post m (HD t) (LAST t)
End

Theorem conforms_conforms_proc:
  !lk pre post. conforms lk pre post <=> !m. conforms_proc lk pre post m
Proof
  rw[conforms_def, conforms_proc_def] >> metis_tac[]
QED

(* validity of  forall s. Pre_m(s(1)) ==> pcc_1(S_m, Post_m)  *)
Definition pcc_valid_def:
  pcc_valid lk pre post m <=>
    !body. lk m = SOME body ==>
           nf body /\
           !g. pre m (g 1) ==> pcc pre post (post m) (g 1) 1 body g
End

(* the procedures in C conform if their contract conditions are valid and
   the other procedures conform *)
Theorem pcc_conforms_set:
  !lk pre post C.
    (!m. m NOTIN C ==> conforms_proc lk pre post m) /\
    (!m. m IN C ==> pcc_valid lk pre post m) ==>
    !m. m IN C ==> conforms_proc lk pre post m
Proof
  rpt gen_tac >> strip_tac >>
  `!L m t. m IN C /\ t IN Str lk (K {}) (S_call m) /\ LENGTH t <= L /\
           pre m (HD t) ==> post m (HD t) (LAST t)`
    suffices_by (rw[conforms_proc_def] >> metis_tac[LESS_EQ_REFL]) >>
  Induct
  >- (rw[] >> drule Str_call_cases >> rw[] >> fs[])
  >- (rw[] >> drule Str_call_cases >> rw[] >> fs[] >>
      `?u. eff lk body (s::r) u` by metis_tac[Str_eff] >>
      `?g. agree 1 u g` by metis_tac[agree_exists] >>
      `pcc_valid lk pre post m` by metis_tac[] >>
      fs[pcc_valid_def] >>
      `!m' t'. t' IN Str lk (K {}) (S_call m') /\ LENGTH t' <= L /\
               pre m' (HD t') ==> post m' (HD t') (LAST t')`
        by (rw[] >> Cases_on `m' IN C` >- metis_tac[] >>
            fs[conforms_proc_def] >> metis_tac[]) >>
      `tc pre post 1 body g`
        by (qspecl_then [`lk`, `pre`, `post`, `L`] mp_tac eff_tc_below >>
            impl_tac >- metis_tac[] >> disch_then drule >> rw[] >>
            metis_tac[]) >>
      imp_res_tac eff_HD >>
      `g 1 = s` by (Cases_on `u` >> fs[agree_def]) >>
      `pcc pre post (post m) (g 1) 1 body g` by metis_tac[] >>
      drule pcc_sound >>
      disch_then (qspecl_then [`pre`, `post`, `post m`, `g 1`, `1`, `g`]
                              mp_tac) >>
      rw[] >> imp_res_tac eff_LAST >> fs[] >> metis_tac[])
QED

(* Lemma 4.35 *)
Theorem pcc_conforms_one:
  !lk pre post m.
    (!m'. m' <> m ==> conforms_proc lk pre post m') /\
    pcc_valid lk pre post m ==>
    conforms_proc lk pre post m
Proof
  rw[] >> qspecl_then [`lk`, `pre`, `post`, `{m}`] mp_tac pcc_conforms_set >>
  rw[]
QED

(* Lemma 4.36 *)
Theorem pcc_conforms:
  !lk pre post. (!m. pcc_valid lk pre post m) ==> conforms lk pre post
Proof
  rw[conforms_conforms_proc] >>
  qspecl_then [`lk`, `pre`, `post`, `UNIV`] mp_tac pcc_conforms_set >>
  rw[]
QED

(* Lemma 4.36 for procedure bodies in any shape, via normalization *)
Theorem pcc_conforms_norm:
  !lk pre post.
    (!m. pcc_valid (norm_lk lk) pre post m) ==> conforms lk pre post
Proof
  metis_tac[pcc_conforms, conforms_norm_lk]
QED
