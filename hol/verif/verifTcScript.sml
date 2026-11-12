(* Trace constraints (thesis Definition 4.13) and Lemma 4.16: every
   effective trace satisfies the trace constraints. *)

Theory verifTc
Ancestors
  arithmetic pred_set list combin traces tracesSem verifEff verifNorm

(* a weight under which re-associating a sequence to the right decreases *)
Definition seqw_def:
  (seqw (S_seq S1 S2) = 2 * seqw S1 + seqw S2 + 1) /\
  (seqw (S_ifelse b S1 S2) = seqw S1 + seqw S2 + 1) /\
  (seqw _ = 1:num)
End

(* tc_i(S) of Definition 4.13, as a predicate on state sequences g. The
   thesis's first-order formulas are embedded shallowly: the predicates
   Id and Sb are equalities of states, and B[[b]](s) is b_eval. *)
Definition tc_def:
  (tc (pre:string -> state -> bool) (post:string -> state -> state -> bool)
      (i:num) S_skip (g:num -> state) = (g (i + 1) = g i)) /\
  (tc pre post i (S_assign x a) g =
     (g (i + 1) = (x =+ a_eval a (g i)) (g i))) /\
  (tc pre post i (S_ifelse b S1 S2) g =
     (g (i + 1) = g i /\
      (b_eval b (g i) ==> tc pre post (i + 1) S1 g) /\
      (~b_eval b (g i) ==> tc pre post (i + 1) S2 g))) /\
  (tc pre post i (S_call m) g =
     (g (i + 1) = g i /\
      (pre m (g (i + 1)) ==> post m (g (i + 1)) (g (i + 2))))) /\
  (tc pre post i (S_seq (S_call m) S2) g =
     (tc pre post i (S_call m) g /\ tc pre post (i + 2) S2 g)) /\
  (tc pre post i (S_seq (S_seq S1 S2) S3) g =
     tc pre post i (S_seq S1 (S_seq S2 S3)) g) /\
  (tc pre post i (S_seq S1 S2) g =
     (tc pre post i S1 g /\ tc pre post (i + 1) S2 g)) /\
  (tc pre post i (S_var Y) g = T)
Termination
  WF_REL_TAC `measure (\(pre,post,i,S0,g). seqw S0)` >> rw[seqw_def]
End

(* Lemma 4.16, for statements in normal form: the effective trace u of a
   trace of S, placed at position i, satisfies tc_i(S) *)
Theorem eff_tc:
  !lk pre post.
    conforms lk pre post ==>
    !S0 t u. eff lk S0 t u ==>
             !i g. nf S0 /\ agree i u g ==> tc pre post i S0 g
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac eff_strongind >>
  rw[tc_def, agree_def, nf_def]
  >- ((* sequence *)
      rename1 `agree i (u1 ++ TL u2) g` >> rename1 `atomic S1` >>
      rename1 `LAST t1 = HD t2` >>
      imp_res_tac eff_props >>
      `u1 <> [] /\ u2 <> []` by (Cases_on `u1` >> Cases_on `u2` >> fs[]) >>
      `LAST u1 = HD u2` by metis_tac[] >>
      drule_all agree_fuse >> strip_tac >>
      Cases_on `S1` >> fs[atomic_def, nf_def, tc_def]
      >- (qpat_x_assum `eff _ S_skip _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >> fs[agree_def])
      >- (qpat_x_assum `eff _ (S_assign _ _) _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >> fs[agree_def])
      >- (qpat_x_assum `eff _ (S_call _) _ _` (strip_assume_tac o
            SIMP_RULE (srw_ss()) [Once eff_cases]) >> rw[] >> fs[agree_def])
      >- fs[Once eff_cases])
  >- ((* call *)
      fs[conforms_def])
QED
