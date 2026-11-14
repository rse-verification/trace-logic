(* The verification conditions over the states of the program variables xs
   only, as in thesis Definition 4.2 (D_State, states as tuples over xs)
   and the Z3 encoding of thesis Section 5.1. A state over xs is
   represented as a total state that is 0 outside xs. The proofs project
   arbitrary states to xs: proj xs s keeps the values of xs and sets the
   other variables to 0. *)

Theory vcXs
Ancestors
  arithmetic pred_set list rich_list alist combin string string_num traces
  tracesSem
  verifEff verifNorm verifTc verifPred verifFtc folLang folModels
  folString folRec vcContract vcPcc vcGen vcSound

(* ------------------------------------------------------------------------ *)
(* Program variables                                                        *)
(* ------------------------------------------------------------------------ *)

Definition avars_def:
  (avars (a_num n) = []) /\
  (avars (a_var x) = [x]) /\
  (avars (a_uminus a) = avars a) /\
  (avars (a_plus a1 a2) = avars a1 ++ avars a2) /\
  (avars (a_minus a1 a2) = avars a1 ++ avars a2) /\
  (avars (a_times a1 a2) = avars a1 ++ avars a2)
End

Definition bvars_def:
  (bvars b_true = []) /\
  (bvars b_false = []) /\
  (bvars (b_eq a1 a2) = avars a1 ++ avars a2) /\
  (bvars (b_leq a1 a2) = avars a1 ++ avars a2) /\
  (bvars (b_neg b) = bvars b) /\
  (bvars (b_and b1 b2) = bvars b1 ++ bvars b2)
End

(* the program variables of a statement (not its procedure names) *)
Definition svars_def:
  (svars S_skip = []) /\
  (svars (S_assign x a) = x :: avars a) /\
  (svars (S_seq S1 S2) = svars S1 ++ svars S2) /\
  (svars (S_ifelse b S1 S2) = bvars b ++ svars S1 ++ svars S2) /\
  (svars (S_call m) = []) /\
  (svars (S_var Y) = [])
End

(* the program variables of a trace formula *)
Definition fvars_def:
  (fvars (f_state (p_b b)) = bvars b) /\
  (fvars (f_rel R_Id) = []) /\
  (fvars (f_rel (R_Sb a x)) = x :: avars a) /\
  (fvars (f_rel (R_other q)) = []) /\
  (fvars (f_recvar X) = []) /\
  (fvars (f_and f1 f2) = fvars f1 ++ fvars f2) /\
  (fvars (f_or f1 f2) = fvars f1 ++ fvars f2) /\
  (fvars (f_chop f1 f2) = fvars f1 ++ fvars f2) /\
  (fvars (f_mu X f) = fvars f)
End

Definition tavars_def:
  (tavars (ta_num n) = []) /\
  (tavars (ta_var x) = [x]) /\
  (tavars (ta_old x) = [x]) /\
  (tavars (ta_uminus a) = tavars a) /\
  (tavars (ta_plus a1 a2) = tavars a1 ++ tavars a2) /\
  (tavars (ta_minus a1 a2) = tavars a1 ++ tavars a2) /\
  (tavars (ta_times a1 a2) = tavars a1 ++ tavars a2)
End

Definition tbvars_def:
  (tbvars tb_true = []) /\
  (tbvars tb_false = []) /\
  (tbvars (tb_eq a1 a2) = tavars a1 ++ tavars a2) /\
  (tbvars (tb_leq a1 a2) = tavars a1 ++ tavars a2) /\
  (tbvars (tb_neg b) = tbvars b) /\
  (tbvars (tb_and b1 b2) = tbvars b1 ++ tbvars b2)
End

(* the contracts only mention variables in xs *)
Definition ct_over_def:
  ct_over xs (ct:ctable) <=>
    !m p q. ct m = SOME (p, q) ==>
            set (bvars p) SUBSET set xs /\ set (tbvars q) SUBSET set xs
End

(* ------------------------------------------------------------------------ *)
(* States over xs and projection                                            *)
(* ------------------------------------------------------------------------ *)

Definition xs_states_def:
  xs_states xs = {s:state | !v. ~MEM v xs ==> s v = 0}
End

Definition proj_def:
  proj xs (s:state) = \v. if MEM v xs then s v else 0
End

(* s and s' agree outside xs *)
Definition agree_out_def:
  agree_out xs (s:state) (s':state) <=> !v. ~MEM v xs ==> s v = s' v
End

Theorem proj_in:
  !xs s. proj xs s IN xs_states xs
Proof
  rw[proj_def, xs_states_def]
QED

Theorem a_eval_proj:
  !a xs s. set (avars a) SUBSET set xs ==> a_eval a (proj xs s) = a_eval a s
Proof
  Induct >> rw[avars_def, a_eval_def, proj_def]
QED

Theorem b_eval_proj:
  !b xs s. set (bvars b) SUBSET set xs ==>
           (b_eval b (proj xs s) <=> b_eval b s)
Proof
  Induct >> rw[bvars_def, b_eval_def, a_eval_proj]
QED

Theorem ta_eval_proj:
  !a xs s0 s. set (tavars a) SUBSET set xs ==>
              ta_eval a (proj xs s0) (proj xs s) = ta_eval a s0 s
Proof
  Induct >> rw[tavars_def, ta_eval_def, proj_def]
QED

Theorem tb_eval_proj:
  !b xs s0 s. set (tbvars b) SUBSET set xs ==>
              (tb_eval b (proj xs s0) (proj xs s) <=> tb_eval b s0 s)
Proof
  Induct >> rw[tbvars_def, tb_eval_def, ta_eval_proj]
QED

Theorem proj_update:
  !xs x c s. MEM x xs ==> proj xs ((x =+ c) s) = (x =+ c) (proj xs s)
Proof
  rw[proj_def, FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] >> fs[]
QED

Theorem proj_eq_agree:
  !xs s s'. agree_out xs s s' ==> (proj xs s = proj xs s' <=> s = s')
Proof
  rw[proj_def, agree_out_def, FUN_EQ_THM] >> metis_tac[]
QED

Theorem agree_out_update:
  !xs s s' x c. agree_out xs s s' /\ MEM x xs ==>
                agree_out xs s ((x =+ c) s')
Proof
  rw[agree_out_def, APPLY_UPDATE_THM] >> rw[] >> fs[]
QED

(* contracts over xs do not distinguish a state from its projection *)
Definition inv_pre_def:
  inv_pre xs (pre:string -> state -> bool) <=>
    !m s. pre m (proj xs s) <=> pre m s
End

Definition inv_post_def:
  inv_post xs (post:string -> state -> state -> bool) <=>
    !m s0 s. post m (proj xs s0) (proj xs s) <=> post m s0 s
End

Theorem ct_over_inv:
  !xs ct. ct_over xs ct ==> inv_pre xs (cpre ct) /\ inv_post xs (cpost ct)
Proof
  rw[ct_over_def, inv_pre_def, inv_post_def, cpre_def, cpost_def] >>
  Cases_on `ct m` >> rw[] >> PairCases_on `x` >> res_tac >>
  rw[b_eval_proj, tb_eval_proj]
QED

(* ------------------------------------------------------------------------ *)
(* Variables of derived formulas and statements                             *)
(* ------------------------------------------------------------------------ *)

Theorem fvars_subst:
  !f g X. set (fvars (subst_f g X f)) SUBSET set (fvars g) UNION set (fvars f)
Proof
  Induct >> rw[subst_f_def, fvars_def] >>
  TRY (Cases_on `p` >> rw[subst_f_def, fvars_def] >> NO_TAC) >>
  TRY (Cases_on `R` >> rw[subst_f_def, fvars_def] >> NO_TAC) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem fvars_unfold:
  !X f. set (fvars (subst_f (f_mu X f) X f)) SUBSET set (fvars f)
Proof
  rw[] >> qspecl_then [`f`, `f_mu X f`, `X`] mp_tac fvars_subst >>
  rw[fvars_def]
QED

Theorem fvars_chopd:
  !f2 f1. set (fvars (chopd f1 f2)) SUBSET set (fvars f1) UNION set (fvars f2)
Proof
  Induct >> rw[chopd_def, fvars_def] >> fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem MEM_fvars_chopd:
  !f1 f2 x. MEM x (fvars (chopd f1 f2)) ==>
            MEM x (fvars f1) \/ MEM x (fvars f2)
Proof
  rpt strip_tac >> qspecl_then [`f2`, `f1`] mp_tac fvars_chopd >>
  rw[SUBSET_DEF] >> res_tac >> fs[]
QED

Theorem fvars_distr:
  !f. set (fvars (distr f)) SUBSET set (fvars f)
Proof
  recInduct distr_ind >> rw[distr_def, fvars_def] >>
  fs[SUBSET_DEF, fvars_def] >> rpt strip_tac >>
  imp_res_tac MEM_fvars_chopd >> res_tac >> fs[fvars_def]
QED

Theorem svars_seqn:
  !S1 S2. set (svars (seqn S1 S2)) = set (svars S1) UNION set (svars S2)
Proof
  recInduct seqn_ind >> rw[seqn_def, svars_def, EXTENSION] >> metis_tac[]
QED

Theorem svars_norm:
  !S0. set (svars (norm S0)) = set (svars S0)
Proof
  Induct >> rw[norm_def, svars_def, svars_seqn]
QED

(* ------------------------------------------------------------------------ *)
(* Projection of tc, pred, ftc and pcc                                      *)
(* ------------------------------------------------------------------------ *)

Theorem agree_out_refl[simp]:
  !xs s. agree_out xs s s
Proof
  rw[agree_out_def]
QED

Theorem agree_out_assign:
  !xs x c s. MEM x xs ==> agree_out xs ((x =+ c) s) s
Proof
  rw[agree_out_def, APPLY_UPDATE_THM] >> rw[] >> fs[]
QED

Theorem pred_proj:
  !n i f g xs.
    set (fvars f) SUBSET set xs /\ agree_out xs (g (i + 1)) (g i) ==>
    (pred n i f (proj xs o g) <=> pred n i f g)
Proof
  recInduct pred_ind >> rw[pred_def, fvars_def, b_eval_proj]
  >- metis_tac[proj_eq_agree]
  >- (`a_eval a (proj xs (g i)) = a_eval a (g i)` by rw[a_eval_proj] >>
      rw[GSYM proj_update] >> irule proj_eq_agree >>
      fs[agree_out_def, APPLY_UPDATE_THM] >> rw[] >> fs[])
  >- (first_x_assum irule >> metis_tac[fvars_unfold, SUBSET_TRANS])
QED

Theorem tc_proj:
  !xs pre post i S0 g.
    inv_pre xs pre /\ inv_post xs post /\ set (svars S0) SUBSET set xs /\
    tc pre post i S0 g ==> tc pre post i S0 (proj xs o g)
Proof
  gen_tac >> recInduct tc_ind >>
  rw[tc_def, svars_def, a_eval_proj, proj_update, b_eval_proj] >>
  fs[inv_pre_def, inv_post_def, svars_def] >> metis_tac[]
QED

Theorem pcc_proj:
  !xs pre post phi s0 i S0 g.
    inv_pre xs pre /\ inv_post xs post /\
    (!s0 s. phi (proj xs s0) (proj xs s) <=> phi s0 s) /\
    set (svars S0) SUBSET set xs /\
    pcc pre post phi (proj xs s0) i S0 (proj xs o g) ==>
    pcc pre post phi s0 i S0 g
Proof
  gen_tac >> recInduct pcc_ind >>
  rw[pcc_def, svars_def, a_eval_proj, proj_update, b_eval_proj] >>
  fs[inv_pre_def, inv_post_def, svars_def, a_eval_proj, proj_update,
     b_eval_proj] >> rfs[] >>
  `proj xs ((x =+ a_eval a (g i)) (g i)) =
   (x =+ a_eval a (proj xs (g i))) (proj xs (g i))`
    by rw[proj_update, a_eval_proj] >>
  metis_tac[]
QED

Theorem fvars_unfold_sub:
  !xs X f. set (fvars f) SUBSET set xs ==>
           set (fvars (subst_f (f_mu X f) X f)) SUBSET set xs
Proof
  metis_tac[fvars_unfold, SUBSET_TRANS]
QED

Theorem fvars_unfold_chop_sub:
  !xs X f f0.
    set (fvars f) SUBSET set xs /\ set (fvars f0) SUBSET set xs ==>
    set (fvars (distr (f_chop (subst_f (f_mu X f) X f) f0))) SUBSET set xs
Proof
  rw[] >> irule SUBSET_TRANS >> irule_at Any fvars_distr >>
  rw[fvars_def] >> metis_tac[fvars_unfold_sub]
QED

(* ftc_dom over the states over xs, of the projected sequence, together with
   tc gives ftc of the sequence itself: pred is only applied to steps that
   tc constrains, and those do not change variables outside xs. *)
Theorem ftc_proj:
  !xs.
  (!lk pre post n i S0 phi X g.
     inv_pre xs pre /\ inv_post xs post /\
     (!m b. lk m = SOME b ==> set (svars b) SUBSET set xs) /\
     set (svars S0) SUBSET set xs /\ set (fvars phi) SUBSET set xs /\
     tc pre post i S0 g /\
     ftc_dom (xs_states xs) lk pre post n i S0 phi X (proj xs o g) ==>
     ftc lk pre post n i S0 phi X g) /\
  (!lk pre post n i S0 phi X g.
     inv_pre xs pre /\ inv_post xs post /\
     (!m b. lk m = SOME b ==> set (svars b) SUBSET set xs) /\
     set (svars S0) SUBSET set xs /\ set (fvars phi) SUBSET set xs /\
     tc pre post i S0 g /\
     ftc0_dom (xs_states xs) lk pre post n i S0 phi X (proj xs o g) ==>
     ftc0 lk pre post n i S0 phi X g)
Proof
  gen_tac >> ho_match_mp_tac ftc_ind >> rpt conj_tac >> rpt strip_tac >>
  pop_assum mp_tac >> simp[Once ftc_dom_def] >> simp[Once ftc_def] >>
  rpt CASE_TAC >> rw[] >> fs[fvars_def, svars_def, tc_def] >>
  TRY (metis_tac[fvars_unfold_sub, fvars_unfold_chop_sub] >> NO_TAC) >>
  TRY (metis_tac[pred_proj, agree_out_refl, agree_out_assign] >> NO_TAC) >>
  TRY (rfs[b_eval_proj] >> metis_tac[] >> NO_TAC) >>
  `!m s. pre m (proj xs s) <=> pre m s` by fs[inv_pre_def] >> fs[] >>
  TRY (metis_tac[pred_proj, agree_out_refl] >> NO_TAC) >>
  (* the side condition of a first call: project the body's sequence *)
  rename1 `lk m = SOME body` >> rename1 `MEM (m, f_mu Y psi) X` >>
  Cases_on `MEM (m, f_mu Y psi) X` >> fs[] >> rpt strip_tac >>
  qpat_x_assum `!g. tc _ _ 1 _ g /\ _ ==> _` (qspec_then `h` mp_tac) >>
  impl_tac >- fs[] >> disch_then irule >> rw[] >>
  TRY (metis_tac[fvars_unfold_sub] >> NO_TAC) >>
  first_x_assum irule >> rw[proj_in] >> irule tc_proj >> metis_tac[]
QED

(* ------------------------------------------------------------------------ *)
(* End-to-end soundness over the states over xs                             *)
(* ------------------------------------------------------------------------ *)

Theorem norm_lk_svars:
  !xs tbl m b.
    (!m b. MEM (m, b) tbl ==> set (svars b) SUBSET set xs) /\
    norm_lk (ALOOKUP tbl) m = SOME b ==> set (svars b) SUBSET set xs
Proof
  rw[norm_lk_def] >> imp_res_tac ALOOKUP_MEM >> res_tac >> rw[svars_norm]
QED

(* If the verification conditions hold in M with the sort State denoting
   the states over xs, and S, the procedure bodies, phi and the contracts
   only mention variables in xs, the program satisfies the specification. *)
Theorem vc_fols_sound_xs:
  !xs tbl ct n S0 phi relI.
    fv_f phi = [] /\ set (svars S0) SUBSET set xs /\
    (!m b. MEM (m, b) tbl ==> set (svars b) SUBSET set xs) /\
    set (fvars phi) SUBSET set xs /\ ct_over xs ct /\
    (!f v. MEM f (vc_fols tbl ct n S0 phi) /\
           (!x. v x IN (rec_model (xs_states xs)).SDom) ==>
           sholds (rec_model (xs_states xs)) v f) ==>
    Str (ALOOKUP tbl) (K {}) S0 SUBSET fsem relI phi
Proof
  rpt gen_tac >> strip_tac >>
  `inv_pre xs (cpre ct) /\ inv_post xs (cpost ct)` by metis_tac[ct_over_inv] >>
  `sholds (rec_model (xs_states xs)) (K (INL 0))
          (vc_main (ALOOKUP tbl) ct n S0 phi)`
    by (first_x_assum irule >> rw[vc_fols_def]) >>
  `!m b. MEM (m, b) tbl ==>
         sholds (rec_model (xs_states xs)) (K (INL 0))
           (pcc_valid_fol ct m (norm b))`
    by (rw[] >> first_x_assum irule >> rw[vc_fols_def, MEM_MAP] >>
        disj2_tac >> qexists_tac `(m, b)` >> rw[]) >>
  irule vc_sound >> rw[] >>
  qexistsl_tac [`n`, `cpost ct`, `cpre ct`] >> conj_tac
  >- (qpat_x_assum `sholds _ _ (vc_main _ _ _ _ _)` mp_tac >>
      rw[sholds_vc_main] >>
      first_x_assum (qspec_then `proj xs o g` mp_tac) >>
      impl_tac
      >- (rw[proj_in] >> irule tc_proj >> rw[svars_norm]) >>
      strip_tac >>
      irule (cj 1 ftc_proj) >> rw[] >> qexists_tac `xs` >> rw[svars_norm] >>
      metis_tac[norm_lk_svars])
  >- (irule pcc_conforms_norm >>
      rw[pcc_valid_def, norm_lk_def] >- rw[nf_norm] >>
      rename1 `ALOOKUP tbl m = SOME b` >>
      `MEM (m, b) tbl` by metis_tac[ALOOKUP_MEM] >>
      first_x_assum drule >> rw[sholds_pcc_valid_fol] >>
      first_x_assum (qspec_then `proj xs o g` mp_tac) >>
      fs[inv_pre_def, proj_in] >> strip_tac >>
      irule pcc_proj >> rw[] >> qexists_tac `xs` >> rw[svars_norm] >>
      fs[inv_post_def, inv_pre_def] >> res_tac >> fs[])
QED

(* ------------------------------------------------------------------------ *)
(* Id and Sb as conjunctions over xs (Definition 4.1, Section 5.1)          *)
(* ------------------------------------------------------------------------ *)

Definition sconj_def:
  (sconj [] = STrue) /\
  (sconj (f::fs) = SAnd f (sconj fs))
End

(* Id(st, st') = /\_{y in xs} st(y) = st'(y), with the sorts of st, st' *)
Definition Id_xs_def:
  Id_xs xs st st' =
    SAnd (SPred "State" [st])
         (SAnd (SPred "State" [st'])
               (sconj (MAP (\y. SPred "=" [SFn ("sel_" ++ y) [st];
                                            SFn ("sel_" ++ y) [st']]) xs)))
End

(* Sb^a_x(st, st') = st'(x) = a /\ /\_{y in xs \ {x}} st(y) = st'(y), where
   the term vt is the value of a *)
Definition Sb_xs_def:
  Sb_xs xs x vt st st' =
    SAnd (SPred "State" [st])
         (SAnd (SPred "State" [st'])
               (SAnd (SPred "=" [SFn ("sel_" ++ x) [st']; vt])
                     (sconj (MAP (\y. SPred "=" [SFn ("sel_" ++ y) [st'];
                                                  SFn ("sel_" ++ y) [st]])
                                 (FILTER (\y. y <> x) xs)))))
End

(* the variable x of a predicate name "Sb_x" *)
Definition sb_name_def:
  sb_name p = if isPREFIX "Sb_" p then SOME (DROP 3 p) else NONE
End

Theorem sb_name_SOME:
  !p x. sb_name p = SOME x <=> p = "Sb_" ++ x
Proof
  rw[sb_name_def] >> EQ_TAC >> rw[] >>
  TRY (fs[isPREFIX_STRCAT] >> rw[DROP_APPEND] >> NO_TAC) >>
  pop_assum mp_tac >> rpt (CASE_TAC >> simp[])
QED

(* replace the atoms Id and Sb_x (x in xs) by their definitions over xs *)
Definition expand_atoms_def:
  (expand_atoms xs SFalse = SFalse) /\
  (expand_atoms xs STrue = STrue) /\
  (expand_atoms xs (SPred p l) =
     if p = "Id" /\ LENGTH l = 2 then Id_xs xs (EL 0 l) (EL 1 l)
     else
       case sb_name p of
         SOME x =>
           if MEM x xs /\ LENGTH l = 3 then
             Sb_xs xs x (EL 0 l) (EL 1 l) (EL 2 l)
           else SPred p l
       | NONE => SPred p l) /\
  (expand_atoms xs (SNot f) = SNot (expand_atoms xs f)) /\
  (expand_atoms xs (SAnd f1 f2) = SAnd (expand_atoms xs f1) (expand_atoms xs f2)) /\
  (expand_atoms xs (SOr f1 f2) = SOr (expand_atoms xs f1) (expand_atoms xs f2)) /\
  (expand_atoms xs (SImp f1 f2) = SImp (expand_atoms xs f1) (expand_atoms xs f2)) /\
  (expand_atoms xs (SIff f1 f2) = SIff (expand_atoms xs f1) (expand_atoms xs f2)) /\
  (expand_atoms xs (SForall x f) = SForall x (expand_atoms xs f)) /\
  (expand_atoms xs (SExists x f) = SExists x (expand_atoms xs f))
End

Theorem sholds_sconj:
  !M v fs. sholds M v (sconj fs) <=> EVERY (sholds M v) fs
Proof
  Induct_on `fs` >> rw[sconj_def, sholds_def]
QED

Theorem rec_fun_ISL:
  !f l. ISL (rec_fun f l)
Proof
  rw[rec_fun_def] >> rpt CASE_TAC >> rw[]
QED

Theorem stermval_dom:
  !t D v. (!x. v x IN (rec_model D).SDom) ==>
          stermval (rec_model D) v t IN (rec_model D).SDom
Proof
  rw[] >> Cases_on `t` >> rw[stermval_def, rec_fun_ISL] >> fs[]
QED

Theorem xs_states_eq:
  !xs s s'. s IN xs_states xs /\ s' IN xs_states xs ==>
            (s = s' <=> EVERY (\y. s y = s' y) xs)
Proof
  rw[xs_states_def, EVERY_MEM, FUN_EQ_THM] >> metis_tac[]
QED

Theorem xs_states_update_eq:
  !xs x c s s'. s IN xs_states xs /\ s' IN xs_states xs /\ MEM x xs ==>
    (s' = (x =+ c) s <=>
     s' x = c /\ EVERY (\y. s' y = s y) (FILTER (\y. y <> x) xs))
Proof
  rw[xs_states_def, EVERY_MEM, MEM_FILTER, FUN_EQ_THM, APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem sholds_Id_xs:
  !xs v t1 t2.
    (!x. v x IN (rec_model (xs_states xs)).SDom) ==>
    (sholds (rec_model (xs_states xs)) v (Id_xs xs t1 t2) <=>
     rec_pred (xs_states xs) "Id"
       [stermval (rec_model (xs_states xs)) v t1;
        stermval (rec_model (xs_states xs)) v t2])
Proof
  rw[Id_xs_def, sholds_def, sholds_sconj, EVERY_MAP, stermval_def] >>
  `stermval (rec_model (xs_states xs)) v t1 IN
     (rec_model (xs_states xs)).SDom /\
   stermval (rec_model (xs_states xs)) v t2 IN
     (rec_model (xs_states xs)).SDom`
    by (rpt conj_tac >> irule stermval_dom >> rw[]) >>
  Cases_on `stermval (rec_model (xs_states xs)) v t1` >>
  Cases_on `stermval (rec_model (xs_states xs)) v t2` >>
  fs[rec_pred_def, rec_fun_def, isPREFIX_STRCAT, DROP_APPEND] >>
  metis_tac[xs_states_eq]
QED

Theorem sholds_Sb_xs:
  !xs x v t0 t1 t2.
    MEM x xs /\ (!x. v x IN (rec_model (xs_states xs)).SDom) ==>
    (sholds (rec_model (xs_states xs)) v (Sb_xs xs x t0 t1 t2) <=>
     rec_pred (xs_states xs) ("Sb_" ++ x)
       [stermval (rec_model (xs_states xs)) v t0;
        stermval (rec_model (xs_states xs)) v t1;
        stermval (rec_model (xs_states xs)) v t2])
Proof
  rw[Sb_xs_def, sholds_def, sholds_sconj, EVERY_MAP, stermval_def] >>
  `stermval (rec_model (xs_states xs)) v t0 IN
     (rec_model (xs_states xs)).SDom /\
   stermval (rec_model (xs_states xs)) v t1 IN
     (rec_model (xs_states xs)).SDom /\
   stermval (rec_model (xs_states xs)) v t2 IN
     (rec_model (xs_states xs)).SDom`
    by (rpt conj_tac >> irule stermval_dom >> rw[]) >>
  Cases_on `stermval (rec_model (xs_states xs)) v t0` >>
  Cases_on `stermval (rec_model (xs_states xs)) v t1` >>
  Cases_on `stermval (rec_model (xs_states xs)) v t2` >>
  fs[rec_pred_def, rec_fun_def, isPREFIX_STRCAT, DROP_APPEND] >>
  metis_tac[xs_states_update_eq]
QED

Theorem upd_dom:
  !xs v x a.
    (!y. ISL (v y) \/ OUTR (v y) IN xs_states xs) /\
    (ISL a \/ OUTR a IN xs_states xs) ==>
    !y. ISL (((x =+ a) v) y) \/ OUTR (((x =+ a) v) y) IN xs_states xs
Proof
  rw[APPLY_UPDATE_THM] >> rw[]
QED

(* on the states over xs, the expanded atoms mean the same *)
Theorem sholds_expand_atoms:
  !xs f v.
    (!x. v x IN (rec_model (xs_states xs)).SDom) ==>
    (sholds (rec_model (xs_states xs)) v (expand_atoms xs f) <=>
     sholds (rec_model (xs_states xs)) v f)
Proof
  gen_tac >> Induct >>
  rw[expand_atoms_def, sholds_def] >>
  TRY (rpt (first_x_assum (qspec_then `v` mp_tac)) >> rw[] >> NO_TAC) >>
  TRY (gvs[LENGTH_EQ_NUM_compute] >> rw[sholds_Id_xs] >> NO_TAC) >>
  TRY (qmatch_goalsub_rename_tac `sb_name p` >>
       Cases_on `sb_name p` >> fs[sholds_def, sb_name_SOME] >>
       rw[sholds_def] >> gvs[LENGTH_EQ_NUM_compute] >> rw[sholds_Sb_xs] >>
       NO_TAC) >>
  EQ_TAC >> rw[] >> fs[] >> metis_tac[upd_dom]
QED

(* ------------------------------------------------------------------------ *)
(* End-to-end soundness in the form of the Z3 encoding                      *)
(* ------------------------------------------------------------------------ *)

(* the verification conditions with Id and Sb over xs *)
Definition vc_fols_xs_def:
  vc_fols_xs xs tbl ct n S0 phi = MAP (expand_atoms xs) (vc_fols tbl ct n S0 phi)
End

(* If the verification conditions, with Id and Sb expanded over xs, hold in
   M with State denoting the states over xs (in the thesis: tuples over
   xs, as Z3 records), the program satisfies the specification. *)
Theorem vc_fols_xs_sound:
  !xs tbl ct n S0 phi relI.
    fv_f phi = [] /\ set (svars S0) SUBSET set xs /\
    (!m b. MEM (m, b) tbl ==> set (svars b) SUBSET set xs) /\
    set (fvars phi) SUBSET set xs /\ ct_over xs ct /\
    (!f v. MEM f (vc_fols_xs xs tbl ct n S0 phi) /\
           (!x. v x IN (rec_model (xs_states xs)).SDom) ==>
           sholds (rec_model (xs_states xs)) v f) ==>
    Str (ALOOKUP tbl) (K {}) S0 SUBSET fsem relI phi
Proof
  rw[vc_fols_xs_def, MEM_MAP, PULL_EXISTS] >>
  irule vc_fols_sound_xs >> rw[] >>
  qexistsl_tac [`ct`, `n`, `xs`] >> rw[] >>
  TRY (res_tac >> NO_TAC) >>
  qspecl_then [`xs`, `f`, `v`] mp_tac sholds_expand_atoms >> fs[]
QED

(* the same, with satisfaction in the folcompactness model *)
Theorem vc_fols_xs_sound_fol:
  !xs tbl ct n S0 phi relI.
    fv_f phi = [] /\ set (svars S0) SUBSET set xs /\
    (!m b. MEM (m, b) tbl ==> set (svars b) SUBSET set xs) /\
    set (fvars phi) SUBSET set xs /\ ct_over xs ct /\
    (!f. MEM f (vc_fols_xs xs tbl ct n S0 phi) ==>
         smodel2model (rec_model (xs_states xs)) satisfies {sform2form f}) ==>
    Str (ALOOKUP tbl) (K {}) S0 SUBSET fsem relI phi
Proof
  rpt strip_tac >> irule vc_fols_xs_sound >> rpt conj_tac >> TRY (fs[] >> NO_TAC) >>
  qexistsl_tac [`ct`, `n`, `xs`] >> rpt strip_tac >> TRY (res_tac >> NO_TAC) >>
  res_tac >> fs[satisfies_sholds]
QED

(* ftc implies ftc_dom D: the side conditions of ftc_dom are weaker *)
Theorem ftc_ftc_dom:
  !D.
  (!lk pre post n i S0 phi X g.
     ftc lk pre post n i S0 phi X g ==> ftc_dom D lk pre post n i S0 phi X g) /\
  (!lk pre post n i S0 phi X g.
     ftc0 lk pre post n i S0 phi X g ==> ftc0_dom D lk pre post n i S0 phi X g)
Proof
  gen_tac >> ho_match_mp_tac ftc_ind >> rpt conj_tac >> rpt strip_tac >>
  pop_assum mp_tac >> simp[Once ftc_def] >> simp[Once ftc_dom_def] >>
  rpt CASE_TAC >> rw[] >> fs[] >> metis_tac[]
QED
