(* Strongest trace formulas (Definition 4.6) and their characterisation
   (Theorem 4.9), with Corollary 5.5. *)

open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory alistTheory combinTheory pairTheory
     ottTheory tracesTheory tracesSemTheory tracesSosTheory tracesSoundTheory;

val _ = new_theory "tracesStf";

(* ------------------------------------------------------------------------ *)
(* Definition 4.6                                                           *)
(* ------------------------------------------------------------------------ *)

(* stf(X, S) of Figure 4. The recursion variable X_m of procedure m is
   named m, as the statement variable Y_m is. The procedures in the list X
   already have a fixed-point binder around the current position. *)
Definition stf_def:
  (stf tbl X S_skip = f_rel R_Id) /\
  (stf tbl X (S_assign x a) = f_rel (R_Sb a x)) /\
  (stf tbl X (S_seq S1 S2) = f_chop (stf tbl X S1) (stf tbl X S2)) /\
  (stf tbl X (S_ifelse b S1 S2) =
     f_or (f_and (f_state (p_b b)) (f_chop (f_rel R_Id) (stf tbl X S1)))
          (f_and (f_state (p_b (b_neg b)))
                 (f_chop (f_rel R_Id) (stf tbl X S2)))) /\
  (stf tbl X (S_call m) =
     case ALOOKUP tbl m of
       SOME body =>
         if MEM m X then f_chop (f_rel R_Id) (f_recvar m)
         else f_chop (f_rel R_Id) (f_mu m (stf tbl (m::X) body))
     | NONE => f_chop (f_rel R_Id) (f_recvar m)) /\
  (stf tbl X (S_var Y) = f_recvar Y)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\(tbl,X,S0). (CARD (set (MAP FST tbl) DIFF set X), S_size S0))` >>
  rpt strip_tac >> simp_tac std_ss [LEX_DEF] >>
  disj1_tac >> irule CARD_PSUBSET >>
  rw[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
  qexists_tac `m` >> imp_res_tac ALOOKUP_MEM >> rw[MEM_MAP] >>
  qexists_tac `(m,body)` >> rw[]
End

(* ------------------------------------------------------------------------ *)
(* Auxiliary facts about the semantics                                      *)
(* ------------------------------------------------------------------------ *)

Theorem f_sem_Id_chop:
  !relI V f. f_sem relI V (f_chop (f_rel R_Id) f) = dup (f_sem relI V f)
Proof
  rw[f_sem_def, R_sem_def] >> rw[chop_id]
QED

Theorem f_sem_guard_Id_chop:
  !relI V b f.
    f_sem relI V (f_and (f_state (p_b b)) (f_chop (f_rel R_Id) f)) =
    restrict b (dup (f_sem relI V f))
Proof
  rw[Once f_sem_def, f_sem_Id_chop] >>
  rw[f_sem_def, p_sem_def, restrict_def, dup_def, EXTENSION] >>
  metis_tac[]
QED

Theorem rho0_app:
  !lk iv n. rho0 lk iv n = H lk iv (rho0 lk iv) n
Proof
  metis_tac[rho0_fixpoint]
QED

Theorem rho0_ovr_out:
  !D lk iv n. n NOTIN D ==>
    rho0 (ovr D lk) iv n =
    case lk n of SOME b => dup (Str0 (rho0 (ovr D lk) iv) iv b) | NONE => {}
Proof
  rw[] >> simp[Once rho0_app] >> rw[H_def, ovr_def]
QED

Theorem rho0_mono_iv:
  !lk iv1 iv2. ileq iv1 iv2 ==> ileq (rho0 lk iv1) (rho0 lk iv2)
Proof
  rw[] >> irule rho0_least >>
  `ileq (H lk iv1 (rho0 lk iv2)) (H lk iv2 (rho0 lk iv2))`
    suffices_by metis_tac[rho0_fixpoint] >>
  rw[ileq_def, H_def] >> CASE_TAC >> rw[] >>
  irule dup_mono >> irule Str0_mono >> fs[ileq_def]
QED

Theorem Str_mono_iv:
  !lk iv1 iv2 S0. ileq iv1 iv2 ==> Str lk iv1 S0 SUBSET Str lk iv2 S0
Proof
  rw[Str_def] >> irule Str0_mono >> rw[rho0_mono_iv]
QED

(* fixed-point induction for the system with m treated as a variable *)
Theorem bekic_prefix:
  !lk D m body iv g.
    m NOTIN D /\ lk m = SOME body /\
    (!n b. lk n = SOME b ==> var_free b) /\
    Str0 (rho0 (ovr (m INSERT D) lk) ((m =+ g) iv)) ((m =+ g) iv) body
      SUBSET g ==>
    Str0 (rho0 (ovr D lk) iv) iv body SUBSET g
Proof
  rw[] >>
  qabbrev_tac `r = rho0 (ovr (m INSERT D) lk) ((m =+ g) iv)` >>
  `var_free body` by metis_tac[] >>
  `Str0 r iv body SUBSET g` by metis_tac[Str0_var_free] >>
  `ileq (rho0 (ovr D lk) iv) r`
    suffices_by metis_tac[Str0_mono, ileq_def, SUBSET_REFL, SUBSET_TRANS] >>
  `!n. r n = H (ovr (m INSERT D) lk) ((m =+ g) iv) r n`
    by metis_tac[rho0_fixpoint] >>
  irule rho0_least >> simp[ileq_def] >> qx_gen_tac `n` >>
  qpat_x_assum `!n. r n = _` (qspec_then `n` SUBST1_TAC) >>
  Cases_on `n = m`
  >- (fs[H_def, ovr_def, Str0_def, APPLY_UPDATE_THM] >>
      irule dup_mono >> rw[]) >>
  Cases_on `n IN D`
  >- fs[H_def, ovr_def, Str0_def, APPLY_UPDATE_THM] >>
  fs[H_def, ovr_def] >> CASE_TAC >> rw[] >>
  `var_free x` by metis_tac[] >>
  metis_tac[Str0_var_free, SUBSET_REFL, dup_mono]
QED

(* Bekic's principle, one procedure at a time: the least interpretation of
   the whole system at m is obtained from the least fixed point in m of the
   system where m is treated as a statement variable. *)
Theorem rho0_bekic:
  !lk D m body iv.
    m NOTIN D /\ lk m = SOME body /\
    (!n b. lk n = SOME b ==> var_free b) ==>
    mu_sem (\g. Str (ovr (m INSERT D) lk) ((m =+ g) iv) body) =
    Str (ovr D lk) iv body
Proof
  rpt strip_tac >>
  `var_free body` by metis_tac[] >>
  rw[Str_def] >>
  irule SUBSET_ANTISYM >> reverse conj_tac
  >- (irule mu_sem_greatest >> rw[] >> irule bekic_prefix >> metis_tac[]) >>
  irule mu_sem_least >> BETA_TAC >>
  qabbrev_tac `r0 = rho0 (ovr D lk) iv` >>
  `!n. n IN D ==> r0 n = dup (iv n)` by metis_tac[rho0_ovr] >>
  `!n. n NOTIN D ==>
       r0 n = case lk n of SOME b => dup (Str0 r0 iv b) | NONE => {}`
    by (rw[Abbr `r0`] >> metis_tac[rho0_ovr_out]) >>
  qabbrev_tac `iv' = (m =+ Str0 r0 iv body) iv` >>
  `ileq (rho0 (ovr (m INSERT D) lk) iv') r0`
    by (irule rho0_least >> rw[ileq_def, H_def, ovr_def] >>
        Cases_on `m' = m` >- fs[Abbr `iv'`, Str0_def, APPLY_UPDATE_THM] >>
        Cases_on `m' IN D`
        >- fs[Abbr `iv'`, Str0_def, APPLY_UPDATE_THM] >>
        res_tac >> fs[] >> CASE_TAC >> rw[] >>
        metis_tac[Str0_var_free, SUBSET_REFL]) >>
  `Str0 r0 iv' body = Str0 r0 iv body` by metis_tac[Str0_var_free] >>
  metis_tac[Str0_mono, ileq_def, SUBSET_REFL]
QED

(* procedures in D whose variables denote their actual semantics can be
   interpreted either way *)
Theorem rho0_ovr_solution:
  !lk D iv.
    (!n b. lk n = SOME b ==> var_free b) /\
    (!n. n IN D ==> ?b. lk n = SOME b /\ iv n = Str lk iv b) ==>
    rho0 (ovr D lk) iv = rho0 lk iv
Proof
  rpt strip_tac >>
  qabbrev_tac `r = rho0 lk iv` >>
  qabbrev_tac `r' = rho0 (ovr D lk) iv` >>
  `!n. r n = case lk n of SOME b => dup (Str0 r iv b) | NONE => {}`
    by (rw[Abbr `r`] >> simp[Once rho0_app] >> rw[H_def]) >>
  `!n. n IN D ==> r' n = dup (iv n)` by metis_tac[rho0_ovr] >>
  `!n. n NOTIN D ==>
       r' n = case lk n of SOME b => dup (Str0 r' iv b) | NONE => {}`
    by (rw[Abbr `r'`] >> metis_tac[rho0_ovr_out]) >>
  `ileq r' r`
    by (qunabbrev_tac `r'` >> irule rho0_least >>
        rw[ileq_def, H_def, ovr_def] >>
        Cases_on `m IN D` >> fs[Str0_def]
        >- (res_tac >> fs[Str_def] >> qunabbrev_tac `r` >> rw[]) >>
        metis_tac[SUBSET_REFL]) >>
  `ileq r r'`
    by (qunabbrev_tac `r` >> irule rho0_least >>
        rw[ileq_def, H_def] >>
        Cases_on `m IN D` >> fs[]
        >- (res_tac >> fs[Str_def] >> irule dup_mono >>
            metis_tac[Str0_mono, ileq_def, SUBSET_REFL]) >>
        metis_tac[SUBSET_REFL]) >>
  CONV_TAC FUN_EQ_CONV >> gen_tac >> irule SUBSET_ANTISYM >> fs[ileq_def]
QED

Theorem Str_ovr_solution:
  !lk D iv S0.
    (!n b. lk n = SOME b ==> var_free b) /\
    (!n. n IN D ==> ?b. lk n = SOME b /\ iv n = Str lk iv b) ==>
    Str (ovr D lk) iv S0 = Str lk iv S0
Proof
  rw[] >> `rho0 (ovr D lk) iv = rho0 lk iv` suffices_by rw[Str_def] >>
  irule rho0_ovr_solution >> metis_tac[]
QED

(* ------------------------------------------------------------------------ *)
(* Theorem 4.9                                                              *)
(* ------------------------------------------------------------------------ *)

(* Generalisation of Theorem 4.9 to open strongest trace formulas: the
   recursion variables X_m for m in X denote the procedures m, which are
   interpreted as statement variables. This replaces the modal equation
   systems of the paper's proof (Appendix A.2). *)
Theorem stf_sem_ovr:
  !tbl X S0 relI V.
    tbl_var_free tbl /\
    (!m. ~MEM m X /\ ALOOKUP tbl m = NONE ==> V m = {}) ==>
    f_sem relI V (stf tbl X S0) = Str (ovr (set X) (ALOOKUP tbl)) V S0
Proof
  ho_match_mp_tac stf_ind >> rpt conj_tac >> rpt gen_tac
  >- (rw[stf_def, f_sem_def, Str_def, Str0_def, R_sem_def, EXTENSION] >>
      metis_tac[])
  >- (rw[stf_def, f_sem_def, Str_def, Str0_def, R_sem_def, EXTENSION] >>
      metis_tac[])
  >- (rw[stf_def, Once f_sem_def] >> fs[Str_def, Str0_def])
  >- (rw[stf_def, Once f_sem_def, f_sem_guard_Id_chop] >>
      fs[Str_def, Str0_def])
  >- (strip_tac >> rpt strip_tac >>
      simp[stf_def, Str_def, Str0_def] >>
      Cases_on `ALOOKUP tbl m` >> simp[f_sem_Id_chop]
      >- (Cases_on `MEM m X`
          >- simp[f_sem_def, rho0_ovr] >>
          rw[f_sem_def, rho0_ovr_out, dup_def]) >>
      rename1 `ALOOKUP tbl m = SOME body` >>
      Cases_on `MEM m X` >> simp[f_sem_Id_chop]
      >- simp[f_sem_def, rho0_ovr] >>
      simp[rho0_ovr_out] >> simp[f_sem_def] >>
      AP_TERM_TAC >>
      `(\g. f_sem relI ((m =+ g) V) (stf tbl (m::X) body)) =
       (\g. Str (ovr (m INSERT set X) (ALOOKUP tbl)) ((m =+ g) V) body)`
        by (CONV_TAC FUN_EQ_CONV >> gen_tac >> BETA_TAC >>
            `set (m::X) = m INSERT set X` by rw[] >>
            pop_assum (SUBST1_TAC o SYM) >>
            first_x_assum irule >> rw[APPLY_UPDATE_THM]) >>
      pop_assum SUBST1_TAC >>
      `Str (ovr (set X) (ALOOKUP tbl)) V body =
       Str0 (rho0 (ovr (set X) (ALOOKUP tbl)) V) V body` by rw[Str_def] >>
      pop_assum (SUBST1_TAC o SYM) >>
      irule rho0_bekic >> fs[tbl_var_free_def] >> metis_tac[]) >>
  rw[stf_def, f_sem_def, Str_def, Str0_def]
QED

(* Theorem 4.9: ||stf(S)|| = Str[[S]] *)
Theorem stf_Str:
  !tbl S0 relI iv.
    tbl_var_free tbl /\ var_free S0 ==>
    fsem relI (stf tbl [] S0) = Str (ALOOKUP tbl) iv S0
Proof
  rw[fsem_def] >>
  `f_sem relI (K {}) (stf tbl [] S0) =
   Str (ovr (set []) (ALOOKUP tbl)) (K {}) S0`
    by (irule stf_sem_ovr >> rw[]) >>
  fs[ovr_empty] >> metis_tac[Str_eq_Ssos]
QED

(* ... and, via Theorem 3.2, ||stf(S)|| = S_sos[[S]] *)
Theorem stf_Ssos:
  !tbl S0 relI.
    tbl_var_free tbl /\ var_free S0 ==>
    fsem relI (stf tbl [] S0) = Ssos tbl S0
Proof
  metis_tac[stf_Str, Str_eq_Ssos]
QED

(* Corollary 5.5: stf(S) entails exactly the valid formulas for S *)
Theorem stf_strongest:
  !tbl S0 relI f.
    tbl_var_free tbl /\ var_free S0 ==>
    (valid relI (ALOOKUP tbl) {} S0 f <=>
     fsem relI (stf tbl [] S0) SUBSET fsem relI f)
Proof
  rw[valid_def, G_holds_def, G_dom_def, ovr_empty] >>
  metis_tac[stf_Str]
QED

(* ------------------------------------------------------------------------ *)
(* Unfolding strongest trace formulas                                       *)
(* ------------------------------------------------------------------------ *)

(* The fixed-point formula created for a call of m *)
Theorem stf_mu_sem:
  !tbl X m body relI V.
    tbl_var_free tbl /\ ALOOKUP tbl m = SOME body /\ ~MEM m X /\
    (!n. ~MEM n X /\ ALOOKUP tbl n = NONE ==> V n = {}) ==>
    f_sem relI V (f_mu m (stf tbl (m::X) body)) =
    Str (ovr (set X) (ALOOKUP tbl)) V body
Proof
  rw[f_sem_def] >>
  `(\g. f_sem relI ((m =+ g) V) (stf tbl (m::X) body)) =
   (\g. Str (ovr (m INSERT set X) (ALOOKUP tbl)) ((m =+ g) V) body)`
    by (CONV_TAC FUN_EQ_CONV >> gen_tac >> BETA_TAC >>
        `set (m::X) = m INSERT set X` by rw[] >>
        pop_assum (SUBST1_TAC o SYM) >>
        irule stf_sem_ovr >> rw[APPLY_UPDATE_THM]) >>
  pop_assum SUBST1_TAC >>
  irule rho0_bekic >> fs[tbl_var_free_def] >> metis_tac[]
QED

(* Interpreting X_n by the fixed-point formula for n is the same as
   interpreting n by the procedure table *)
Theorem Str_ovr_unfold:
  !tbl n body S0 relI iv.
    tbl_var_free tbl /\ ALOOKUP tbl n = SOME body /\ var_free S0 ==>
    Str (ovr {n} (ALOOKUP tbl))
        ((n =+ f_sem relI (K {}) (f_mu n (stf tbl [n] body))) (K {})) S0 =
    Str (ALOOKUP tbl) iv S0
Proof
  rpt strip_tac >>
  `var_free body` by metis_tac[tbl_var_free_def] >>
  `f_sem relI (K {}) (f_mu n (stf tbl [n] body)) =
   Str (ALOOKUP tbl) (K {}) body`
    by (`Str (ALOOKUP tbl) (K {}) body =
         Str (ovr (set []) (ALOOKUP tbl)) (K {}) body` by rw[ovr_empty] >>
        pop_assum SUBST1_TAC >> irule stf_mu_sem >> rw[]) >>
  pop_assum SUBST1_TAC >>
  `Str (ovr {n} (ALOOKUP tbl)) ((n =+ Str (ALOOKUP tbl) (K {}) body) (K {})) S0 =
   Str (ALOOKUP tbl) ((n =+ Str (ALOOKUP tbl) (K {}) body) (K {})) S0`
    by (irule Str_ovr_solution >> rw[APPLY_UPDATE_THM]
        >- metis_tac[tbl_var_free_def] >>
        metis_tac[Str_eq_Ssos]) >>
  metis_tac[Str_eq_Ssos]
QED

(* Unfolding the fixed point of stf(n()) in stf(X_n, S) does not change
   the semantics, which is the one of S *)
Theorem stf_unfold_Str:
  !tbl n body S0 relI iv.
    tbl_var_free tbl /\ ALOOKUP tbl n = SOME body /\ var_free S0 /\
    fv_f (f_mu n (stf tbl [n] body)) = [] ==>
    fsem relI (subst_f (f_mu n (stf tbl [n] body)) n (stf tbl [n] S0)) =
    Str (ALOOKUP tbl) iv S0
Proof
  rw[fsem_def, f_sem_subst] >>
  `f_sem relI ((n =+ f_sem relI (K {}) (f_mu n (stf tbl [n] body))) (K {}))
     (stf tbl [n] S0) =
   Str (ovr (set [n]) (ALOOKUP tbl))
     ((n =+ f_sem relI (K {}) (f_mu n (stf tbl [n] body))) (K {})) S0`
    by (irule stf_sem_ovr >> rw[APPLY_UPDATE_THM]) >>
  fs[] >> metis_tac[Str_ovr_unfold]
QED

(* ... and similarly for the fixed-point formula of another procedure m *)
Theorem stf_unfold_mu:
  !tbl n body m bm relI.
    tbl_var_free tbl /\ ALOOKUP tbl n = SOME body /\
    ALOOKUP tbl m = SOME bm /\ m <> n /\
    fv_f (f_mu n (stf tbl [n] body)) = [] ==>
    fsem relI (subst_f (f_mu n (stf tbl [n] body)) n
                 (f_mu m (stf tbl [m; n] bm))) =
    fsem relI (f_mu m (stf tbl [m] bm))
Proof
  rw[fsem_def, f_sem_subst] >>
  `var_free bm` by metis_tac[tbl_var_free_def] >>
  `f_sem relI ((n =+ f_sem relI (K {}) (f_mu n (stf tbl [n] body))) (K {}))
     (f_mu m (stf tbl [m; n] bm)) =
   Str (ovr (set [n]) (ALOOKUP tbl))
     ((n =+ f_sem relI (K {}) (f_mu n (stf tbl [n] body))) (K {})) bm`
    by (irule stf_mu_sem >> rw[APPLY_UPDATE_THM]) >>
  `f_sem relI (K {}) (f_mu m (stf tbl [m] bm)) =
   Str (ovr (set []) (ALOOKUP tbl)) (K {}) bm`
    by (irule stf_mu_sem >> rw[]) >>
  fs[ovr_empty] >> metis_tac[Str_ovr_unfold]
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.8                                                              *)
(* ------------------------------------------------------------------------ *)

(* down {if x > 0 then x := x - 2; down() else skip} (Example 2.3), with
   x > 0 written as ~(x <= 0) *)
Overload x_gt_0 = ``b_neg (b_leq (a_var "x") (a_num 0))``
Overload down_tbl =
  ``[("down", S_ifelse x_gt_0
                (S_seq (S_assign "x" (a_minus (a_var "x") (a_num 2)))
                       (S_call "down"))
                S_skip)]``

(* Id ^ mu X_down. (x > 0 /\ Id ^ Sb_x^(x-2) ^ Id ^ X_down) \/
                   (x <= 0 /\ Id ^ Id),
   where x <= 0 is ~(x > 0) *)
Theorem example_4_8:
  stf down_tbl [] (S_call "down") =
  f_chop (f_rel R_Id)
    (f_mu "down"
       (f_or (f_and (f_state (p_b x_gt_0))
                    (f_chop (f_rel R_Id)
                       (f_chop (f_rel (R_Sb (a_minus (a_var "x") (a_num 2)) "x"))
                               (f_chop (f_rel R_Id) (f_recvar "down")))))
             (f_and (f_state (p_b (b_neg x_gt_0)))
                    (f_chop (f_rel R_Id) (f_rel R_Id)))))
Proof
  EVAL_TAC
QED

val _ = export_theory ();
