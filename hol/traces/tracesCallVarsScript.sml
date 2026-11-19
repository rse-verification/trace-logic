(* The rule (Call) with statement variables Y_m that are not identified with
   the procedure names m.

   In the formalization, the statement variable Y_m of a procedure m is the
   name m itself. An Isabelle/HOL formalization of the paper
   (https://github.com/OybekBabaev/Mechanization-of-Judgments-for-Trace-Formulas-in-Isabelle-HOL)
   instead keeps a separate variable Y_m in each antecedent entry, and its
   corrected rule (Call) then needs two extra side conditions: Y_m is fresh
   for the antecedent, and the procedure names in the antecedent are distinct.

   This theory makes the choice of variables a parameter: a function nu maps
   each procedure name m to its variable Y_m = nu m. Since nu is a function,
   each procedure has exactly one variable, which is what the distinctness
   condition ensures. Freshness becomes the premise
   !n. n IN G_dom G ==> nu n <> nu m of call_sound_nu. With nu = I, all
   definitions are the ones of tracesSound, freshness is the side condition
   m NOTIN G_dom G that (Call) already has, and call_sound follows
   (call_sound_from_nu). The freshness premise cannot be dropped
   (call_nu_freshness_necessary). Only validity is generalized; the
   inductive calculus calc is unchanged. *)

Theory tracesCallVars
Ancestors
  pred_set list alist combin pair ott traces tracesSem tracesSos tracesSound

(* ------------------------------------------------------------------------ *)
(* Validity with variables nu m                                             *)
(* ------------------------------------------------------------------------ *)

Definition ovr_nu_def:
  ovr_nu (nu:string -> string) D (lk:lookup) =
    \m. if m IN D then SOME (S_var (nu m)) else lk m
End

Definition G_holds_nu_def:
  G_holds_nu relI (nu:string -> string) (G:G) iv =
    !n f. (n,f) IN G ==> iv (nu n) SUBSET fsem relI f
End

Definition valid_nu_def:
  valid_nu relI lk nu G S0 f =
    !iv. G_holds_nu relI nu G iv ==>
         Str (ovr_nu nu (G_dom G) lk) iv S0 SUBSET fsem relI f
End

(* replace each call m() with skip;Y_m where Y_m = nu m and m is in ms *)
Definition subst_calls_nu_def:
  (subst_calls_nu nu ms S_skip = S_skip) /\
  (subst_calls_nu nu ms (S_assign x a) = S_assign x a) /\
  (subst_calls_nu nu ms (S_seq S1 S2) =
    S_seq (subst_calls_nu nu ms S1) (subst_calls_nu nu ms S2)) /\
  (subst_calls_nu nu ms (S_ifelse b S1 S2) =
    S_ifelse b (subst_calls_nu nu ms S1) (subst_calls_nu nu ms S2)) /\
  (subst_calls_nu nu ms (S_call m) =
    if m IN ms then S_seq S_skip (S_var (nu m)) else S_call m) /\
  (subst_calls_nu nu ms (S_var Y) = S_var Y)
End

(* ------------------------------------------------------------------------ *)
(* With nu = I, these are the definitions of tracesSound                    *)
(* ------------------------------------------------------------------------ *)

Theorem ovr_nu_I:
  !D lk. ovr_nu I D lk = ovr D lk
Proof
  rw[ovr_nu_def, ovr_def]
QED

Theorem G_holds_nu_I:
  !relI G iv. G_holds_nu relI I G iv = G_holds relI G iv
Proof
  rw[G_holds_nu_def, G_holds_def]
QED

Theorem valid_nu_I:
  !relI lk G S0 f. valid_nu relI lk I G S0 f = valid relI lk G S0 f
Proof
  rw[valid_nu_def, valid_def, ovr_nu_I, G_holds_nu_I]
QED

Theorem subst_calls_nu_I:
  !ms S0. subst_calls_nu I ms S0 = subst_calls ms S0
Proof
  gen_tac >> Induct >> rw[subst_calls_nu_def, subst_calls_def]
QED

(* with Y_m = m, freshness of Y_m is the side condition m NOTIN dom G *)
Theorem fresh_I:
  !D m. (!n. n IN D ==> I n <> I m) <=> m NOTIN D
Proof
  metis_tac[I_THM]
QED

(* ------------------------------------------------------------------------ *)
(* The rule (Call)                                                          *)
(* ------------------------------------------------------------------------ *)

Theorem G_holds_nu_insert:
  !relI nu n f G iv.
    G_holds_nu relI nu ((n,f) INSERT G) iv <=>
    iv (nu n) SUBSET fsem relI f /\ G_holds_nu relI nu G iv
Proof
  rw[G_holds_nu_def] >> metis_tac[]
QED

Theorem rho0_ovr_nu:
  !nu D lk iv n. n IN D ==> rho0 (ovr_nu nu D lk) iv n = dup (iv (nu n))
Proof
  rw[] >>
  `rho0 (ovr_nu nu D lk) iv n = H (ovr_nu nu D lk) iv (rho0 (ovr_nu nu D lk) iv) n`
    by metis_tac[rho0_fixpoint] >>
  rw[H_def, ovr_nu_def, Str0_def]
QED

Theorem subst_calls_nu_Str0:
  !S0 nu ms rho iv. (!n. n IN ms ==> rho n = dup (iv (nu n))) ==>
                    Str0 rho iv (subst_calls_nu nu ms S0) = Str0 rho iv S0
Proof
  Induct >> rw[subst_calls_nu_def, Str0_def, Str0_seq_skip]
QED

(* fixed-point induction as in call_fixpoint_induction; freshness is
   needed already here, since the other procedures n in D are interpreted
   by the variables nu n, which the update at nu m must leave unchanged *)
Theorem call_fixpoint_induction_nu:
  !nu lk D m body iv g.
    m NOTIN D /\ (!n. n IN D ==> nu n <> nu m) /\ lk m = SOME body /\
    (!n b. lk n = SOME b ==> var_free b) /\
    Str0 (rho0 (ovr_nu nu (m INSERT D) lk) ((nu m =+ g) iv)) iv body
      SUBSET g ==>
    rho0 (ovr_nu nu D lk) iv m SUBSET dup g
Proof
  rw[] >>
  qabbrev_tac `r = rho0 (ovr_nu nu (m INSERT D) lk) ((nu m =+ g) iv)` >>
  `!n. r n = H (ovr_nu nu (m INSERT D) lk) ((nu m =+ g) iv) r n`
    by metis_tac[rho0_fixpoint] >>
  `ileq (H (ovr_nu nu D lk) iv r) r`
    by (simp[ileq_def] >> qx_gen_tac `n` >>
        qpat_x_assum `!n. r n = _` (qspec_then `n` SUBST1_TAC) >>
        Cases_on `n = m`
        >- (fs[H_def, ovr_nu_def, Str0_def, APPLY_UPDATE_THM] >>
            irule dup_mono >> rw[]) >>
        Cases_on `n IN D`
        >- (`nu n <> nu m` by metis_tac[] >>
            fs[H_def, ovr_nu_def, Str0_def, APPLY_UPDATE_THM]) >>
        fs[H_def, ovr_nu_def] >> CASE_TAC >> rw[] >>
        `var_free x` by metis_tac[] >>
        metis_tac[Str0_var_free, SUBSET_REFL, dup_mono]) >>
  `ileq (rho0 (ovr_nu nu D lk) iv) r` by metis_tac[rho0_least] >>
  `r m = dup ((nu m =+ g) iv (nu m))`
    by (qunabbrev_tac `r` >> irule rho0_ovr_nu >> rw[]) >>
  fs[ileq_def, APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem call_sound_nu:
  !relI tbl nu G m body f.
    tbl_var_free tbl /\ ALOOKUP tbl m = SOME body /\ m NOTIN G_dom G /\
    (!n. n IN G_dom G ==> nu n <> nu m) /\
    valid_nu relI (ALOOKUP tbl) nu ((m,f) INSERT G)
      (subst_calls_nu nu (G_dom ((m,f) INSERT G)) body) f ==>
    valid_nu relI (ALOOKUP tbl) nu G (S_call m) (f_chop (f_rel R_Id) f)
Proof
  rw[valid_nu_def, fsem_Id_chop, G_dom_insert] >>
  rw[Str_def, Str0_def] >>
  irule call_fixpoint_induction_nu >>
  fs[tbl_var_free_def] >> rw[] >- metis_tac[] >>
  qabbrev_tac `iv' = (nu m =+ fsem relI f) iv` >>
  `G_holds_nu relI nu ((m,f) INSERT G) iv'`
    by (rw[G_holds_nu_insert, Abbr `iv'`, APPLY_UPDATE_THM] >>
        fs[G_holds_nu_def, G_dom_def, APPLY_UPDATE_THM] >> rw[] >>
        metis_tac[IN_IMAGE, FST]) >>
  first_x_assum drule >> rw[Str_def] >>
  `!n. n IN m INSERT G_dom G ==>
       rho0 (ovr_nu nu (m INSERT G_dom G) (ALOOKUP tbl)) iv' n =
       dup (iv' (nu n))`
    by metis_tac[rho0_ovr_nu] >>
  qabbrev_tac `r = rho0 (ovr_nu nu (m INSERT G_dom G) (ALOOKUP tbl)) iv'` >>
  `Str0 r iv' (subst_calls_nu nu (m INSERT G_dom G) body) = Str0 r iv' body`
    by (irule subst_calls_nu_Str0 >> metis_tac[IN_INSERT]) >>
  `Str0 r iv' body = Str0 r iv body` by metis_tac[Str0_var_free] >>
  metis_tac[]
QED

(* call_sound is the instance nu = I, where freshness is m NOTIN G_dom G *)
Theorem call_sound_from_nu:
  !relI tbl G m body f.
    tbl_var_free tbl /\ ALOOKUP tbl m = SOME body /\ m NOTIN G_dom G /\
    valid relI (ALOOKUP tbl) ((m,f) INSERT G)
      (subst_calls (G_dom ((m,f) INSERT G)) body) f ==>
    valid relI (ALOOKUP tbl) G (S_call m) (f_chop (f_rel R_Id) f)
Proof
  rw[GSYM valid_nu_I, GSYM subst_calls_nu_I] >>
  irule call_sound_nu >> rw[fresh_I] >> metis_tac[]
QED

(* ------------------------------------------------------------------------ *)
(* Freshness cannot be dropped                                              *)
(* ------------------------------------------------------------------------ *)

(* T = { m {n()} }, Gamma = { Y_n : true }, and Y_m = Y_n = Y. The premise
   of (Call) holds: its antecedent Y : false, Y : true forces Y to be empty.
   The conclusion m() : Id^false fails when Y is interpreted by the traces
   of skip. All other side conditions of call_sound_nu hold. *)
Theorem call_nu_freshness_necessary:
  tbl_var_free [("m", S_call "n")] /\
  ALOOKUP [("m", S_call "n")] "m" = SOME (S_call "n") /\
  "m" NOTIN G_dom {("n", f_state (p_b b_true))} /\
  ~(!n. n IN G_dom {("n", f_state (p_b b_true))} ==> K "Y" n <> K "Y" "m") /\
  !relI.
    valid_nu relI (ALOOKUP [("m", S_call "n")]) (K "Y")
      (("m", f_state (p_b b_false)) INSERT {("n", f_state (p_b b_true))})
      (subst_calls_nu (K "Y")
         (G_dom (("m", f_state (p_b b_false)) INSERT
                 {("n", f_state (p_b b_true))}))
         (S_call "n"))
      (f_state (p_b b_false)) /\
    ~valid_nu relI (ALOOKUP [("m", S_call "n")]) (K "Y")
      {("n", f_state (p_b b_true))} (S_call "m")
      (f_chop (f_rel R_Id) (f_state (p_b b_false)))
Proof
  rpt conj_tac
  >- (rw[tbl_var_free_def, ALOOKUP_def] >> rw[var_free_def])
  >- rw[ALOOKUP_def]
  >- rw[G_dom_def]
  >- rw[G_dom_def]
  >- (gen_tac >> conj_tac
      >- (rw[valid_nu_def, G_dom_insert, G_dom_def, subst_calls_nu_def,
             G_holds_nu_insert, Str_def, Str0_seq_skip] >>
          fs[Str0_def, fsem_eqs, p_sem_def, b_eval_def, SUBSET_DEF, dup_def] >>
          metis_tac[])
      >- (rw[valid_nu_def, G_holds_nu_def, G_dom_def] >>
          qexists_tac `K {t | ?s. t = [s;s]}` >>
          rw[fsem_eqs, p_sem_def, b_eval_def, SUBSET_DEF] >>
          qabbrev_tac `lk = ovr_nu (K "Y") {"n"} (ALOOKUP [("m",S_call "n")])` >>
          qabbrev_tac `iv0 : interp = K {t | ?s. t = [s;s]}` >>
          `rho0 lk iv0 "m" = H lk iv0 (rho0 lk iv0) "m"`
            by metis_tac[rho0_fixpoint] >>
          `H lk iv0 (rho0 lk iv0) "m" = dup (rho0 lk iv0 "n")`
            by rw[Abbr `lk`, H_def, ovr_nu_def, ALOOKUP_def, Str0_def] >>
          `rho0 lk iv0 "n" = dup (iv0 "Y")`
            by (qunabbrev_tac `lk` >>
                mp_tac (Q.SPECL [`K "Y"`, `{"n"}`] rho0_ovr_nu) >> rw[]) >>
          rw[Str_def, Str0_def, fsem_Id_chop, fsem_eqs, p_sem_def, b_eval_def,
             SUBSET_DEF, dup_def, Abbr `iv0`] >>
          qexists_tac `[K 0; K 0; K 0; K 0]` >> rw[chop_def]))
QED
