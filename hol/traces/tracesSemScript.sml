(* Denotational semantics of Rec statements (Section 3, Definition 3.1)
   and of trace formulas (Section 4, Definition 4.2). *)

Theory tracesSem
Ancestors
  pred_set list rich_list alist combin pair ott traces

Type state = ``:string -> int``
Type trace = ``:state list``
Type tset = ``:trace set``

(* ------------------------------------------------------------------------ *)
(* Operators on trace sets                                                  *)
(* ------------------------------------------------------------------------ *)

(* A|b: traces whose first state satisfies b *)
Definition restrict_def:
  restrict b (A:tset) = {t | t IN A /\ ?s r. t = s::r /\ b_eval b s}
End

(* #A: duplicate the first state *)
Definition dup_def:
  dup (A:tset) = {t | ?s r. t = s::s::r /\ s::r IN A}
End

(* A ^ B: concatenation fusing the last state of A with the first of B *)
Definition chop_def:
  chop (A:tset) (B:tset) =
    {t | ?l1 s l2. t = l1 ++ [s] ++ l2 /\ l1 ++ [s] IN A /\ s::l2 IN B}
End

Theorem restrict_mono:
  !b A B. A SUBSET B ==> restrict b A SUBSET restrict b B
Proof
  rw[restrict_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem dup_mono:
  !A B. A SUBSET B ==> dup A SUBSET dup B
Proof
  rw[dup_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem chop_mono:
  !A A' B B'. A SUBSET A' /\ B SUBSET B' ==> chop A B SUBSET chop A' B'
Proof
  rw[chop_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem chop_pairs:
  !P A. chop {t | ?s s'. t = [s;s'] /\ P s s'} A =
        {t | ?s s' r. t = s::s'::r /\ P s s' /\ s'::r IN A}
Proof
  rw[chop_def, EXTENSION, EQ_IMP_THM, PULL_EXISTS] >>
  TRY (Cases_on `l1` >> fs[] >> Cases_on `t` >> fs[] >> metis_tac[]) >>
  TRY (qexists_tac `[s]` >> rw[] >> metis_tac[])
QED

Theorem chop_id:
  !A. chop {t | ?s. t = [s;s]} A = dup A
Proof
  rw[chop_def, dup_def, EXTENSION, EQ_IMP_THM, PULL_EXISTS] >>
  TRY (Cases_on `l1` >> fs[] >> Cases_on `t` >> fs[] >> metis_tac[]) >>
  TRY (qexists_tac `[s]` >> rw[] >> metis_tac[])
QED

(* ------------------------------------------------------------------------ *)
(* Least fixed points on procedure interpretations (Knaster-Tarski)         *)
(* ------------------------------------------------------------------------ *)

Type interp = ``:string -> tset``

Definition ileq_def:
  ileq (r1:interp) r2 = !m. r1 m SUBSET r2 m
End

Definition imono_def:
  imono (H:interp -> interp) = !r1 r2. ileq r1 r2 ==> ileq (H r1) (H r2)
End

Definition ilfp_def:
  ilfp (H:interp -> interp) =
    \m. {t | !r. ileq (H r) r ==> t IN r m}
End

Theorem ilfp_least:
  !H r. ileq (H r) r ==> ileq (ilfp H) r
Proof
  rw[ileq_def, ilfp_def, SUBSET_DEF]
QED

Theorem ilfp_prefix:
  !H. imono H ==> ileq (H (ilfp H)) (ilfp H)
Proof
  rw[] >> simp[Once ileq_def] >> rw[SUBSET_DEF] >>
  simp[ilfp_def] >> rw[] >>
  `ileq (ilfp H) r` by metis_tac[ilfp_least] >>
  `ileq (H (ilfp H)) (H r)` by metis_tac[imono_def] >>
  fs[ileq_def, SUBSET_DEF]
QED

Theorem ilfp_fixpoint:
  !H. imono H ==> H (ilfp H) = ilfp H
Proof
  rw[] >>
  `ileq (H (ilfp H)) (ilfp H)` by metis_tac[ilfp_prefix] >>
  `ileq (H (H (ilfp H))) (H (ilfp H))` by metis_tac[imono_def] >>
  `ileq (ilfp H) (H (ilfp H))` by metis_tac[ilfp_least] >>
  fs[ileq_def, FUN_EQ_THM] >> metis_tac[SUBSET_ANTISYM]
QED

(* ------------------------------------------------------------------------ *)
(* Statement semantics (Figure 2), relativized on interpretations rho of    *)
(* procedure names and iv of statement variables                            *)
(* ------------------------------------------------------------------------ *)

Definition Str0_def:
  (Str0 (rho:interp) (iv:interp) S_skip = {t | ?s. t = [s;s]}) /\
  (Str0 rho iv (S_assign x a) = {t | ?s. t = [s; (x =+ a_eval a s) s]}) /\
  (Str0 rho iv (S_seq S1 S2) = chop (Str0 rho iv S1) (Str0 rho iv S2)) /\
  (Str0 rho iv (S_ifelse b S1 S2) =
     restrict b (dup (Str0 rho iv S1)) UNION
     restrict (b_neg b) (dup (Str0 rho iv S2))) /\
  (Str0 rho iv (S_call m) = rho m) /\
  (Str0 rho iv (S_var Y) = iv Y)
End

Theorem Str0_mono:
  !S rho1 rho2 iv1 iv2.
    ileq rho1 rho2 /\ ileq iv1 iv2 ==>
    Str0 rho1 iv1 S SUBSET Str0 rho2 iv2 S
Proof
  `!b A1 A2 B1 B2. A1 SUBSET A2 /\ B1 SUBSET B2 ==>
      restrict b (dup A1) UNION restrict (b_neg b) (dup B1) SUBSET
      restrict b (dup A2) UNION restrict (b_neg b) (dup B2)`
    by (rw[SUBSET_DEF, restrict_def, dup_def] >> metis_tac[]) >>
  Induct >> rw[Str0_def] >> fs[ileq_def] >> metis_tac[chop_mono]
QED

Theorem Str0_seq_skip:
  !rho iv S. Str0 rho iv (S_seq S_skip S) = dup (Str0 rho iv S)
Proof
  rw[Str0_def, chop_id]
QED

(* statements without statement variables *)
Definition var_free_def:
  (var_free (S_seq S1 S2) = (var_free S1 /\ var_free S2)) /\
  (var_free (S_ifelse b S1 S2) = (var_free S1 /\ var_free S2)) /\
  (var_free (S_var Y) = F) /\
  (var_free _ = T)
End

Theorem Str0_var_free:
  !S rho iv1 iv2. var_free S ==> Str0 rho iv1 S = Str0 rho iv2 S
Proof
  Induct >> rw[Str0_def, var_free_def] >> metis_tac[]
QED

(* procedure lookup functions; for a table T this is ALOOKUP T *)
Type lookup = ``:string -> S option``

(* the transformer H of Definition 3.1 *)
Definition H_def:
  H (lk:lookup) iv rho m =
    case lk m of SOME body => dup (Str0 rho iv body) | NONE => {}
End

Theorem H_mono:
  !lk iv. imono (H lk iv)
Proof
  rw[imono_def] >> simp[Once ileq_def] >> rw[H_def] >>
  CASE_TAC >> rw[] >> irule dup_mono >> irule Str0_mono >> rw[ileq_def]
QED

Definition rho0_def:
  rho0 lk iv = ilfp (H lk iv)
End

Theorem rho0_fixpoint:
  !lk iv. H lk iv (rho0 lk iv) = rho0 lk iv
Proof
  metis_tac[rho0_def, ilfp_fixpoint, H_mono]
QED

Theorem rho0_least:
  !lk iv r. ileq (H lk iv r) r ==> ileq (rho0 lk iv) r
Proof
  metis_tac[rho0_def, ilfp_least]
QED

(* Str[[S]]_I, relative to the least interpretation of the procedures *)
Definition Str_def:
  Str lk iv S = Str0 (rho0 lk iv) iv S
End

Theorem Str_call:
  !lk iv m S. lk m = SOME S ==> Str lk iv (S_call m) = dup (Str lk iv S)
Proof
  rw[Str_def, Str0_def] >>
  `rho0 lk iv m = H lk iv (rho0 lk iv) m` by metis_tac[rho0_fixpoint] >>
  rw[H_def]
QED

(* ------------------------------------------------------------------------ *)
(* Trace formula semantics (Figure 3)                                       *)
(* ------------------------------------------------------------------------ *)

Definition p_sem_def:
  p_sem (p_b b) s = b_eval b s
End

(* interpretation of the relation symbols (Section 4.2); other relation
   symbols Q are interpreted by relI *)
Definition R_sem_def:
  (R_sem (relI:string -> state -> state -> bool) R_Id s s' = (s' = s)) /\
  (R_sem relI (R_Sb a x) s s' = (s' = (x =+ a_eval a s) s)) /\
  (R_sem relI (R_other q) s s' = relI q s s')
End

(* least fixed point of a set transformer: intersection of its pre-fixed points *)
Definition mu_sem_def:
  mu_sem (Fn:tset -> tset) = BIGINTER {g | Fn g SUBSET g}
End

Theorem mu_sem_least:
  !Fn g. Fn g SUBSET g ==> mu_sem Fn SUBSET g
Proof
  rw[mu_sem_def, SUBSET_DEF, IN_BIGINTER] >> metis_tac[]
QED

Theorem mu_sem_greatest:
  !Fn A. (!g. Fn g SUBSET g ==> A SUBSET g) ==> A SUBSET mu_sem Fn
Proof
  rw[mu_sem_def, SUBSET_DEF, IN_BIGINTER] >> metis_tac[]
QED

Theorem mu_sem_mono:
  !F1 F2. (!g. F1 g SUBSET F2 g) ==> mu_sem F1 SUBSET mu_sem F2
Proof
  rw[] >> irule mu_sem_greatest >> rw[] >> irule mu_sem_least >>
  metis_tac[SUBSET_TRANS]
QED

Theorem mu_sem_fixpoint:
  !Fn. (!g1 g2. g1 SUBSET g2 ==> Fn g1 SUBSET Fn g2) ==>
       Fn (mu_sem Fn) = mu_sem Fn
Proof
  rw[] >>
  `Fn (mu_sem Fn) SUBSET mu_sem Fn`
    by (irule mu_sem_greatest >> rw[] >>
        `mu_sem Fn SUBSET g` by metis_tac[mu_sem_least] >>
        metis_tac[SUBSET_TRANS]) >>
  `mu_sem Fn SUBSET Fn (mu_sem Fn)` by metis_tac[mu_sem_least] >>
  metis_tac[SUBSET_ANTISYM]
QED

Definition f_sem_def:
  (f_sem relI (V:string -> tset) (f_state p) =
     {t | ?s r. t = s::r /\ p_sem p s}) /\
  (f_sem relI V (f_rel R) = {t | ?s s'. t = [s;s'] /\ R_sem relI R s s'}) /\
  (f_sem relI V (f_recvar X) = V X) /\
  (f_sem relI V (f_and f1 f2) = f_sem relI V f1 INTER f_sem relI V f2) /\
  (f_sem relI V (f_or f1 f2) = f_sem relI V f1 UNION f_sem relI V f2) /\
  (f_sem relI V (f_chop f1 f2) = chop (f_sem relI V f1) (f_sem relI V f2)) /\
  (f_sem relI V (f_mu X f) = mu_sem (\g. f_sem relI ((X =+ g) V) f))
End

(* semantics of (closed) formulas: ||phi|| *)
Definition fsem_def:
  fsem relI f = f_sem relI (K {}) f
End

Theorem ileq_update:
  !V1 V2 X g. ileq V1 V2 ==> ileq ((X =+ g) V1) ((X =+ g) V2)
Proof
  rw[ileq_def, APPLY_UPDATE_THM] >> rw[]
QED

Theorem f_sem_mono:
  !f relI V1 V2. ileq V1 V2 ==> f_sem relI V1 f SUBSET f_sem relI V2 f
Proof
  Induct >> rw[f_sem_def] >>
  FIRST [fs[ileq_def] >> NO_TAC,
         irule mu_sem_mono >> rw[] >> metis_tac[ileq_update],
         metis_tac[chop_mono],
         fs[SUBSET_DEF] >> metis_tac[]]
QED

Theorem f_sem_mono_update:
  !relI V X f g1 g2. g1 SUBSET g2 ==>
    f_sem relI ((X =+ g1) V) f SUBSET f_sem relI ((X =+ g2) V) f
Proof
  rw[] >> irule f_sem_mono >> rw[ileq_def, APPLY_UPDATE_THM] >> rw[]
QED

(* the least fixed-point property (used for Proposition 4.3) *)
Theorem f_sem_mu_fixpoint:
  !relI V X f.
    f_sem relI V (f_mu X f) =
    f_sem relI ((X =+ f_sem relI V (f_mu X f)) V) f
Proof
  rw[f_sem_def] >>
  qspec_then `\g. f_sem relI ((X =+ g) V) f` mp_tac mu_sem_fixpoint >>
  impl_tac >- (rw[] >> metis_tac[f_sem_mono_update]) >>
  rw[]
QED

(* the semantics depends only on the free recursion variables *)
Theorem f_sem_fv:
  !f relI V1 V2. (!X. MEM X (fv_f f) ==> V1 X = V2 X) ==>
                 f_sem relI V1 f = f_sem relI V2 f
Proof
  Induct >> rw[f_sem_def, fv_f_def] >>
  TRY (metis_tac[]) >>
  AP_TERM_TAC >> CONV_TAC FUN_EQ_CONV >> gen_tac >> BETA_TAC >>
  first_x_assum irule >> rw[APPLY_UPDATE_THM] >>
  first_x_assum irule >> rw[list_minus_thm]
QED

Theorem f_sem_closed:
  !f relI V. fv_f f = [] ==> f_sem relI V f = fsem relI f
Proof
  rw[fsem_def] >> irule f_sem_fv >> rw[]
QED

(* substitution lemma for closed formulas *)
Theorem f_sem_subst:
  !f g X relI V.
    fv_f g = [] ==>
    f_sem relI V (subst_f g X f) = f_sem relI ((X =+ f_sem relI V g) V) f
Proof
  Induct >> rw[f_sem_def, subst_f_def, APPLY_UPDATE_THM] >> fs[UPDATE_EQ] >>
  AP_TERM_TAC >> CONV_TAC FUN_EQ_CONV >> gen_tac >> BETA_TAC >>
  simp[f_sem_closed] >> metis_tac[UPDATE_COMMUTES]
QED

(* Proposition 4.3 (fixed-point unfolding), for closed fixed-point formulas *)
Theorem fsem_unfold:
  !relI X f. fv_f (f_mu X f) = [] ==>
             fsem relI (subst_f (f_mu X f) X f) = fsem relI (f_mu X f)
Proof
  rw[fsem_def, f_sem_subst] >> metis_tac[f_sem_mu_fixpoint]
QED

Theorem fsem_Id_chop:
  !relI f. fsem relI (f_chop (f_rel R_Id) f) = dup (fsem relI f)
Proof
  rw[fsem_def, f_sem_def, R_sem_def, EXTENSION] >> rw[chop_id, dup_def]
QED

