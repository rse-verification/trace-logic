(* The induced predicate pred_i of a trace formula (thesis Definition
   4.17, Lemma 4.19), expand (thesis Definition 4.20, Lemma 4.21) and the
   distribution of chop over disjunction (thesis Definition 4.23, Lemma
   4.24, corrected). *)

Theory verifPred
Ancestors
  arithmetic pred_set list combin ott traces tracesSem verifChop

(* ------------------------------------------------------------------------ *)
(* Free variables and closed formulas                                       *)
(* ------------------------------------------------------------------------ *)

Theorem fv_f_subst:
  !g. fv_f g = [] ==>
      !f X. set (fv_f (subst_f g X f)) = set (fv_f f) DELETE X
Proof
  gen_tac >> strip_tac >> Induct >>
  rw[subst_f_def, fv_f_def, EXTENSION, list_minus_thm] >>
  metis_tac[]
QED

(* unfolding a closed fixed-point formula gives a closed formula *)
Theorem closed_unfold:
  !X f. fv_f (f_mu X f) = [] ==> fv_f (subst_f (f_mu X f) X f) = []
Proof
  rw[] >> drule fv_f_subst >>
  disch_then (qspecl_then [`f`, `X`] assume_tac) >>
  `!y. MEM y (fv_f f) ==> y = X`
    by (rw[] >> CCONTR_TAC >>
        `MEM y (list_minus (fv_f f) [X])` by rw[list_minus_thm] >>
        metis_tac[MEM, fv_f_def]) >>
  Cases_on `fv_f (subst_f (f_mu X f) X f)` >> fs[EXTENSION] >> metis_tac[]
QED

Theorem fsem_and:
  !relI f1 f2. fsem relI (f_and f1 f2) = fsem relI f1 INTER fsem relI f2
Proof
  rw[fsem_def, f_sem_def]
QED

Theorem fsem_or:
  !relI f1 f2. fsem relI (f_or f1 f2) = fsem relI f1 UNION fsem relI f2
Proof
  rw[fsem_def, f_sem_def]
QED

Theorem fsem_chop:
  !relI f1 f2. fsem relI (f_chop f1 f2) = chop (fsem relI f1) (fsem relI f2)
Proof
  rw[fsem_def, f_sem_def]
QED

(* ------------------------------------------------------------------------ *)
(* Definition 4.17 and Lemma 4.19                                           *)
(* ------------------------------------------------------------------------ *)

(* pred_i(phi) as a predicate on state sequences g. Unfolding mu X. phi
   need not terminate (e.g. for mu X. X), so pred takes fuel n, spent at
   each unfolding; without fuel it is false. Relation symbols other than
   Id and Sb give false, as in the thesis. *)
Definition pred_def:
  (pred (n:num) (i:num) (f_state (p_b b)) (g:num -> state) = b_eval b (g i)) /\
  (pred n i (f_rel R_Id) g = (g (i + 1) = g i)) /\
  (pred n i (f_rel (R_Sb a x)) g = (g (i + 1) = (x =+ a_eval a (g i)) (g i))) /\
  (pred n i (f_rel (R_other q)) g = F) /\
  (pred n i (f_recvar X) g = F) /\
  (pred n i (f_and f1 f2) g = (pred n i f1 g /\ pred n i f2 g)) /\
  (pred n i (f_or f1 f2) g = (pred n i f1 g \/ pred n i f2 g)) /\
  (pred n i (f_chop f1 f2) g = F) /\
  (pred 0 i (f_mu X f) g = F) /\
  (pred (SUC n) i (f_mu X f) g = pred n i (subst_f (f_mu X f) X f) g)
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\(n,i,f,g). (n, f_size f))` >>
  rw[f_size_def]
End

(* Lemma 4.19 *)
Theorem pred_sound:
  !n i f g relI. pred n i f g /\ fv_f f = [] ==> [g i; g (i + 1)] IN fsem relI f
Proof
  recInduct pred_ind >>
  rw[pred_def, fsem_and, fsem_or] >>
  TRY (rw[fsem_def, f_sem_def, p_sem_def, R_sem_def] >> NO_TAC) >>
  TRY (fs[fv_f_def] >> NO_TAC) >>
  `fv_f (subst_f (f_mu X f) X f) = []` by metis_tac[closed_unfold] >>
  metis_tac[fsem_unfold]
QED

(* ------------------------------------------------------------------------ *)
(* Definition 4.20 and Lemma 4.21                                           *)
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

(* Lemma 4.21 *)
Theorem expand_sem:
  !f relI V. f_sem relI V (expand f) = f_sem relI V f
Proof
  Induct >> rw[expand_def, f_sem_def] >>
  rw[EXTENSION, IN_chop, EQ_IMP_THM] >> rw[] >>
  Cases_on `t1` >> fs[] >>
  qexists_tac `s::(h::t ++ TL t2)` >> rw[] >> fs[] >>
  Cases_on `t` >> fs[]
QED

Theorem fv_f_expand:
  !f. set (fv_f (expand f)) = set (fv_f f)
Proof
  Induct >> rw[expand_def, fv_f_def, EXTENSION, list_minus_thm] >>
  metis_tac[]
QED

Theorem fsem_expand:
  !relI f. fsem relI (expand f) = fsem relI f
Proof
  rw[fsem_def, expand_sem]
QED

(* ------------------------------------------------------------------------ *)
(* Definition 4.23 and Lemma 4.24, corrected                                *)
(* ------------------------------------------------------------------------ *)

(* phi1 ^ phi2, distributed over the disjunctions at the top of phi2 *)
Definition chopd_def:
  (chopd f1 (f_or f2 f3) = f_or (chopd f1 f2) (chopd f1 f3)) /\
  (chopd f1 f2 = f_chop f1 f2)
End

(* a weight under which re-grouping a chop to the right decreases *)
Definition chopw_def:
  (chopw (f_chop f1 f2) = 2 * chopw f1 + chopw f2 + 1) /\
  (chopw (f_and f1 f2) = chopw f1 + chopw f2 + 1) /\
  (chopw (f_or f1 f2) = chopw f1 + chopw f2 + 1) /\
  (chopw (f_mu X f) = chopw f + 1) /\
  (chopw _ = 1:num)
End

(* The thesis also distributes chop over conjunction, which does not
   preserve the semantics (see verifCounterexamples and verifFtcThesis).
   Instead, distr re-groups chops to the right, as the thesis does
   implicitly by writing chop sequences without brackets, and also
   distributes chop over disjunction in its right operand. *)
Definition distr_def:
  (distr (f_chop (f_or f1 f2) f3) =
     f_or (distr (f_chop f1 f3)) (distr (f_chop f2 f3))) /\
  (distr (f_chop (f_chop f1 f2) f3) = distr (f_chop f1 (f_chop f2 f3))) /\
  (distr (f_chop f1 f2) = chopd (distr f1) (distr f2)) /\
  (distr (f_and f1 f2) = f_and (distr f1) (distr f2)) /\
  (distr (f_or f1 f2) = f_or (distr f1) (distr f2)) /\
  (distr (f_mu X f) = f_mu X (distr f)) /\
  (distr f = f)
Termination
  WF_REL_TAC `measure chopw` >> rw[chopw_def]
End

Theorem chopd_sem:
  !f2 f1 relI V.
    f_sem relI V (chopd f1 f2) = chop (f_sem relI V f1) (f_sem relI V f2)
Proof
  Induct >> rw[chopd_def, f_sem_def, chop_union_r]
QED

Theorem fv_f_chopd:
  !f2 f1. set (fv_f (chopd f1 f2)) = set (fv_f f1) UNION set (fv_f f2)
Proof
  Induct >> rw[chopd_def, fv_f_def, EXTENSION] >> metis_tac[]
QED

(* Lemma 4.24 *)
Theorem distr_sem:
  !f relI V. f_sem relI V (distr f) = f_sem relI V f
Proof
  recInduct distr_ind >> rw[] >>
  fs[distr_def, f_sem_def, chopd_sem, chop_union_l, chop_assoc]
QED

Theorem fv_f_distr:
  !f. set (fv_f (distr f)) = set (fv_f f)
Proof
  recInduct distr_ind >>
  rw[distr_def, fv_f_def, fv_f_chopd, EXTENSION, list_minus_thm] >>
  metis_tac[]
QED

Theorem closed_distr:
  !f. fv_f f = [] ==> fv_f (distr f) = []
Proof
  metis_tac[fv_f_distr, LIST_TO_SET_EQ_EMPTY]
QED

Theorem fsem_distr:
  !relI f. fsem relI (distr f) = fsem relI f
Proof
  rw[fsem_def, distr_sem]
QED
