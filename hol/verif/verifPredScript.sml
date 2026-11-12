(* The induced predicate pred_i of a trace formula (thesis Definition
   4.17, Lemma 4.19) and the distribution of chop over disjunction
   (thesis Definition 4.23, Lemma 4.24, corrected). *)

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
(* Definition 4.23 and Lemma 4.24, for disjunction only                     *)
(* ------------------------------------------------------------------------ *)

(* The thesis also distributes chop over conjunction, which does not
   preserve the semantics (see verifCounterexamples). *)
Definition distr_def:
  (distr (f_chop (f_or f1 f2) f3) =
     f_or (distr (f_chop f1 f3)) (distr (f_chop f2 f3))) /\
  (distr (f_chop f1 f2) = f_chop (distr f1) (distr f2)) /\
  (distr (f_and f1 f2) = f_and (distr f1) (distr f2)) /\
  (distr (f_or f1 f2) = f_or (distr f1) (distr f2)) /\
  (distr (f_mu X f) = f_mu X (distr f)) /\
  (distr f = f)
Termination
  WF_REL_TAC `measure f_size` >> rw[f_size_def]
End

(* Lemma 4.24 *)
Theorem distr_sem:
  !f relI V. f_sem relI V (distr f) = f_sem relI V f
Proof
  recInduct distr_ind >> rw[] >>
  fs[distr_def, f_sem_def, chop_union_l]
QED

Theorem fv_f_distr:
  !f. set (fv_f (distr f)) = set (fv_f f)
Proof
  recInduct distr_ind >>
  rw[distr_def, fv_f_def, EXTENSION, list_minus_thm] >> metis_tac[]
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
