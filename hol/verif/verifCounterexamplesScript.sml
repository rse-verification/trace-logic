(* Counterexamples to definitions and results of the thesis as stated,
   which justify the corrections in the formalization. *)

Theory verifCounterexamples
Ancestors
  arithmetic pred_set list combin alist traces tracesSem verifChop verifEff
  verifNorm verifTc verifPred

(* ------------------------------------------------------------------------ *)
(* Definition 4.8: effective traces abstract only a call at the top level   *)
(* ------------------------------------------------------------------------ *)

(* S_eff[[S]] as defined in the thesis *)
Definition Seff_thesis_def:
  Seff_thesis lk S0 =
    case S0 of
      S_call m => {[HD t; HD t; LAST t] | t IN Str lk (K {}) (S_call m)}
    | _ => Str lk (K {}) S0
End

Overload x1_x2_tbl =
  ``ALOOKUP [("m", S_seq (S_assign "x" (a_num 1)) (S_assign "x" (a_num 2)))]``

Theorem Str_assign_in:
  !lk iv x a s. [s; (x =+ a_eval a s) s] IN Str lk iv (S_assign x a)
Proof
  rw[Str_def, Str0_def]
QED

(* m { x := 1; x := 2 } conforms with <true, x = 2> *)
Theorem x1_x2_conforms:
  conforms x1_x2_tbl (\m s. T) (\m s s'. s' "x" = 2)
Proof
  rw[conforms_def] >> drule Str_call_cases >> rw[] >>
  fs[Str_def, Str0_def, IN_chop] >> rw[] >>
  Cases_on `m = "m"` >> fs[] >> rw[] >> fs[Str_def, Str0_def, IN_chop] >>
  rw[] >> rw[APPLY_UPDATE_THM, a_eval_def]
QED

(* Lemma 4.16 fails for skip; m() with the thesis's effective traces:
   the state after x := 1 inside the call is taken as the final state of
   the call. *)
Theorem Seff_thesis_counterexample:
  ?lk pre post S0 u g.
    conforms lk pre post /\ nf S0 /\ u IN Seff_thesis lk S0 /\
    agree 1 u g /\ ~tc pre post 1 S0 g
Proof
  qabbrev_tac `s0 = (K 0):state` >>
  qabbrev_tac `s1 = ("x" =+ 1) s0` >>
  qabbrev_tac `s2 = ("x" =+ 2) s1` >>
  qspecl_then [`[s0; s0; s0; s1; s2]`, `1`] strip_assume_tac agree_exists >>
  qexistsl_tac [`x1_x2_tbl`, `\m s. T`, `\m s s'. s' "x" = 2`,
                `S_seq S_skip (S_call "m")`, `[s0; s0; s0; s1; s2]`, `g`] >>
  rw[x1_x2_conforms, nf_def, atomic_def, Seff_thesis_def]
  >- (`[s0; s0; s1; s2] IN Str x1_x2_tbl (K {}) (S_call "m")`
        by (`x1_x2_tbl "m" = SOME (S_seq (S_assign "x" (a_num 1))
                                          (S_assign "x" (a_num 2)))`
              by rw[] >>
            drule Str_call >> disch_then (qspec_then `K {}` SUBST1_TAC) >>
            rw[dup_def] >> rw[Str_def, Str0_def, IN_chop] >>
            qexistsl_tac [`[s0; s1]`, `[s1; s2]`] >>
            rw[Abbr `s1`, Abbr `s2`, a_eval_def]) >>
      fs[Str_def, Str0_def] >> rw[IN_chop] >>
      qexistsl_tac [`[s0; s0]`, `[s0; s0; s1; s2]`] >> rw[])
  >- (fs[agree_def, tc_def] >> rw[Abbr `s1`, APPLY_UPDATE_THM])
QED

(* ------------------------------------------------------------------------ *)
(* The shape condition after Lemma 4.11 is too weak for Lemma 4.16          *)
(* ------------------------------------------------------------------------ *)

(* The statement (skip; if true then x := 1 else skip); x := 2 has no
   conditional as a left operand of a sequence, but tc re-associates it
   into one, and its trace then fails tc. *)
Theorem no_if_left_counterexample:
  ?lk pre post S0 t u g.
    conforms lk pre post /\ no_if_left S0 /\ eff lk S0 t u /\
    agree 1 u g /\ ~tc pre post 1 S0 g
Proof
  qabbrev_tac `s0 = (K 0):state` >>
  qabbrev_tac `s1 = ("x" =+ 1) s0` >>
  qabbrev_tac `s2 = ("x" =+ 2) s1` >>
  qspecl_then [`[s0; s0; s0; s1; s2]`, `1`] strip_assume_tac agree_exists >>
  qexistsl_tac [`K NONE`, `\m s. T`, `\m s s'. T`,
                `S_seq (S_seq S_skip (S_ifelse b_true (S_assign "x" (a_num 1))
                                                    S_skip))
                       (S_assign "x" (a_num 2))`,
                `[s0; s0; s0; s1; s2]`, `[s0; s0; s0; s1; s2]`, `g`] >>
  rw[no_if_left_def]
  >- (rw[conforms_def] >> CCONTR_TAC >> fs[] >>
      drule Str_call_cases >> rw[])
  >- (`eff (K NONE) (S_assign "x" (a_num 1)) [s0; s1] [s0; s1]`
        by metis_tac[eff_rules, a_eval_def] >>
      `eff (K NONE) (S_assign "x" (a_num 2)) [s1; s2] [s1; s2]`
        by metis_tac[eff_rules, a_eval_def] >>
      `eff (K NONE) (S_ifelse b_true (S_assign "x" (a_num 1)) S_skip)
           [s0; s0; s1] [s0; s0; s1]`
        by (irule (cj 4 eff_rules) >> rw[b_eval_def]) >>
      `eff (K NONE)
           (S_seq S_skip (S_ifelse b_true (S_assign "x" (a_num 1)) S_skip))
           ([s0; s0] ++ TL [s0; s0; s1]) ([s0; s0] ++ TL [s0; s0; s1])`
        by (irule (cj 3 eff_rules) >> rw[eff_rules]) >>
      `eff (K NONE)
           (S_seq (S_seq S_skip (S_ifelse b_true (S_assign "x" (a_num 1))
                                          S_skip))
                  (S_assign "x" (a_num 2)))
           ([s0; s0; s0; s1] ++ TL [s1; s2])
           ([s0; s0; s0; s1] ++ TL [s1; s2])`
        by (irule (cj 3 eff_rules) >> fs[]) >>
      fs[])
  >- (fs[agree_def, tc_def, a_eval_def] >>
      rw[Abbr `s2`, Abbr `s1`, Abbr `s0`, FUN_EQ_THM, APPLY_UPDATE_THM] >>
      first_x_assum (qspec_then `"x"` mp_tac) >> rw[])
QED

(* ------------------------------------------------------------------------ *)
(* Lemma 2.22 and Lemma 4.24: chop does not distribute over conjunction     *)
(* ------------------------------------------------------------------------ *)

Overload fId = ``f_rel R_Id``
Overload ftrue = ``f_state (p_b b_true)``

(* ((Id /\ Id^Id)^true) has no traces, but distributing the chop over the
   conjunction, as in Definition 4.23, gives (Id^true) /\ ((Id^Id)^true),
   which contains s.s.s *)
Theorem distr_and_counterexample:
  !relI.
    fsem relI (f_chop (f_and fId (f_chop fId fId)) ftrue) <>
    fsem relI (f_and (f_chop fId ftrue) (f_chop (f_chop fId fId) ftrue))
Proof
  gen_tac >>
  `~([K 0; K 0; K 0] IN
     fsem relI (f_chop (f_and fId (f_chop fId fId)) ftrue))`
    by (rw[fsem_chop, fsem_and, IN_chop] >>
        rw[fsem_def, f_sem_def, R_sem_def, p_sem_def, b_eval_def] >>
        CCONTR_TAC >> fs[] >> rw[] >> fs[]) >>
  `[K 0; K 0; K 0] IN
   fsem relI (f_and (f_chop fId ftrue) (f_chop (f_chop fId fId) ftrue))`
    by (rw[fsem_chop, fsem_and] >>
        rw[fsem_def, f_sem_def, R_sem_def, p_sem_def, b_eval_def, IN_chop]
        >- (qexistsl_tac [`[K 0; K 0]`, `[K 0; K 0]`] >> rw[])
        >- (qexistsl_tac [`[K 0; K 0; K 0]`, `[K 0]`] >> rw[] >>
            qexistsl_tac [`[K 0; K 0]`, `[K 0; K 0]`] >> rw[])) >>
  metis_tac[]
QED
