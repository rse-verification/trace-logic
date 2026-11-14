(* Incompleteness of the finite-trace calculus (thesis Section 6.3):
   Examples 6.5 and 6.6, where every trace of the statement satisfies the
   specification but the verification condition tc(S) ==> ftc(S, phi)
   fails, for every contract the procedures conform with. *)

Theory verifIncompleteness
Ancestors
  arithmetic pred_set list rich_list combin alist integer traces tracesSem
  verifChop verifEff verifNorm verifTc verifPred verifFtc
Libs
  intLib

Overload fId[local] = ``f_rel R_Id``
Overload ftrue[local] = ``f_state (p_b b_true)``

(* ------------------------------------------------------------------------ *)
(* Example 6.6: a non-recursive call without a matching fixed point         *)
(* ------------------------------------------------------------------------ *)

(* m { x := x + 1; n() }   n { y := y + 1 } *)
Definition tbl66_def:
  tbl66 = ALOOKUP [("m", S_seq (S_assign "x" (a_plus (a_var "x") (a_num 1)))
                               (S_call "n"));
                   ("n", S_assign "y" (a_plus (a_var "y") (a_num 1)))]
End

Overload Sbx1[local] = ``f_rel (R_Sb (a_plus (a_var "x") (a_num 1)) "x")``
Overload Sby1[local] = ``f_rel (R_Sb (a_plus (a_var "y") (a_num 1)) "y")``

(* Id ^ Sb^(x+1)_x ^ Id ^ Sb^(y+1)_y *)
Definition phi66_def:
  phi66 = f_chop fId (f_chop Sbx1 (f_chop fId Sby1))
End

(* the traces of m(): Id, x := x + 1, Id, y := y + 1 *)
Definition tr66_def:
  tr66 (s:state) =
    let s1 = ("x" =+ s "x" + 1) s in [s; s; s1; s1; ("y" =+ s1 "y" + 1) s1]
End

Theorem ex66_Str:
  Str tbl66 (K {}) (S_call "m") = {tr66 s | T}
Proof
  `rho0 tbl66 (K {}) "n" =
   {t | ?s. t = [s; s; ("y" =+ s "y" + 1) s]}`
    by (`tbl66 "n" = SOME (S_assign "y" (a_plus (a_var "y") (a_num 1)))`
          by EVAL_TAC >>
        drule Str_call >> disch_then (qspec_then `K {}` mp_tac) >>
        rw[Str_def, Str0_def, dup_def, a_eval_def]) >>
  `tbl66 "m" = SOME (S_seq (S_assign "x" (a_plus (a_var "x") (a_num 1)))
                           (S_call "n"))` by EVAL_TAC >>
  drule Str_call >> disch_then (qspec_then `K {}` SUBST1_TAC) >>
  rw[Str_def, Str0_def, dup_def, IN_chop, EXTENSION, EQ_IMP_THM,
     a_eval_def, tr66_def] >> rw[]
  >- (Cases_on `r` >> fs[] >> rw[])
  >- (qexistsl_tac [`[s; ("x" =+ s "x" + 1) s]`,
                    `[("x" =+ s "x" + 1) s; ("x" =+ s "x" + 1) s;
                      ("y" =+ s "y" + 1) (("x" =+ s "x" + 1) s)]`] >>
      rw[APPLY_UPDATE_THM])
QED

(* chop with the traces of an assignment-like relation *)
Theorem chop_fun[local]:
  !f A. chop {t | ?s. t = [s; f s]} A =
        {t | ?s r. t = s::f s::r /\ f s::r IN A}
Proof
  rw[EXTENSION, IN_chop, EQ_IMP_THM, PULL_EXISTS] >> rw[]
  >- (Cases_on `t2` >> fs[])
  >- (qexists_tac `f s::r` >> rw[])
QED

(* phi follows from unfolding the strongest trace formula: m() and phi
   have the same traces *)
Theorem ex66_fsem:
  !relI. fsem relI phi66 = Str tbl66 (K {}) (S_call "m")
Proof
  rw[ex66_Str, phi66_def, fsem_chop] >>
  rw[fsem_def, f_sem_def, R_sem_def, a_eval_def] >>
  rw[chop_id, chop_fun, dup_def, EXTENSION, tr66_def, EQ_IMP_THM] >>
  rw[] >> qexists_tac `s` >> rw[]
QED

(* ftc fails on m() and phi for any fuel: phi has no fixed point for the
   call *)
Theorem ex66_ftc_fails:
  !pre post n g. ~ftc tbl66 pre post n 1 (S_call "m") phi66 [] g
Proof
  Cases_on `n` >> rw[ftc_def, phi66_def]
QED

Theorem ex66_normalised:
  distr (expand phi66) = phi66
Proof
  EVAL_TAC
QED

(* Example 6.6: every trace of m() satisfies phi, but for every contract
   that m and n conform with, the verification condition fails *)
Theorem ex66_incomplete:
  (!relI. Str tbl66 (K {}) (S_call "m") SUBSET fsem relI phi66) /\
  !pre post. conforms tbl66 pre post ==>
    ?g. tc pre post 1 (S_call "m") g /\
        !n. ~ftc tbl66 pre post n 1 (S_call "m") (distr (expand phi66)) [] g
Proof
  rw[ex66_fsem, ex66_normalised, ex66_ftc_fails] >>
  qexists_tac `\i. if i <= 2 then K 0 else LAST (tr66 (K 0))` >>
  rw[tc_def] >>
  `tr66 (K 0) IN Str tbl66 (K {}) (S_call "m")`
    by (rw[ex66_Str] >> metis_tac[]) >>
  fs[conforms_def] >> first_x_assum drule >> fs[tr66_def]
QED

(* With two fixed points, as in the strongest trace formula
   Id ^ mu X_m. (Sb^(x+1)_x ^ Id ^ mu X_n. Sb^(y+1)_y), the verification
   condition holds *)
Definition phi66_mu_def:
  phi66_mu = f_chop fId (f_mu "m" (f_chop Sbx1 (f_chop fId (f_mu "n" Sby1))))
End

Theorem ex66_mu_vc:
  !post g. tc (\m s. T) post 1 (S_call "m") g ==>
           ftc tbl66 (\m s. T) post 10 1 (S_call "m") phi66_mu [] g
Proof
  EVAL_TAC >> rw[]
QED

(* the method then proves the specification *)
Theorem ex66_mu:
  !relI. Str tbl66 (K {}) (S_call "m") SUBSET fsem relI phi66_mu
Proof
  gen_tac >> irule vc_sound_nf >> rw[] >>
  TRY (fs[tbl66_def, AllCaseEqs()] >> EVAL_TAC >> NO_TAC) >>
  TRY (EVAL_TAC >> NO_TAC) >>
  qexistsl_tac [`10`, `\m s s'. T`, `\m s. T`] >>
  rw[ex66_mu_vc, conforms_def]
QED

(* the two formulas have the same semantics: the fixed points do not
   recurse *)
Theorem ex66_mu_fsem:
  !relI. fsem relI phi66_mu = fsem relI phi66
Proof
  gen_tac >>
  `!X f. fv_f f = [] ==> fsem relI (f_mu X f) = fsem relI f`
    by (rw[fsem_def] >> ONCE_REWRITE_TAC[f_sem_mu_fixpoint] >>
        metis_tac[f_sem_closed, fsem_def]) >>
  `fv_f (f_chop Sbx1 (f_chop fId (f_mu "n" Sby1))) = [] /\ fv_f Sby1 = []`
    by EVAL_TAC >>
  rw[phi66_mu_def, phi66_def, fsem_chop]
QED

(* ------------------------------------------------------------------------ *)
(* Example 6.5: intermediate states of a recursive call                     *)
(* ------------------------------------------------------------------------ *)

(* m { if x > 0 then (y := 2 * y; x := x - 1; m()) else x := 0 } *)
Definition m65_body_def:
  m65_body =
    S_ifelse (b_neg (b_leq (a_var "x") (a_num 0)))
             (S_seq (S_assign "y" (a_times (a_num 2) (a_var "y")))
                    (S_seq (S_assign "x" (a_minus (a_var "x") (a_num 1)))
                           (S_call "m")))
             (S_assign "x" (a_num 0))
End

Definition tbl65_def:
  tbl65 = ALOOKUP [("m", m65_body)]
End

(* x := 5; y := 1; m() *)
Definition S65_def:
  S65 = S_seq (S_assign "x" (a_num 5))
              (S_seq (S_assign "y" (a_num 1)) (S_call "m"))
End

(* true ^ Sb^(2^3)_y ^ true: some step sets y to 8 *)
Definition phi65_def:
  phi65 = f_chop ftrue (f_chop (f_rel (R_Sb (a_num 8) "y")) ftrue)
End

Theorem ex65_nf:
  nf S65 /\ nf m65_body /\ norm S65 = S65 /\ norm m65_body = m65_body
Proof
  EVAL_TAC
QED

(* ||phi|| is closed under adding states in front *)
Theorem phi65_prefix:
  !relI l t. t IN fsem relI phi65 ==> l ++ t IN fsem relI phi65
Proof
  gen_tac >>
  `!B l t. t IN chop (fsem relI ftrue) B ==>
           l ++ t IN chop (fsem relI ftrue) B`
    by (rw[IN_chop, fsem_def, f_sem_def, p_sem_def, b_eval_def] >>
        qexistsl_tac [`l ++ s::r`, `t2`] >> rw[LAST_APPEND_CONS] >>
        Cases_on `l` >> rw[]) >>
  rw[phi65_def, fsem_chop] >> fs[phi65_def, fsem_chop]
QED

Theorem phi65_fuse:
  !relI t1 t. t1 <> [] /\ t <> [] /\ LAST t1 = HD t /\
              t IN fsem relI phi65 ==> t1 ++ TL t IN fsem relI phi65
Proof
  rw[] >>
  `t1 ++ TL t = FRONT t1 ++ t`
    by (Cases_on `t` >> fs[] >>
        metis_tac[APPEND_FRONT_LAST, APPEND_ASSOC, APPEND]) >>
  rw[phi65_prefix]
QED

Theorem phi65_cons:
  !relI s t. t IN fsem relI phi65 ==> s::t IN fsem relI phi65
Proof
  metis_tac[phi65_prefix, APPEND]
QED

Theorem phi65_step:
  !relI s r. s::("y" =+ 8) s::r IN fsem relI phi65
Proof
  rw[phi65_def, fsem_chop] >>
  rw[fsem_def, f_sem_def, chop_pairs, R_sem_def, p_sem_def, b_eval_def,
     a_eval_def, IN_chop] >>
  qexistsl_tac [`[s]`, `s::("y" =+ 8) s::r`] >> rw[] >>
  qexistsl_tac [`[s; ("y" =+ 8) s]`, `("y" =+ 8) s::r`] >> rw[]
QED

(* every trace of m() from x = 5, y = 1 (or the states that follow) has
   a step that sets y to 8 *)
Definition from65_def:
  from65 (s:state) =
    ((s "x" = 5 /\ s "y" = 1) \/ (s "x" = 4 /\ s "y" = 2) \/
     (s "x" = 3 /\ s "y" = 4))
End

Theorem m65_call_phi:
  !relI t. t IN Str tbl65 (K {}) (S_call "m") /\ from65 (HD t) ==>
           t IN fsem relI phi65
Proof
  gen_tac >>
  `ileq (rho0 tbl65 (K {}))
        (\m:string. {t | t <> [] /\ (from65 (HD t) ==> t IN fsem relI phi65)})`
    by (irule rho0_least >>
        rw[ileq_def, H_def, SUBSET_DEF] >>
        Cases_on `tbl65 m` >> fs[] >>
        fs[tbl65_def, AllCaseEqs()] >> rw[] >>
        fs[m65_body_def, Str0_def, dup_def, restrict_def, IN_chop] >>
        rw[] >> fs[b_eval_def, a_eval_def, from65_def] >> rw[] >>
        TRY (`F` suffices_by rw[] >> rpt (pop_assum mp_tac) >>
             intLib.ARITH_TAC) >>
        rename1 `_ = HD tt` >> Cases_on `tt` >> gvs[APPLY_UPDATE_THM] >>
        metis_tac[phi65_cons, phi65_step]) >>
  rw[Str_def, Str0_def] >> fs[ileq_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ex65_Str:
  !relI. Str tbl65 (K {}) S65 SUBSET fsem relI phi65
Proof
  rw[SUBSET_DEF, Str_def, S65_def, Str0_def, IN_chop] >>
  gvs[a_eval_def] >> rename1 `tt IN rho0 _ _ _` >> Cases_on `tt` >> gvs[] >>
  irule phi65_cons >> irule phi65_cons >> irule m65_call_phi >>
  rw[Str_def, Str0_def, from65_def, APPLY_UPDATE_THM]
QED

(* m() terminates from every state with x >= 0 *)
Theorem m65_terminates:
  !k s. s "x" = &k ==> ?t. t IN Str tbl65 (K {}) (S_call "m") /\ HD t = s
Proof
  `tbl65 "m" = SOME m65_body` by EVAL_TAC >>
  drule Str_call >> disch_then (qspec_then `K {}` assume_tac) >>
  Induct >> rw[]
  >- (qexists_tac `[s; s; s; ("x" =+ 0) s]` >>
      rw[dup_def, Str_def, m65_body_def, Str0_def, restrict_def,
         b_eval_def, a_eval_def])
  >- (qabbrev_tac `s1 = ("y" =+ 2 * s "y") s` >>
      qabbrev_tac `s2 = ("x" =+ s1 "x" - 1) s1` >>
      first_x_assum (qspec_then `s2` mp_tac) >>
      impl_tac
      >- (rw[Abbr `s2`, Abbr `s1`, APPLY_UPDATE_THM] >> intLib.ARITH_TAC) >>
      strip_tac >> rename1 `HD tt = s2` >>
      `tt IN rho0 tbl65 (K {}) "m"` by metis_tac[Str_def, Str0_def] >>
      Cases_on `tt` >- (imp_res_tac Str_call_cases >> fs[]) >>
      qexists_tac `s::s::s::s1::s2::t` >>
      rw[dup_def, Str_def, m65_body_def, Str0_def, restrict_def,
         b_eval_def, a_eval_def, chop_fun] >>
      fs[Abbr `s2`, Abbr `s1`] >> intLib.ARITH_TAC)
QED

(* Unfold ftc with a fuel variable n by a case split on n, until no such
   ftc is left (as in verifExamples) *)
val ftc_tm = prim_mk_const {Thy = "verifFtc", Name = "ftc"};

fun fuel_var t =
  let val (f, args) = strip_comb t
  in
    if same_const f ftc_tm andalso length args = 9 andalso
       is_var (el 4 args)
    then SOME (el 4 args) else NONE
  end;

val fuel_tac : tactic = fn (asl, w) =>
  let val n = valOf (fuel_var (find_term (isSome o fuel_var) w))
  in
    (Cases_on `^n` >> CONV_TAC EVAL >> asm_simp_tac std_ss []) (asl, w)
  end;

(* ftc fails for any fuel on a sequence where none of the steps of
   x := 5, y := 1 and the call sets y to 8 *)
Theorem ex65_ftc_fails_lemma[local]:
  !pre post g n.
    g 2 <> ("y" =+ 8) (g 1) /\ g 3 <> ("y" =+ 8) (g 2) /\
    g 4 <> ("y" =+ 8) (g 3) ==>
    ~ftc tbl65 pre post n 1 S65 (distr (expand phi65)) [] g
Proof
  rewrite_tac[EVAL ``distr (expand phi65)``, S65_def] >>
  rpt gen_tac >> strip_tac >> rpt fuel_tac
QED

(* Example 6.5: every trace of S satisfies phi, but for every contract
   that m conforms with, the verification condition fails *)
Theorem ex65_incomplete:
  (!relI. Str tbl65 (K {}) S65 SUBSET fsem relI phi65) /\
  !pre post. conforms tbl65 pre post ==>
    ?g. tc pre post 1 S65 g /\
        !n. ~ftc tbl65 pre post n 1 S65 (distr (expand phi65)) [] g
Proof
  rw[ex65_Str] >>
  `?t. t IN Str tbl65 (K {}) (S_call "m") /\
       HD t = ("y" =+ 1) (("x" =+ 5) (K 0))`
    by (irule m65_terminates >> qexists_tac `5` >> rw[APPLY_UPDATE_THM]) >>
  qexists_tac `\i. if i = 1 then K 0 else if i = 2 then ("x" =+ 5) (K 0)
                   else if i <= 4 then HD t else LAST t` >>
  rw[]
  >- (rw[S65_def, tc_def, a_eval_def] >> fs[conforms_def] >>
      first_x_assum drule >> rw[])
  >- (irule ex65_ftc_fails_lemma >> rw[FUN_EQ_THM] >>
      qexists_tac `"y"` >> rw[APPLY_UPDATE_THM])
QED
