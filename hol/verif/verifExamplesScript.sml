(* Examples of the thesis: the motivating Example 3.1, Examples 4.31 and
   4.32 for the verification condition, and Examples 4.12, 4.15, 4.18 and
   4.25 for the auxiliary definitions. *)

Theory verifExamples
Ancestors
  arithmetic pred_set list combin alist integer traces tracesSem verifChop
  verifEff verifNorm verifTc verifPred verifFtc
Libs
  intLib

(* ------------------------------------------------------------------------ *)
(* The procedure m of Examples 3.1, 4.31 and 4.32                           *)
(* ------------------------------------------------------------------------ *)

(* m { if x <= 0 then x := 0 else (x := x - 1; m()) } *)
Definition m_body_def:
  m_body =
    S_ifelse (b_leq (a_var "x") (a_num 0))
             (S_assign "x" (a_num 0))
             (S_seq (S_assign "x" (a_minus (a_var "x") (a_num 1)))
                    (S_call "m"))
End

Definition m_tbl_def:
  m_tbl = ALOOKUP [("m", m_body)]
End

(* the strongest contract of m: x is 0 at the end, and m changes no other
   variable *)
Definition m_inv_def:
  m_inv (s:state) (s':state) = (s' "x" = 0 /\ !v. v <> "x" ==> s' v = s v)
End

Theorem m_call_inv:
  !t. t IN Str m_tbl (K {}) (S_call "m") ==>
      t <> [] /\ m_inv (HD t) (LAST t)
Proof
  `ileq (rho0 m_tbl (K {}))
        (\m:string. {t | t <> [] /\ m_inv (HD t) (LAST t)})`
    by (irule rho0_least >>
        rw[ileq_def, H_def, SUBSET_DEF] >>
        Cases_on `m_tbl m` >> fs[] >>
        fs[m_tbl_def, AllCaseEqs()] >> rw[] >>
        fs[m_body_def, Str0_def, dup_def, restrict_def, IN_chop] >>
        rw[] >>
        fs[m_inv_def, APPLY_UPDATE_THM, a_eval_def, LAST_APPEND_CONS] >>
        Cases_on `t2` >> fs[] >> rw[] >> fs[APPLY_UPDATE_THM] >>
        Cases_on `t` >> fs[LAST_DEF] >> rw[] >> fs[APPLY_UPDATE_THM]) >>
  rw[Str_def, Str0_def] >> fs[ileq_def, SUBSET_DEF] >> metis_tac[]
QED

(* every contract implied by m_inv holds *)
Theorem m_conforms:
  !pre post. (!s s'. m_inv s s' ==> post "m" s s') ==>
             conforms m_tbl pre post
Proof
  rw[conforms_def] >> drule Str_call_cases >> rw[] >>
  `m = "m"` by (fs[m_tbl_def, AllCaseEqs()]) >> rw[] >>
  imp_res_tac m_call_inv >> fs[LAST_CONS]
QED

Theorem m_tbl_nf:
  !m body. m_tbl m = SOME body ==> nf body
Proof
  rw[m_tbl_def, AllCaseEqs()] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------ *)
(* Example 3.1                                                              *)
(* ------------------------------------------------------------------------ *)

(* y := x; m(); y := y - x *)
Definition S31_def:
  S31 = S_seq (S_assign "y" (a_var "x"))
              (S_seq (S_call "m")
                     (S_assign "y" (a_minus (a_var "y") (a_var "x"))))
End

Definition pre31_def:
  pre31 (m:string) (s:state) = T
End

(* x = 0 /\ y = y0 *)
Definition post31_def:
  post31 (m:string) (s:state) (s':state) = (s' "x" = 0 /\ s' "y" = s "y")
End

(* psi = Id ^ (Sb^0_x \/ Sb^(x-1)_x ^ Id ^ X_m) *)
Definition psi31_def:
  psi31 =
    f_chop (f_rel R_Id)
           (f_or (f_rel (R_Sb (a_num 0) "x"))
                 (f_chop (f_rel (R_Sb (a_minus (a_var "x") (a_num 1)) "x"))
                         (f_chop (f_rel R_Id) (f_recvar "m"))))
End

(* phi = Sb^x_y ^ Id ^ (mu X_m. psi) ^ Id *)
Definition phi31_def:
  phi31 =
    f_chop (f_rel (R_Sb (a_var "x") "y"))
           (f_chop (f_rel R_Id)
                   (f_chop (f_mu "m" psi31) (f_rel R_Id)))
End

(* the verification condition tc(S) => ftc(S, phi) *)
Theorem ex31_vc:
  !g. tc pre31 post31 1 S31 g ==>
      ftc m_tbl pre31 post31 20 1 S31 phi31 [] g
Proof
  EVAL_TAC >> rw[] >> fs[] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] >> intLib.ARITH_TAC
QED

Theorem ex31:
  !relI. Str m_tbl (K {}) S31 SUBSET fsem relI phi31
Proof
  gen_tac >> irule vc_sound_nf >> rw[]
  >- metis_tac[m_tbl_nf]
  >- EVAL_TAC
  >- EVAL_TAC
  >- (qexistsl_tac [`20`, `post31`, `pre31`] >> rw[ex31_vc] >>
      irule m_conforms >> rw[m_inv_def, post31_def])
QED

(* The inclusion is not vacuous: S has traces, and the specification rejects
   the traces of y := x; m(); y := y + 1. *)

Theorem K0_update[local]:
  !x. (x =+ 0) (K 0) = (K 0):state
Proof
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[]
QED

Theorem m_call_base:
  !s. s "x" <= 0 ==>
      [s; s; s; ("x" =+ 0) s] IN Str m_tbl (K {}) (S_call "m")
Proof
  rw[] >> `m_tbl "m" = SOME m_body` by EVAL_TAC >>
  drule Str_call >> disch_then (qspec_then `K {}` SUBST1_TAC) >>
  rw[dup_def, Str_def, m_body_def, Str0_def, restrict_def, b_eval_def,
     a_eval_def]
QED

Theorem ex31_trace:
  [K 0; K 0; K 0; K 0; K 0; K 0] IN Str m_tbl (K {}) S31
Proof
  `[K 0; K 0; K 0; K 0] IN Str m_tbl (K {}) (S_call "m")`
    by (qspec_then `K 0` mp_tac m_call_base >> rw[K0_update]) >>
  fs[Str_def, S31_def, Str0_def, IN_chop] >>
  qexistsl_tac [`[K 0; K 0]`, `[K 0; K 0; K 0; K 0; K 0]`] >>
  rw[a_eval_def, K0_update] >>
  qexistsl_tac [`[K 0; K 0; K 0; K 0]`, `[K 0; K 0]`] >>
  rw[a_eval_def, K0_update]
QED

(* y := x; m(); y := y + 1 *)
Definition S31_wrong_def:
  S31_wrong = S_seq (S_assign "y" (a_var "x"))
                    (S_seq (S_call "m")
                           (S_assign "y" (a_plus (a_var "y") (a_num 1))))
End

(* traces that end with two equal states *)
Definition ends_stutter_def:
  ends_stutter (t:state list) = ?l s. t = l ++ [s; s]
End

Theorem chop_ends_stutter:
  !A B t. (!u. u IN B ==> ends_stutter u) /\ t IN chop A B ==>
          ends_stutter t
Proof
  rw[IN_chop] >> res_tac >> fs[ends_stutter_def] >> rw[] >>
  Cases_on `l` >> fs[] >>
  `?l' x. t1 = SNOC x l'` by metis_tac[SNOC_CASES] >> fs[] >>
  qexistsl_tac [`l'`, `s`] >> rw[]
QED

Theorem phi31_ends_stutter:
  !relI t. t IN fsem relI phi31 ==> ends_stutter t
Proof
  rpt gen_tac >>
  qabbrev_tac `I0 = fsem relI (f_rel R_Id)` >>
  `!u. u IN I0 ==> ends_stutter u`
    by (rw[Abbr `I0`, fsem_def, f_sem_def, R_sem_def, ends_stutter_def] >>
        qexistsl_tac [`[]`, `s`] >> rw[]) >>
  `!A u. u IN chop A I0 ==> ends_stutter u`
    by metis_tac[chop_ends_stutter] >>
  `!A B u. u IN chop A (chop B I0) ==> ends_stutter u`
    by metis_tac[chop_ends_stutter] >>
  `!A B C u. u IN chop A (chop B (chop C I0)) ==> ends_stutter u`
    by metis_tac[chop_ends_stutter] >>
  rw[phi31_def, fsem_chop] >> metis_tac[]
QED

(* the specification rejects a trace of y := x; m(); y := y + 1 *)
Theorem ex31_nonvacuous:
  [K 0; K 0; K 0; K 0; K 0; K 0] IN Str m_tbl (K {}) S31 /\
  ?t. t IN Str m_tbl (K {}) S31_wrong /\ !relI. t NOTIN fsem relI phi31
Proof
  rw[ex31_trace] >>
  qexists_tac `[K 0; K 0; K 0; K 0; K 0; ("y" =+ 1) (K 0)]` >> rw[]
  >- (`[K 0; K 0; K 0; K 0] IN Str m_tbl (K {}) (S_call "m")`
        by (qspec_then `K 0` mp_tac m_call_base >> rw[K0_update]) >>
      fs[Str_def, S31_wrong_def, Str0_def, IN_chop] >>
      qexistsl_tac [`[K 0; K 0]`,
                    `[K 0; K 0; K 0; K 0; ("y" =+ 1) (K 0)]`] >>
      rw[a_eval_def, K0_update] >>
      qexistsl_tac [`[K 0; K 0; K 0; K 0]`, `[K 0; ("y" =+ 1) (K 0)]`] >>
      rw[a_eval_def, K0_update])
  >- (strip_tac >> drule phi31_ends_stutter >>
      rw[ends_stutter_def, FUN_EQ_THM] >> CCONTR_TAC >> fs[] >>
      first_x_assum (qspec_then `"y"` mp_tac) >> rw[APPLY_UPDATE_THM])
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.31                                                             *)
(* ------------------------------------------------------------------------ *)

(* the weaker contract x = 0 *)
Definition post431_def:
  post431 (m:string) (s:state) (s':state) = (s' "x" = 0)
End

(* true ^ (mu X_m. true ^ (Sb^0_x \/ X_m)) ^ Id *)
Definition phi431_def:
  phi431 =
    f_chop (f_state (p_b b_true))
           (f_chop (f_mu "m" (f_chop (f_state (p_b b_true))
                                     (f_or (f_rel (R_Sb (a_num 0) "x"))
                                           (f_recvar "m"))))
                   (f_rel R_Id))
End

Theorem ex431_vc:
  !g. tc pre31 post431 1 S31 g ==>
      ftc m_tbl pre31 post431 30 1 S31 (distr (expand phi431)) [] g
Proof
  EVAL_TAC >> rw[] >> fs[] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] >> intLib.ARITH_TAC
QED

Theorem ex431:
  !relI. Str m_tbl (K {}) S31 SUBSET fsem relI phi431
Proof
  gen_tac >> once_rewrite_tac[GSYM fsem_expand] >>
  once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_sound_nf >> rw[]
  >- metis_tac[m_tbl_nf]
  >- EVAL_TAC
  >- EVAL_TAC
  >- (qexistsl_tac [`30`, `post431`, `pre31`] >> rw[ex431_vc] >>
      irule m_conforms >> rw[m_inv_def, post431_def])
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.32                                                             *)
(* ------------------------------------------------------------------------ *)

(* x := -x; z := 0; y := x; m(); y := y - (x + z) *)
Definition S432_def:
  S432 =
    S_seq (S_assign "x" (a_uminus (a_var "x")))
          (S_seq (S_assign "z" (a_num 0))
                 (S_seq (S_assign "y" (a_var "x"))
                        (S_seq (S_call "m")
                               (S_assign "y"
                                  (a_minus (a_var "y")
                                           (a_plus (a_var "x")
                                                   (a_var "z")))))))
End

(* x = 0 /\ z = z0 *)
Definition post432_def:
  post432 (m:string) (s:state) (s':state) = (s' "x" = 0 /\ s' "z" = s "z")
End

(* Unfold ftc with a fuel variable n by a case split on n, until no such
   ftc is left. *)
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

(* With the contract x = 0 of Example 4.31, ftc(S, phi) fails on a
   sequence that satisfies tc(S), for any fuel: after the call, z is
   unconstrained. *)
Theorem ex432_weak_fails_lemma[local]:
  !g n. g 7 <> g 6 ==>
        ~ftc m_tbl pre31 post431 n 1 S432 (distr (expand phi431)) [] g
Proof
  rewrite_tac[EVAL ``distr (expand phi431)``, S432_def] >>
  rpt gen_tac >> strip_tac >> rpt fuel_tac
QED

Theorem ex432_weak_fails:
  ?g. tc pre31 post431 1 S432 g /\
      !n. ~ftc m_tbl pre31 post431 n 1 S432 (distr (expand phi431)) [] g
Proof
  qexists_tac `\i. if i <= 5 then K 0
                   else if i = 6 then ("z" =+ 1) (K 0)
                   else ("y" =+ -1) (("z" =+ 1) (K 0))` >>
  rw[]
  >- (EVAL_TAC >> rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[])
  >- (irule ex432_weak_fails_lemma >> rw[FUN_EQ_THM] >>
      qexists_tac `"y"` >> rw[APPLY_UPDATE_THM])
QED

(* With the contract x = 0 /\ z = z0, the verification condition holds *)
Theorem ex432_vc:
  !g. tc pre31 post432 1 S432 g ==>
      ftc m_tbl pre31 post432 30 1 S432 (distr (expand phi431)) [] g
Proof
  EVAL_TAC >> rw[] >> fs[] >>
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[] >> intLib.ARITH_TAC
QED

Theorem ex432:
  !relI. Str m_tbl (K {}) S432 SUBSET fsem relI phi431
Proof
  gen_tac >> once_rewrite_tac[GSYM fsem_expand] >>
  once_rewrite_tac[GSYM fsem_distr] >>
  irule vc_sound_nf >> rw[]
  >- metis_tac[m_tbl_nf]
  >- EVAL_TAC
  >- EVAL_TAC
  >- (qexistsl_tac [`30`, `post432`, `pre31`] >> rw[ex432_vc] >>
      irule m_conforms >> rw[m_inv_def, post432_def])
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.12: normalization                                              *)
(* ------------------------------------------------------------------------ *)

Overload bx0 = ``b_eq (a_var "x") (a_num 0)``
(* x < 0 *)
Overload bxneg = ``b_neg (b_leq (a_num 0) (a_var "x"))``
Overload xinc = ``S_assign "x" (a_plus (a_var "x") (a_num 1))``

(* (if x = 0 then x := 1 else (if x < 0 then skip else x := -x); skip);
   x := x + 1 *)
Definition S412_def:
  S412 =
    S_seq (S_ifelse bx0 (S_assign "x" (a_num 1))
                    (S_seq (S_ifelse bxneg S_skip
                                     (S_assign "x" (a_uminus (a_var "x"))))
                           S_skip))
          xinc
End

Theorem ex412:
  norm S412 =
    S_ifelse bx0 (S_seq (S_assign "x" (a_num 1)) xinc)
             (S_ifelse bxneg (S_seq S_skip (S_seq S_skip xinc))
                       (S_seq (S_assign "x" (a_uminus (a_var "x")))
                              (S_seq S_skip xinc))) /\
  nf (norm S412)
Proof
  EVAL_TAC
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.15: trace constraints need the normal form                     *)
(* ------------------------------------------------------------------------ *)

(* (if y = 0 then x := 1 else skip); x := 2 *)
Definition S415_def:
  S415 = S_seq (S_ifelse (b_eq (a_var "y") (a_num 0))
                         (S_assign "x" (a_num 1)) S_skip)
               (S_assign "x" (a_num 2))
End

(* tc(S) holds only if y <> 0 and x = 2 initially, but tc(norm(S)) holds
   for a trace with y = 0 *)
Theorem ex415:
  (!pre post g. tc pre post 1 S415 g ==> g 1 "y" <> 0 /\ g 1 "x" = 2) /\
  norm S415 =
    S_ifelse (b_eq (a_var "y") (a_num 0))
             (S_seq (S_assign "x" (a_num 1)) (S_assign "x" (a_num 2)))
             (S_seq S_skip (S_assign "x" (a_num 2))) /\
  ?g. g 1 "y" = 0 /\ tc (\m s. T) (\m s s'. T) 1 (norm S415) g
Proof
  rw[]
  >- (CCONTR_TAC >> fs[S415_def, tc_def, b_eval_def, a_eval_def] >>
      rfs[] >> fs[FUN_EQ_THM] >>
      first_x_assum (qspec_then `"x"` mp_tac) >> rw[APPLY_UPDATE_THM])
  >- (`!f (a:int). f = ("x" =+ a) f ==> f "x" = a`
        by (rw[] >> pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
            rw[APPLY_UPDATE_THM]) >>
      `!f (a:int) b. ("x" =+ a) f = ("x" =+ b) f ==> a = b`
        by (rw[FUN_EQ_THM] >> pop_assum (qspec_then `"x"` mp_tac) >>
            rw[APPLY_UPDATE_THM]) >>
      fs[S415_def, tc_def, b_eval_def, a_eval_def] >>
      Cases_on `g 1 "y" = 0` >> fs[]
      >- (res_tac >> fs[])
      >- metis_tac[])
  >- EVAL_TAC
  >- (qexists_tac `\i. if i <= 2 then K 0
                       else if i = 3 then ("x" =+ 1) (K 0)
                       else ("x" =+ 2) (K 0)` >>
      EVAL_TAC >> rw[FUN_EQ_THM, APPLY_UPDATE_THM])
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.18: the induced predicate                                      *)
(* ------------------------------------------------------------------------ *)

(* mu X. Id ^ X \/ ((x = 10) /\ Sb^(x+1)_x) *)
Definition phi418_def:
  phi418 =
    f_mu "X" (f_or (f_chop (f_rel R_Id) (f_recvar "X"))
                   (f_and (f_state (p_b (b_eq (a_var "x") (a_num 10))))
                          (f_rel (R_Sb (a_plus (a_var "x") (a_num 1)) "x"))))
End

Theorem ex418:
  (!i g. pred 1 i phi418 g <=>
         g i "x" = 10 /\ g (i + 1) = ("x" =+ g i "x" + 1) (g i)) /\
  !relI. [("x" =+ 10) (K 0); ("x" =+ 11) (K 0)] IN fsem relI phi418
Proof
  conj_asm1_tac
  >- (EVAL_TAC >> rw[])
  >- (rw[] >>
      qspecl_then [`1`, `1`, `phi418`,
                   `\i. if i = 1 then ("x" =+ 10) (K 0)
                        else ("x" =+ 11) (K 0)`, `relI`]
                  mp_tac pred_sound >>
      impl_tac
      >- (rw[] >> TRY (EVAL_TAC >> NO_TAC) >>
          rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> rw[]) >>
      rw[])
QED

(* ------------------------------------------------------------------------ *)
(* Example 4.25: distribution                                               *)
(* ------------------------------------------------------------------------ *)

Overload Sbxm = ``f_rel (R_Sb (a_minus (a_var "x") (a_num 1)) "x")``
Overload Sbxp = ``f_rel (R_Sb (a_plus (a_var "x") (a_num 1)) "x")``

(* distr((Id \/ Id ^ Sb^(x-1)_x) ^ Sb^(x+1)_x) =
   Id ^ Sb^(x+1)_x \/ Id ^ Sb^(x-1)_x ^ Sb^(x+1)_x *)
Theorem ex425:
  distr (f_chop (f_or (f_rel R_Id) (f_chop (f_rel R_Id) Sbxm)) Sbxp) =
  f_or (f_chop (f_rel R_Id) Sbxp) (f_chop (f_rel R_Id) (f_chop Sbxm Sbxp))
Proof
  EVAL_TAC
QED
