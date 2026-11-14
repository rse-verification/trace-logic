(* Deep embeddings of the encodings of thesis Chapter 4 as first-order
   formulas over the structure M of Definition 4.2 (folRec): the induced
   predicate pred (Definition 4.17), the trace constraints tc
   (Definition 4.13), the finite-trace calculus ftc (Definition 4.28) and
   the procedure contract condition pcc (Definition 4.34). Each generator
   follows the shallow definition clause by clause, and each is shown to
   hold in M exactly when the shallow version holds, for a valuation that
   maps the state variable s(k) to g k on the indices used. *)

Theory vcGen
Ancestors
  arithmetic pred_set list combin string ASCIInumbers traces tracesSem
  verifEff verifNorm verifTc verifPred verifFtc folString folRec
  vcContract vcPcc
Libs
  intLib

(* ------------------------------------------------------------------------ *)
(* Contracts as formulas                                                    *)
(* ------------------------------------------------------------------------ *)

(* a two-state arithmetic expression, with initial state st0 and final
   state st *)
Definition ta2sterm_def:
  (ta2sterm st0 st (ta_num n) = int_const n) /\
  (ta2sterm st0 st (ta_var x) = SFn ("sel_" ++ x) [st]) /\
  (ta2sterm st0 st (ta_old x) = SFn ("sel_" ++ x) [st0]) /\
  (ta2sterm st0 st (ta_uminus a) = SFn "neg" [ta2sterm st0 st a]) /\
  (ta2sterm st0 st (ta_plus a1 a2) =
     SFn "+" [ta2sterm st0 st a1; ta2sterm st0 st a2]) /\
  (ta2sterm st0 st (ta_minus a1 a2) =
     SFn "-" [ta2sterm st0 st a1; ta2sterm st0 st a2]) /\
  (ta2sterm st0 st (ta_times a1 a2) =
     SFn "*" [ta2sterm st0 st a1; ta2sterm st0 st a2])
End

Definition tb2sform_def:
  (tb2sform st0 st tb_true = STrue) /\
  (tb2sform st0 st tb_false = SFalse) /\
  (tb2sform st0 st (tb_eq a1 a2) =
     SPred "=" [ta2sterm st0 st a1; ta2sterm st0 st a2]) /\
  (tb2sform st0 st (tb_leq a1 a2) =
     SPred "<=" [ta2sterm st0 st a1; ta2sterm st0 st a2]) /\
  (tb2sform st0 st (tb_neg b) = SNot (tb2sform st0 st b)) /\
  (tb2sform st0 st (tb_and b1 b2) =
     SAnd (tb2sform st0 st b1) (tb2sform st0 st b2))
End

(* Pre_m(st) and Post_m(st0, st) *)
Definition pre_sform_def:
  pre_sform (ct:ctable) m st =
    case ct m of SOME (p, q) => b2sform st p | NONE => STrue
End

Definition post_sform_def:
  post_sform (ct:ctable) m st0 st =
    case ct m of SOME (p, q) => tb2sform st0 st q | NONE => STrue
End

Theorem stermval_ta2sterm:
  !D a v st0 st s0 s.
    stermval (rec_model D) v st0 = INR s0 /\ stermval (rec_model D) v st = INR s ==>
    stermval (rec_model D) v (ta2sterm st0 st a) = INL (ta_eval a s0 s)
Proof
  gen_tac >> Induct >>
  rw[ta2sterm_def, stermval_def, stermval_int_const, ta_eval_def] >>
  res_tac >> rw[rec_fun_def, isPREFIX_STRCAT, DROP_APPEND]
QED

Theorem sholds_tb2sform:
  !D b v st0 st s0 s.
    stermval (rec_model D) v st0 = INR s0 /\ stermval (rec_model D) v st = INR s ==>
    (sholds (rec_model D) v (tb2sform st0 st b) <=> tb_eval b s0 s)
Proof
  gen_tac >> Induct >> rw[tb2sform_def, sholds_def, tb_eval_def] >>
  imp_res_tac stermval_ta2sterm >> res_tac >> rw[rec_pred_def]
QED

Theorem sholds_pre_sform:
  !D ct m v st s.
    stermval (rec_model D) v st = INR s ==>
    (sholds (rec_model D) v (pre_sform ct m st) <=> cpre ct m s)
Proof
  rw[pre_sform_def, cpre_def] >> Cases_on `ct m` >> rw[sholds_def] >>
  PairCases_on `x` >> rw[sholds_b2sform]
QED

Theorem sholds_post_sform:
  !D ct m v st0 st s0 s.
    stermval (rec_model D) v st0 = INR s0 /\ stermval (rec_model D) v st = INR s ==>
    (sholds (rec_model D) v (post_sform ct m st0 st) <=> cpost ct m s0 s)
Proof
  rw[post_sform_def, cpost_def] >> Cases_on `ct m` >> rw[sholds_def] >>
  PairCases_on `x` >> rw[sholds_tb2sform]
QED

(* ------------------------------------------------------------------------ *)
(* State variables                                                          *)
(* ------------------------------------------------------------------------ *)

(* the name of the state variable s(k) *)
Definition sname_def:
  sname (k:num) = "s" ++ toString k
End

Theorem svar_sname:
  !k. svar k = SV (sname k)
Proof
  rw[svar_def, sname_def]
QED

Theorem sname_11[simp]:
  !j k. sname j = sname k <=> j = k
Proof
  rw[sname_def, toString_inj]
QED

(* the valuation v maps s(k) to g k for lo <= k <= hi *)
Definition vagree_def:
  vagree lo hi (v:string -> rdom) (g:num -> state) <=>
    !k. lo <= k /\ k <= hi ==> v (sname k) = INR (g k)
End

Theorem vagree_mono:
  !lo hi v g lo' hi'.
    vagree lo hi v g /\ lo <= lo' /\ hi' <= hi ==> vagree lo' hi' v g
Proof
  rw[vagree_def]
QED

Theorem stermval_svar:
  !D lo hi v g k.
    vagree lo hi v g /\ lo <= k /\ k <= hi ==>
    stermval (rec_model D) v (svar k) = INR (g k)
Proof
  rw[vagree_def, svar_sname, stermval_def]
QED

(* forall s(k) ... s(k + n - 1). f *)
Definition sforall_from_def:
  (sforall_from k 0 f = f) /\
  (sforall_from k (SUC n) f =
     sforall_state (sname k) (sforall_from (k + 1) n f))
End

(* the valuation v with s(j) mapped to h j for k <= j < k + n *)
Definition upd_from_def:
  (upd_from k 0 (h:num -> state) (v:string -> rdom) = v) /\
  (upd_from k (SUC n) h v = upd_from (k + 1) n h ((sname k =+ INR (h k)) v))
End

Theorem upd_from_out:
  !n k h v x.
    (!j. k <= j /\ j < k + n ==> x <> sname j) ==> upd_from k n h v x = v x
Proof
  Induct >> rw[upd_from_def] >>
  `upd_from (k + 1) n h ((sname k =+ INR (h k)) v) x =
   ((sname k =+ INR (h k)) v) x`
    by (first_x_assum irule >> rw[] >> first_x_assum irule >> decide_tac) >>
  rw[APPLY_UPDATE_THM] >> first_x_assum (qspec_then `k` mp_tac) >> rw[]
QED

Theorem upd_from_in:
  !n k h v j. k <= j /\ j < k + n ==> upd_from k n h v (sname j) = INR (h j)
Proof
  Induct >> rw[upd_from_def] >>
  Cases_on `j = k`
  >- (rw[] >>
      qspecl_then [`n`, `j + 1`, `h`, `(sname j =+ INR (h j)) v`,
                   `sname j`] mp_tac upd_from_out >>
      impl_tac >- rw[] >> rw[APPLY_UPDATE_THM])
  >- (first_x_assum irule >> decide_tac)
QED

Theorem vagree_upd_from:
  !n k h v. vagree k (k + n) (upd_from k (SUC n) h v) h
Proof
  rw[vagree_def] >> irule upd_from_in >> decide_tac
QED

Theorem upd_from_cong:
  !n k h h' v.
    (!j. k <= j /\ j < k + n ==> h j = h' j) ==>
    upd_from k n h v = upd_from k n h' v
Proof
  rpt strip_tac >> CONV_TAC FUN_EQ_CONV >> qx_gen_tac `x` >>
  Cases_on `?j. k <= j /\ j < k + n /\ x = sname j`
  >- (qpat_x_assum `?j. _` strip_assume_tac >> rw[] >>
      metis_tac[upd_from_in])
  >- (fs[] >> metis_tac[upd_from_out])
QED

Theorem sholds_sforall_from:
  !D n k f v.
    sholds (rec_model D) v (sforall_from k n f) <=>
    !h. (!j. k <= j /\ j < k + n ==> h j IN D) ==>
        sholds (rec_model D) (upd_from k n h v) f
Proof
  gen_tac >> Induct >>
  rw[sforall_from_def, upd_from_def, sholds_sforall_state] >>
  EQ_TAC >> rw[] >>
  TRY (first_x_assum (qspecl_then [`h k`, `h`] mp_tac) >> rw[] >>
       first_x_assum irule >> rw[] >> first_x_assum irule >> decide_tac >>
       NO_TAC) >>
  first_x_assum (qspec_then `(k =+ s) h` mp_tac) >> rw[APPLY_UPDATE_THM] >>
  `upd_from (k + 1) n ((k =+ s) h) ((sname k =+ INR s) v) =
   upd_from (k + 1) n h ((sname k =+ INR s) v)`
    by (irule upd_from_cong >> rw[APPLY_UPDATE_THM]) >>
  fs[] >> first_x_assum irule >> rw[] >> first_x_assum irule >>
  decide_tac
QED

(* ------------------------------------------------------------------------ *)
(* Index bound                                                              *)
(* ------------------------------------------------------------------------ *)

(* tc_i(S), ftc_i(S, ...) and pcc_i(S, ...) only mention the state
   variables s(k) with i <= k <= i + stb S *)
Definition stb_def:
  (stb S_skip = 1:num) /\
  (stb (S_assign x a) = 1) /\
  (stb (S_call m) = 2) /\
  (stb (S_ifelse b S1 S2) = 1 + stb S1 + stb S2) /\
  (stb (S_seq S1 S2) = stb S1 + stb S2) /\
  (stb (S_var Y) = 1)
End

Theorem stb_pos:
  !S0. 1 <= stb S0
Proof
  Induct >> rw[stb_def] >> decide_tac
QED

(* index arithmetic: add 1 <= stb S for every stb S in the goal *)
val stb_tm = prim_mk_const {Thy = "vcGen", Name = "stb"};

val stb_arith_tac : tactic = fn (asl, w) =>
  let val ts = find_terms (fn t => is_comb t andalso
                                   same_const (rator t) stb_tm) w
  in (MAP_EVERY (fn t => assume_tac (SPEC (rand t) stb_pos)) ts >>
      decide_tac) (asl, w)
  end;

(* for every state variable s(k) in the goal, add
   stermval (rec_model D) v (svar k) = INR (g k), using vagree _ _ v g *)
val svar_tm = prim_mk_const {Thy = "folRec", Name = "svar"};

val svar_tac : tactic = fn (asl, w) =>
  let
    val ks = map rand (find_terms (fn t => is_comb t andalso
                                           same_const (rator t) svar_tm) w)
    fun fact k =
      let val v = mk_var ("v", ``:string -> rdom``)
          val g = mk_var ("g", ``:num -> state``)
          val D = mk_var ("D", ``:state set``)
      in ``stermval (rec_model ^D) ^v (svar ^k) = INR (^g ^k)`` end
    fun add k =
      TRY (SUBGOAL_THEN (fact k) assume_tac THEN1
             (irule stermval_svar >> first_assum (irule_at Any) >>
              simp[stb_def] >> stb_arith_tac))
  in MAP_EVERY add (op_mk_set aconv ks) (asl, w) end;

(* evaluate the atoms of a generated formula *)
val atoms_tac =
  TRY (simp[] >> NO_TAC) >>
  svar_tac >>
  imp_res_tac sholds_b2sform >> imp_res_tac sholds_Id_sform >>
  imp_res_tac sholds_Sb_sform >> imp_res_tac sholds_pre_sform >>
  imp_res_tac sholds_post_sform >> fs[];

(* Like atoms_tac, but adds only the instantiated equivalences for the
   known values of terms (stermval (rec_model D) v t = INR s), so that fs does
   not rewrite back and forth with both directions of each. *)
val atoms1 = [sholds_b2sform, sholds_pre_sform, stermval_a2sterm];
val atoms2 = map (REWRITE_RULE [GSYM AND_IMP_INTRO])
               [sholds_Id_sform, sholds_Sb_sform, sholds_post_sform];

val atoms_eq_tac : tactic = fn (asl, w) =>
  let
    fun is_fact t =
      let val (l, r) = dest_eq t
      in is_comb r andalso
         (fst (dest_const (fst (strip_comb r))) = "INR" handle _ => false) andalso
         (fst (dest_const (fst (strip_comb l))) = "stermval" handle _ => false)
      end handle _ => false
    val facts = map ASSUME (filter is_fact asl)
    fun mp l f = [MATCH_MP l f] handle _ => []
    val new1 = List.concat (map (fn l => List.concat (map (mp l) facts)) atoms1)
    val new2 = List.concat (map (fn l => List.concat (map (fn f1 =>
                 List.concat (map (fn th => List.concat (map (mp th) facts))
                                  (mp l f1))) facts)) atoms2)
  in (MAP_EVERY assume_tac (new1 @ new2) >> fs[]) (asl, w) end;

(* use the induction hypotheses for v and g *)
val ih_tac =
  rpt (first_x_assum (fn th =>
         mp_tac (Q.SPECL [`v`, `g`] th) >>
         impl_tac >- (irule vagree_mono >> first_assum (irule_at Any) >>
                      simp[stb_def] >> stb_arith_tac) >>
         disch_then SUBST_ALL_TAC));

(* ------------------------------------------------------------------------ *)
(* Definition 4.17                                                          *)
(* ------------------------------------------------------------------------ *)

Definition pred_fol_def:
  (pred_fol (n:num) (i:num) (f_state (p_b b)) = b2sform (svar i) b) /\
  (pred_fol n i (f_rel R_Id) = Id_sform (svar i) (svar (i + 1))) /\
  (pred_fol n i (f_rel (R_Sb a x)) = Sb_sform x a (svar i) (svar (i + 1))) /\
  (pred_fol n i (f_rel (R_other q)) = SFalse) /\
  (pred_fol n i (f_recvar X) = SFalse) /\
  (pred_fol n i (f_and f1 f2) = SAnd (pred_fol n i f1) (pred_fol n i f2)) /\
  (pred_fol n i (f_or f1 f2) = SOr (pred_fol n i f1) (pred_fol n i f2)) /\
  (pred_fol n i (f_chop f1 f2) = SFalse) /\
  (pred_fol 0 i (f_mu X f) = SFalse) /\
  (pred_fol (SUC n) i (f_mu X f) = pred_fol n i (subst_f (f_mu X f) X f))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\(n,i,f). (n, f_size f))` >>
  rw[f_size_def]
End

Theorem pred_fol_sem:
  !D n i f v g.
    vagree i (i + 1) v g ==>
    (sholds (rec_model D) v (pred_fol n i f) <=> pred n i f g)
Proof
  gen_tac >> recInduct pred_fol_ind >> rw[pred_fol_def, pred_def, sholds_def] >>
  ih_tac >> atoms_tac
QED

(* ------------------------------------------------------------------------ *)
(* Definition 4.13                                                          *)
(* ------------------------------------------------------------------------ *)

Definition tc_fol_def:
  (tc_fol (ct:ctable) (i:num) S_skip = Id_sform (svar i) (svar (i + 1))) /\
  (tc_fol ct i (S_assign x a) = Sb_sform x a (svar i) (svar (i + 1))) /\
  (tc_fol ct i (S_ifelse b S1 S2) =
     SAnd (Id_sform (svar i) (svar (i + 1)))
          (SAnd (SImp (b2sform (svar i) b) (tc_fol ct (i + 1) S1))
                (SImp (SNot (b2sform (svar i) b)) (tc_fol ct (i + 1) S2)))) /\
  (tc_fol ct i (S_call m) =
     SAnd (Id_sform (svar i) (svar (i + 1)))
          (SImp (pre_sform ct m (svar (i + 1)))
                (post_sform ct m (svar (i + 1)) (svar (i + 2))))) /\
  (tc_fol ct i (S_seq (S_call m) S2) =
     SAnd (tc_fol ct i (S_call m)) (tc_fol ct (i + 2) S2)) /\
  (tc_fol ct i (S_seq (S_seq S1 S2) S3) =
     tc_fol ct i (S_seq S1 (S_seq S2 S3))) /\
  (tc_fol ct i (S_seq S1 S2) =
     SAnd (tc_fol ct i S1) (tc_fol ct (i + 1) S2)) /\
  (tc_fol ct i (S_var Y) = STrue)
Termination
  WF_REL_TAC `measure (\(ct,i,S0). seqw S0)` >> rw[seqw_def]
End

Theorem tc_fol_sem:
  !D ct i S0 v g.
    vagree i (i + stb S0) v g ==>
    (sholds (rec_model D) v (tc_fol ct i S0) <=>
     tc (cpre ct) (cpost ct) i S0 g)
Proof
  gen_tac >> recInduct tc_fol_ind >> rw[tc_fol_def, tc_def, sholds_def, stb_def] >>
  ih_tac >> atoms_tac
QED

(* ------------------------------------------------------------------------ *)
(* Definition 4.28                                                          *)
(* ------------------------------------------------------------------------ *)

(* The side condition for a first call of m quantifies over the state
   variables s(1) ... s(1 + stb body) of the body. *)
Definition ftc_fol_def:
  (ftc_fol (lk:lookup) (ct:ctable) 0 (i:num) S0 phi
           (X:(string # f) list) = SFalse) /\
  (ftc_fol lk ct (SUC n) i S0 phi X =
     case phi of
       f_mu Y psi => ftc_fol lk ct n i S0 (subst_f (f_mu Y psi) Y psi) X
     | f_chop (f_mu Y psi) phi2 =>
         ftc_fol lk ct n i S0
                 (distr (f_chop (subst_f (f_mu Y psi) Y psi) phi2)) X
     | f_or phi1 phi2 =>
         SOr (ftc_fol lk ct n i S0 phi1 X) (ftc_fol lk ct n i S0 phi2 X)
     | f_and phi1 phi2 =>
         SAnd (ftc_fol lk ct n i S0 phi1 X) (ftc_fol lk ct n i S0 phi2 X)
     | _ => ftc0_fol lk ct n i S0 phi X) /\
  (ftc0_fol lk ct n i S_skip phi X = pred_fol n i phi) /\
  (ftc0_fol lk ct n i (S_assign x a) phi X = pred_fol n i phi) /\
  (ftc0_fol lk ct n i (S_ifelse b S1 S2) phi X =
     case phi of
       f_chop phi1 phi2 =>
         SAnd (pred_fol n i phi1)
              (SAnd (SImp (b2sform (svar i) b)
                          (ftc_fol lk ct n (i + 1) S1 phi2 X))
                    (SImp (SNot (b2sform (svar i) b))
                          (ftc_fol lk ct n (i + 1) S2 phi2 X)))
     | _ => SFalse) /\
  (ftc0_fol lk ct n i (S_call m) phi X =
     case phi of
       f_chop phi1 (f_mu Y psi) =>
         SAnd (pre_sform ct m (svar (i + 1)))
              (SAnd (pred_fol n i phi1)
                    (if MEM (m, f_mu Y psi) X then STrue
                     else
                       case lk m of
                         SOME body =>
                           sforall_from 1 (SUC (stb body))
                             (SImp (SAnd (tc_fol ct 1 body)
                                         (pre_sform ct m (svar 1)))
                                   (ftc_fol lk ct n 1 body
                                      (subst_f (f_mu Y psi) Y psi)
                                      ((m, f_mu Y psi)::X)))
                       | NONE => SFalse))
     | _ => SFalse) /\
  (ftc0_fol lk ct n i (S_seq S1 S2) phi X =
     case (S1, phi) of
       (S_skip, f_chop phi1 phi2) =>
         SAnd (pred_fol n i phi1) (ftc_fol lk ct n (i + 1) S2 phi2 X)
     | (S_assign x a, f_chop phi1 phi2) =>
         SAnd (pred_fol n i phi1) (ftc_fol lk ct n (i + 1) S2 phi2 X)
     | (S_call m, f_chop phi1 (f_chop phi2 phi3)) =>
         SAnd (ftc_fol lk ct n i (S_call m) (f_chop phi1 phi2) X)
              (ftc_fol lk ct n (i + 2) S2 phi3 X)
     | _ => SFalse) /\
  (ftc0_fol lk ct n i (S_var Y) phi X = SFalse)
Termination
  WF_REL_TAC `measure (\x. case x of
                 INL (lk,ct,n,i,S0,phi,X) => 2 * n
               | INR (lk,ct,n,i,S0,phi,X) => 2 * n + 1)` >>
  rw[]
End

(* the side condition of a first call, for any formula Fm that holds
   exactly when P holds of the state sequence *)
Theorem sholds_side_condition:
  !D ct m body Fm P v.
    (!v g. vagree 1 (stb body + 1) v g ==>
           (sholds (rec_model D) v Fm <=> P g)) ==>
    (sholds (rec_model D) v
       (sforall_from 1 (SUC (stb body))
          (SImp (SAnd (tc_fol ct 1 body) (pre_sform ct m (svar 1))) Fm)) <=>
     !h. (!j. 1 <= j /\ j <= stb body + 1 ==> h j IN D) /\
         tc (cpre ct) (cpost ct) 1 body h /\ cpre ct m (h 1) ==> P h)
Proof
  rw[sholds_sforall_from, sholds_def] >>
  `!h. vagree 1 (1 + stb body) (upd_from 1 (SUC (stb body)) h v) h`
    by metis_tac[vagree_upd_from] >>
  `!h. stermval (rec_model D) (upd_from 1 (SUC (stb body)) h v) (svar 1) =
       INR (h 1)`
    by (rw[] >> irule stermval_svar >>
        qexistsl_tac [`1 + stb body`, `1`] >> rw[]) >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb body)) h v)
         (tc_fol ct 1 body) <=> tc (cpre ct) (cpost ct) 1 body h`
    by (gen_tac >> irule tc_fol_sem >> metis_tac[ADD_COMM]) >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb body)) h v)
         (pre_sform ct m (svar 1)) <=> cpre ct m (h 1)`
    by (gen_tac >> irule sholds_pre_sform >> rw[]) >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb body)) h v) Fm <=> P h`
    by (rw[] >> first_x_assum irule >> metis_tac[ADD_COMM]) >>
  fs[] >> EQ_TAC >> rw[] >> first_x_assum irule >> rw[] >>
  first_x_assum irule >> decide_tac
QED

(* rewrite every pred_fol n k f in the goal with pred_fol_sem *)
val pred_fol_tm = prim_mk_const {Thy = "vcGen", Name = "pred_fol"};

val pred_tac : tactic = fn (asl, w) =>
  let
    val ts = find_terms (fn t => let val (f, args) = strip_comb t
                                 in same_const f pred_fol_tm andalso
                                    length args = 3 end) w
    val v = mk_var ("v", ``:string -> rdom``)
    val g = mk_var ("g", ``:num -> state``)
    val D = mk_var ("D", ``:state set``)
    fun rw1 t =
      let val (_, [n, k, f]) = strip_comb t
      in
        TRY (SUBGOAL_THEN ``sholds (rec_model ^D) ^v ^t <=> pred ^n ^k ^f ^g``
               SUBST_ALL_TAC THEN1
               (irule pred_fol_sem >> irule vagree_mono >>
                first_assum (irule_at Any) >> simp[stb_def] >>
                stb_arith_tac))
      end
  in MAP_EVERY rw1 (op_mk_set aconv ts) (asl, w) end;

(* ftc and ftc0 of verifFtc, where the side condition of a first call
   quantifies over the state sequences h with h j in D for the state
   variables s(j) of the side condition (1 <= j <= stb body + 1). With
   D = UNIV this is ftc (ftc_dom_univ). *)
Definition ftc_dom_def:
  (ftc_dom (D:state set) (lk:lookup) pre post 0 (i:num) S0 phi
           (X:(string # f) list) (g:num -> state) = F) /\
  (ftc_dom D lk pre post (SUC n) i S0 phi X g =
     case phi of
       f_mu Y psi =>
         ftc_dom D lk pre post n i S0 (subst_f (f_mu Y psi) Y psi) X g
     | f_chop (f_mu Y psi) phi2 =>
         ftc_dom D lk pre post n i S0
             (distr (f_chop (subst_f (f_mu Y psi) Y psi) phi2)) X g
     | f_or phi1 phi2 =>
         (ftc_dom D lk pre post n i S0 phi1 X g \/
          ftc_dom D lk pre post n i S0 phi2 X g)
     | f_and phi1 phi2 =>
         (ftc_dom D lk pre post n i S0 phi1 X g /\
          ftc_dom D lk pre post n i S0 phi2 X g)
     | _ => ftc0_dom D lk pre post n i S0 phi X g) /\
  (ftc0_dom D lk pre post n i S_skip phi X g = pred n i phi g) /\
  (ftc0_dom D lk pre post n i (S_assign x a) phi X g = pred n i phi g) /\
  (ftc0_dom D lk pre post n i (S_ifelse b S1 S2) phi X g =
     case phi of
       f_chop phi1 phi2 =>
         (pred n i phi1 g /\
          (b_eval b (g i) ==> ftc_dom D lk pre post n (i + 1) S1 phi2 X g) /\
          (~b_eval b (g i) ==> ftc_dom D lk pre post n (i + 1) S2 phi2 X g))
     | _ => F) /\
  (ftc0_dom D lk pre post n i (S_call m) phi X g =
     case phi of
       f_chop phi1 (f_mu Y psi) =>
         (pre m (g (i + 1)) /\ pred n i phi1 g /\
          if MEM (m, f_mu Y psi) X then T
          else
            case lk m of
              SOME body =>
                !h. (!j. 1 <= j /\ j <= stb body + 1 ==> h j IN D) /\
                    tc pre post 1 body h /\ pre m (h 1) ==>
                    ftc_dom D lk pre post n 1 body
                            (subst_f (f_mu Y psi) Y psi)
                            ((m, f_mu Y psi)::X) h
            | NONE => F)
     | _ => F) /\
  (ftc0_dom D lk pre post n i (S_seq S1 S2) phi X g =
     case (S1, phi) of
       (S_skip, f_chop phi1 phi2) =>
         (pred n i phi1 g /\ ftc_dom D lk pre post n (i + 1) S2 phi2 X g)
     | (S_assign x a, f_chop phi1 phi2) =>
         (pred n i phi1 g /\ ftc_dom D lk pre post n (i + 1) S2 phi2 X g)
     | (S_call m, f_chop phi1 (f_chop phi2 phi3)) =>
         (ftc_dom D lk pre post n i (S_call m) (f_chop phi1 phi2) X g /\
          ftc_dom D lk pre post n (i + 2) S2 phi3 X g)
     | _ => F) /\
  (ftc0_dom D lk pre post n i (S_var Y) phi X g = F)
Termination
  WF_REL_TAC `measure (\x. case x of
                 INL (D,lk,pre,post,n,i,S0,phi,X,g) => 2 * n
               | INR (D,lk,pre,post,n,i,S0,phi,X,g) => 2 * n + 1)` >>
  rw[]
End

Theorem ftc_dom_univ:
  (!lk pre post n i S0 phi X g.
     ftc_dom UNIV lk pre post n i S0 phi X g <=>
     ftc lk pre post n i S0 phi X g) /\
  (!lk pre post n i S0 phi X g.
     ftc0_dom UNIV lk pre post n i S0 phi X g <=>
     ftc0 lk pre post n i S0 phi X g)
Proof
  ho_match_mp_tac ftc_ind >> rpt conj_tac >> rpt strip_tac >>
  simp[Once ftc_dom_def, Once ftc_def] >>
  rpt CASE_TAC >> fs[] >>
  rename1 `MEM (m, mu) X` >> Cases_on `MEM (m, mu) X` >> fs[] 

QED

Theorem ftc_fol_sem:
  !D.
  (!lk ct n i S0 phi X v g.
     vagree i (i + stb S0) v g ==>
     (sholds (rec_model D) v (ftc_fol lk ct n i S0 phi X) <=>
      ftc_dom D lk (cpre ct) (cpost ct) n i S0 phi X g)) /\
  (!lk ct n i S0 phi X v g.
     vagree i (i + stb S0) v g ==>
     (sholds (rec_model D) v (ftc0_fol lk ct n i S0 phi X) <=>
      ftc0_dom D lk (cpre ct) (cpost ct) n i S0 phi X g))
Proof
  gen_tac >>
  ho_match_mp_tac ftc_fol_ind >> rpt conj_tac >> rpt strip_tac >>
  simp[Once ftc_fol_def, Once ftc_dom_def] >>
  TRY (simp[sholds_def] >> NO_TAC) >>
  rpt CASE_TAC >> fs[sholds_def] >>
  ih_tac >> pred_tac >> TRY (simp[] >> NO_TAC) >> svar_tac >> atoms_eq_tac >>
  qpat_x_assum `!v g. vagree 1 _ v g ==> _`
    (fn ih => rewrite_tac [MATCH_MP sholds_side_condition ih])
QED



(* ------------------------------------------------------------------------ *)
(* Definition 4.34                                                          *)
(* ------------------------------------------------------------------------ *)

(* pcc_i(S, Post_m) with initial state st0 *)
Definition pcc_fol_def:
  (pcc_fol (ct:ctable) m st0 (i:num) (S_assign x a) =
     SImp (Sb_sform x a (svar i) (svar (i + 1)))
          (post_sform ct m st0 (svar (i + 1)))) /\
  (pcc_fol ct m st0 i S_skip =
     SImp (Id_sform (svar i) (svar (i + 1)))
          (post_sform ct m st0 (svar (i + 1)))) /\
  (pcc_fol ct m st0 i (S_ifelse b S1 S2) =
     SImp (Id_sform (svar i) (svar (i + 1)))
          (SAnd (SImp (b2sform (svar i) b) (pcc_fol ct m st0 (i + 1) S1))
                (SImp (SNot (b2sform (svar i) b))
                      (pcc_fol ct m st0 (i + 1) S2)))) /\
  (pcc_fol ct m st0 i (S_call m') =
     SImp (SAnd (Id_sform (svar i) (svar (i + 1)))
                (SImp (pre_sform ct m' (svar (i + 1)))
                      (post_sform ct m' (svar (i + 1)) (svar (i + 2)))))
          (post_sform ct m st0 (svar (i + 2)))) /\
  (pcc_fol ct m st0 i (S_seq (S_assign x a) S2) =
     SImp (Sb_sform x a (svar i) (svar (i + 1)))
          (pcc_fol ct m st0 (i + 1) S2)) /\
  (pcc_fol ct m st0 i (S_seq S_skip S2) =
     SImp (Id_sform (svar i) (svar (i + 1))) (pcc_fol ct m st0 (i + 1) S2)) /\
  (pcc_fol ct m st0 i (S_seq (S_call m') S2) =
     SImp (SAnd (Id_sform (svar i) (svar (i + 1)))
                (SImp (pre_sform ct m' (svar (i + 1)))
                      (post_sform ct m' (svar (i + 1)) (svar (i + 2)))))
          (pcc_fol ct m st0 (i + 2) S2)) /\
  (pcc_fol ct m st0 i (S_seq S1 S2) = SFalse) /\
  (pcc_fol ct m st0 i (S_var Y) = SFalse)
End

Theorem pcc_fol_sem:
  !D ct m st0 i S0 v g s0.
    vagree i (i + stb S0) v g /\ stermval (rec_model D) v st0 = INR s0 ==>
    (sholds (rec_model D) v (pcc_fol ct m st0 i S0) <=>
     pcc (cpre ct) (cpost ct) (cpost ct m) s0 i S0 g)
Proof
  gen_tac >> recInduct pcc_fol_ind >>
  rw[pcc_fol_def, pcc_def, sholds_def, stb_def] >>
  rpt (first_x_assum (fn th =>
         mp_tac (Q.SPECL [`v`, `g`, `s0`] th) >>
         impl_tac >- (rw[] >> irule vagree_mono >>
                      first_assum (irule_at Any) >> simp[stb_def] >>
                      stb_arith_tac) >>
         disch_then SUBST_ALL_TAC)) >>
  svar_tac >> atoms_eq_tac
QED

(* forall s. Pre_m(s(1)) ==> pcc_1(S_m, Post_m), as one closed formula *)
Definition pcc_valid_fol_def:
  pcc_valid_fol ct m body =
    sforall_from 1 (SUC (stb body))
      (SImp (pre_sform ct m (svar 1)) (pcc_fol ct m (svar 1) 1 body))
End

Theorem sholds_pcc_valid_fol:
  !D ct m body v.
    sholds (rec_model D) v (pcc_valid_fol ct m body) <=>
    !g. (!j. 1 <= j /\ j <= stb body + 1 ==> g j IN D) /\ cpre ct m (g 1) ==>
        pcc (cpre ct) (cpost ct) (cpost ct m) (g 1) 1 body g
Proof
  rw[pcc_valid_fol_def, sholds_sforall_from, sholds_def] >>
  `!h. vagree 1 (1 + stb body) (upd_from 1 (SUC (stb body)) h v) h`
    by metis_tac[vagree_upd_from] >>
  `!h. stermval (rec_model D) (upd_from 1 (SUC (stb body)) h v) (svar 1) =
       INR (h 1)`
    by (rw[] >> irule stermval_svar >>
        qexistsl_tac [`1 + stb body`, `1`] >> rw[]) >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb body)) h v)
         (pre_sform ct m (svar 1)) <=> cpre ct m (h 1)`
    by (gen_tac >> irule sholds_pre_sform >> rw[]) >>
  `!h. sholds (rec_model D) (upd_from 1 (SUC (stb body)) h v)
         (pcc_fol ct m (svar 1) 1 body) <=>
       pcc (cpre ct) (cpost ct) (cpost ct m) (h 1) 1 body h`
    by (gen_tac >> irule pcc_fol_sem >> rw[] >> metis_tac[ADD_COMM]) >>
  fs[] >> EQ_TAC >> rw[] >> first_x_assum irule >> rw[] >>
  first_x_assum irule >> decide_tac
QED
