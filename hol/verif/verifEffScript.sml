(* Procedure contracts (thesis Definitions 4.5 and 4.6), effective traces
   (thesis Definition 4.8, corrected) and the correspondence between
   positions in a state sequence and a trace. *)

Theory verifEff
Ancestors
  arithmetic pred_set list rich_list alist combin traces tracesSem verifChop

(* ------------------------------------------------------------------------ *)
(* Procedure contracts                                                      *)
(* ------------------------------------------------------------------------ *)

(* Statement variables are not part of the thesis language, so all
   statement semantics below use the empty interpretation K {} of them;
   statement variables then have no traces. *)

(* m conforms with <pre m, post m> (Definition 4.6), for every m *)
Definition conforms_def:
  conforms (lk:lookup) (pre:string -> state -> bool)
           (post:string -> state -> state -> bool) =
    !m t. t IN Str lk (K {}) (S_call m) /\ pre m (HD t) ==>
          post m (HD t) (LAST t)
End

Theorem Str_call_cases:
  !lk iv m t. t IN Str lk iv (S_call m) ==>
    ?body s r. lk m = SOME body /\ t = s::s::r /\ s::r IN Str lk iv body
Proof
  rw[] >> Cases_on `lk m`
  >- (fs[Str_def, Str0_def] >>
      `rho0 lk iv m = H lk iv (rho0 lk iv) m` by metis_tac[rho0_fixpoint] >>
      fs[H_def])
  >- (drule Str_call >> disch_then (qspec_then `iv` assume_tac) >>
      fs[dup_def])
QED

(* ------------------------------------------------------------------------ *)
(* Effective traces                                                         *)
(* ------------------------------------------------------------------------ *)

(* eff lk S t u: u is the effective trace of the trace t of S. Every call
   m() of S itself (not of the procedure bodies) contributes only its
   initial state, the duplicated initial state and its final state. The
   thesis's Definition 4.8 abstracts only a call at the top level, but its
   proofs use this compositional version. Relating t and u directly avoids
   the bijection of Lemma 4.9 and the determinism of Rec. *)
Inductive eff:
[eff_skip:]
  (!s. eff lk S_skip [s; s] [s; s])
[eff_assign:]
  (!x a s. eff lk (S_assign x a) [s; (x =+ a_eval a s) s]
                                 [s; (x =+ a_eval a s) s])
[eff_seq:]
  (!S1 S2 t1 t2 u1 u2.
     eff lk S1 t1 u1 /\ eff lk S2 t2 u2 /\ LAST t1 = HD t2 ==>
     eff lk (S_seq S1 S2) (t1 ++ TL t2) (u1 ++ TL u2))
[eff_if_t:]
  (!b S1 S2 s r q.
     b_eval b s /\ eff lk S1 (s::r) (s::q) ==>
     eff lk (S_ifelse b S1 S2) (s::s::r) (s::s::q))
[eff_if_f:]
  (!b S1 S2 s r q.
     ~b_eval b s /\ eff lk S2 (s::r) (s::q) ==>
     eff lk (S_ifelse b S1 S2) (s::s::r) (s::s::q))
[eff_call:]
  (!m t. t IN Str lk (K {}) (S_call m) ==>
         eff lk (S_call m) t [HD t; HD t; LAST t])
End

Theorem fuse_props:
  !l1 l2. 2 <= LENGTH l1 /\ 2 <= LENGTH l2 ==>
          2 <= LENGTH (l1 ++ TL l2) /\ HD (l1 ++ TL l2) = HD l1 /\
          LAST (l1 ++ TL l2) = LAST l2
Proof
  Cases >> Cases >> fs[] >> Cases_on `t'` >> fs[LAST_APPEND_CONS, LAST_CONS] >>
  metis_tac[LAST_APPEND_CONS, APPEND]
QED

Theorem eff_props:
  !lk S0 t u. eff lk S0 t u ==>
    2 <= LENGTH t /\ 2 <= LENGTH u /\ HD u = HD t /\ LAST u = LAST t
Proof
  gen_tac >> ho_match_mp_tac eff_ind >> rw[fuse_props] >>
  drule Str_call_cases >> rw[] >> rw[]
QED

Theorem eff_HD:
  !lk S0 t u. eff lk S0 t u ==> t <> [] /\ u <> [] /\ HD u = HD t
Proof
  rpt gen_tac >> strip_tac >> drule eff_props >> Cases_on `t` >>
  Cases_on `u` >> fs[]
QED

Theorem eff_LAST:
  !lk S0 t u. eff lk S0 t u ==> LAST u = LAST t
Proof
  metis_tac[eff_props]
QED

(* only traces of S have effective traces *)
Theorem eff_Str:
  !lk S0 t u. eff lk S0 t u ==> t IN Str lk (K {}) S0
Proof
  gen_tac >> ho_match_mp_tac eff_strongind >>
  rw[Str_def, Str0_def, restrict_def, dup_def, b_eval_def]
  >- (fs[GSYM Str_def] >> irule chop_intro >> rw[] >>
      imp_res_tac eff_props >> CCONTR_TAC >> fs[])
QED

(* every trace has an effective trace *)
Theorem Str_eff:
  !lk S0 t. t IN Str lk (K {}) S0 ==> ?u. eff lk S0 t u
Proof
  gen_tac >> Induct >> rw[Str_def, Str0_def]
  >- metis_tac[eff_rules]
  >- metis_tac[eff_rules]
  >- (fs[IN_chop, GSYM Str_def] >> res_tac >>
      metis_tac[eff_rules])
  >- (fs[restrict_def, dup_def, GSYM Str_def] >> res_tac >>
      imp_res_tac eff_HD >> Cases_on `u` >> fs[] >>
      metis_tac[eff_rules])
  >- (fs[restrict_def, dup_def, GSYM Str_def, b_eval_def] >> res_tac >>
      imp_res_tac eff_HD >> Cases_on `u` >> fs[] >>
      metis_tac[eff_rules])
  >- (qexists_tac `[HD t; HD t; LAST t]` >> irule eff_call >>
      rw[Str_def, Str0_def])
QED

(* ------------------------------------------------------------------------ *)
(* State sequences                                                          *)
(* ------------------------------------------------------------------------ *)

(* A state sequence is a function g from positions to states (the
   s^(i) of the thesis). agree i u g: g lists the trace u from position i
   on. Positions after the trace are arbitrary (the padding of Example
   4.3). *)
Definition agree_def:
  (agree (i:num) [] (g:num -> state) = T) /\
  (agree i (s::u) g = (g i = s /\ agree (i + 1) u g))
End

Theorem agree_append:
  !u1 u2 i g. agree i (u1 ++ u2) g <=>
              agree i u1 g /\ agree (i + LENGTH u1) u2 g
Proof
  Induct >> rw[agree_def, ADD1] >> metis_tac[ADD_ASSOC, ADD_COMM]
QED

Theorem agree_LAST:
  !u i g. agree i u g /\ u <> [] ==> g (i + LENGTH u - 1) = LAST u
Proof
  Induct >> rw[agree_def] >> Cases_on `u` >> fs[agree_def] >>
  first_x_assum (qspecl_then [`i + 1`, `g`] mp_tac) >> rw[ADD1]
QED

(* splitting the effective trace of a sequence *)
Theorem agree_fuse:
  !u1 u2 i g.
    agree i (u1 ++ TL u2) g /\ u1 <> [] /\ u2 <> [] /\ LAST u1 = HD u2 ==>
    agree i u1 g /\ agree (i + LENGTH u1 - 1) u2 g
Proof
  rw[agree_append] >> Cases_on `u2` >> fs[agree_def] >>
  drule_all agree_LAST >> rw[] >>
  Cases_on `u1` >> fs[ADD1]
QED

Theorem agree_update:
  !u i j s g. j < i ==> (agree i u ((j =+ s) g) <=> agree i u g)
Proof
  Induct >> rw[agree_def, APPLY_UPDATE_THM]
QED

Theorem agree_exists:
  !u i. ?g. agree i u g
Proof
  Induct >> rw[agree_def] >>
  first_x_assum (qspec_then `i + 1` strip_assume_tac) >>
  qexists_tac `(i =+ h) g` >> rw[APPLY_UPDATE_THM, agree_update]
QED
