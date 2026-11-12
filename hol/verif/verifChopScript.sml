(* Generic facts about the chop operator on trace sets, used by the
   formalization of the finite-trace calculus (thesis Chapter 4). *)

Theory verifChop
Ancestors
  pred_set list rich_list tracesSem

Theorem chop_intro:
  !A B t1 t2.
    t1 IN A /\ t2 IN B /\ t1 <> [] /\ t2 <> [] /\ LAST t1 = HD t2 ==>
    t1 ++ TL t2 IN chop A B
Proof
  rw[chop_def] >>
  qexistsl_tac [`FRONT t1`, `HD t2`, `TL t2`] >>
  Cases_on `t2` >> fs[] >> metis_tac[APPEND_FRONT_LAST]
QED

Theorem chop_intro_pair:
  !A B s s' r. [s; s'] IN A /\ s'::r IN B ==> s::s'::r IN chop A B
Proof
  rw[] >> qspecl_then [`A`, `B`, `[s; s']`, `s'::r`] mp_tac chop_intro >>
  rw[]
QED

(* characterisation of chop by the two traces it fuses *)
Theorem IN_chop:
  !A B t. t IN chop A B <=>
          ?t1 t2. t1 IN A /\ t2 IN B /\ t1 <> [] /\ t2 <> [] /\
                  LAST t1 = HD t2 /\ t = t1 ++ TL t2
Proof
  rw[EQ_IMP_THM]
  >- (fs[chop_def] >> qexistsl_tac [`l1 ++ [s]`, `s::l2`] >> rw[])
  >- metis_tac[chop_intro]
QED

Theorem chop_assoc:
  !A B C. chop (chop A B) C = chop A (chop B C)
Proof
  rw[EXTENSION, IN_chop, EQ_IMP_THM, PULL_EXISTS] >> rw[]
  >- (qexistsl_tac [`t1'`, `t2'`, `t2`] >>
      Cases_on `t2'` >> fs[] >> Cases_on `t2` >> fs[] >>
      Cases_on `t` >> fs[LAST_APPEND_CONS])
  >- (qexistsl_tac [`t2'`, `t1`, `t1'`] >>
      Cases_on `t1'` >> fs[] >> Cases_on `t2'` >> fs[] >>
      Cases_on `t` >> fs[LAST_APPEND_CONS])
QED

Theorem chop_union_l:
  !A B C. chop (A UNION B) C = chop A C UNION chop B C
Proof
  rw[chop_def, EXTENSION] >> metis_tac[]
QED

Theorem chop_union_r:
  !A B C. chop A (B UNION C) = chop A B UNION chop A C
Proof
  rw[chop_def, EXTENSION] >> metis_tac[]
QED

Theorem chop_restrict_l:
  !b A C. chop (restrict b A) C = restrict b (chop A C)
Proof
  rw[chop_def, restrict_def, EXTENSION, EQ_IMP_THM, PULL_EXISTS] >>
  Cases_on `l1` >> fs[] >> rw[] >> metis_tac[APPEND]
QED

Theorem chop_dup_l:
  !A C. chop (dup A) C = dup (chop A C)
Proof
  rw[IN_chop, dup_def, EXTENSION, EQ_IMP_THM, PULL_EXISTS]
  >- (qexistsl_tac [`s::r`, `t2`] >> fs[] >> Cases_on `r` >> fs[])
  >- (qexistsl_tac [`t2`, `TL t1`] >> Cases_on `t1` >> fs[] >>
      Cases_on `t` >> fs[])
QED
