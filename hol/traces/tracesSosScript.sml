(* Theorem 3.2: the denotational finite-trace semantics coincides with the
   finite-trace semantics induced by the SOS. *)

Theory tracesSos
Ancestors
  pred_set list rich_list alist combin ott traces tracesSem

(* S_sos[[S]] of Definition 2.6 *)
Definition Ssos_def:
  Ssos tbl S0 = {t | sos_tr tbl S0 t}
End

(* procedure tables whose bodies contain no statement variables *)
Definition tbl_var_free_def:
  tbl_var_free tbl = !m body. ALOOKUP tbl m = SOME body ==> var_free body
End

val c_red_rules = CONJUNCTS sos_defs_rules;
val sos_rule = fn n => List.nth (c_red_rules, n) |> SIMP_RULE std_ss [clause_name_def];
val [r_skip, r_assign, r_seq1, r_seq2, r_if1, r_if2, r_call, r_end, r_step] =
  List.tabulate (9, sos_rule);

(* ------------------------------------------------------------------------ *)
(* Direction Ssos <= Str                                                     *)
(* ------------------------------------------------------------------------ *)

Theorem c_red_final:
  !tbl S0 s s' rho iv.
    c_red tbl (c_tuple S0 s) (c_state s') ==> [s; s'] IN Str0 rho iv S0
Proof
  rw[Once sos_defs_cases, clause_name_def] >> rw[Str0_def]
QED

Theorem c_red_step:
  !tbl c c'. c_red tbl c c' ==>
    !S0 s S1 s' r iv. c = c_tuple S0 s /\ c' = c_tuple S1 s' /\
      s'::r IN Str (ALOOKUP tbl) iv S1 ==>
      s::s'::r IN Str (ALOOKUP tbl) iv S0
Proof
  `!tbl c c'. c_red tbl c c' ==>
     !S0 s S1 s' r iv. c = c_tuple S0 s /\ c' = c_tuple S1 s' /\
       s'::r IN Str (ALOOKUP tbl) iv S1 ==>
       s::s'::r IN Str (ALOOKUP tbl) iv S0` suffices_by metis_tac[] >>
  `(!tbl c c'. c_red tbl c c' ==>
     !S0 s S1 s' r iv. c = c_tuple S0 s /\ c' = c_tuple S1 s' /\
       s'::r IN Str (ALOOKUP tbl) iv S1 ==>
       s::s'::r IN Str (ALOOKUP tbl) iv S0) /\
   (!tbl S0 t. sos_tr tbl S0 t ==> T)` suffices_by metis_tac[] >>
  ho_match_mp_tac sos_defs_strongind >> rw[clause_name_def] >>
  fs[Str_def, Str0_def]
  >- ((* seq1 *)
      rw[chop_def] >> qexistsl_tac [`[s]`, `s'`, `r`] >> rw[] >>
      metis_tac[c_red_final])
  >- ((* seq2 *)
      fs[chop_def] >>
      Cases_on `l1` >> fs[]
      >- (qexistsl_tac [`[s]`, `s'`, `l2`] >> rw[] >>
          first_x_assum (qspecl_then [`[]`, `iv`] mp_tac) >> rw[])
      >- (qexistsl_tac [`s::s'::t`, `s''`, `l2`] >> rw[] >>
          first_x_assum (qspecl_then [`t ++ [s'']`, `iv`] mp_tac) >> rw[]))
  >- (rw[restrict_def, dup_def])
  >- (rw[restrict_def, dup_def, b_eval_def])
  >- ((* call *)
      `rho0 (ALOOKUP tbl) iv m = H (ALOOKUP tbl) iv (rho0 (ALOOKUP tbl) iv) m`
        by metis_tac[rho0_fixpoint] >>
      rw[H_def, dup_def])
QED

Theorem Ssos_SUBSET_Str:
  !tbl S0 iv. Ssos tbl S0 SUBSET Str (ALOOKUP tbl) iv S0
Proof
  `(!tbl c c'. c_red tbl c c' ==> T) /\
   (!tbl S0 t. sos_tr tbl S0 t ==> !iv. t IN Str (ALOOKUP tbl) iv S0)`
     suffices_by rw[Ssos_def, SUBSET_DEF] >>
  ho_match_mp_tac sos_defs_strongind >> rw[clause_name_def]
  >- metis_tac[c_red_final, Str_def]
  >- metis_tac[c_red_step]
QED

(* ------------------------------------------------------------------------ *)
(* Direction Str <= Ssos                                                     *)
(* ------------------------------------------------------------------------ *)

Theorem sos_tr_nonempty:
  !tbl S0 t. sos_tr tbl S0 t ==> ?s s' r. t = s::s'::r
Proof
  rw[Once sos_defs_cases] >> metis_tac[]
QED

Theorem sos_tr_seq:
  !tbl l1 S1 s S2 l2.
    sos_tr tbl S1 (l1 ++ [s]) /\ sos_tr tbl S2 (s::l2) ==>
    sos_tr tbl (S_seq S1 S2) (l1 ++ [s] ++ l2)
Proof
  Induct_on `l1` >- rw[Once sos_defs_cases] >>
  rpt strip_tac >>
  qpat_x_assum `sos_tr tbl S1 _`
    (strip_assume_tac o REWRITE_RULE [clause_name_def] o
     ONCE_REWRITE_RULE [sos_defs_cases]) >>
  fs[] >> rw[] >>
  TRY (Cases_on `l1` >> fs[] >> rw[]) >>
  FIRST [irule r_step >> metis_tac[r_seq1],
         imp_res_tac sos_tr_nonempty >> fs[] >> NO_TAC,
         metis_tac[r_step, r_seq2, APPEND, APPEND_ASSOC]]
QED

(* the SOS traces of calls form a pre-fixed point of H *)
Definition rho_sos_def:
  rho_sos tbl = \m. Ssos tbl (S_call m)
End

Theorem Str0_rho_sos:
  !S0 tbl iv. var_free S0 ==> Str0 (rho_sos tbl) iv S0 SUBSET Ssos tbl S0
Proof
  Induct >> rw[Str0_def, var_free_def] >> fs[SUBSET_DEF, Ssos_def] >> rw[] >>
  FIRST [fs[rho_sos_def, Ssos_def] >> NO_TAC,
         irule r_end >> metis_tac[r_skip, r_assign],
         fs[chop_def] >> rw[] >> irule sos_tr_seq >> metis_tac[],
         fs[restrict_def, dup_def, b_eval_def] >> rw[] >> irule r_step >>
         metis_tac[r_if1, r_if2]]
QED

Theorem rho_sos_prefix:
  !tbl iv. tbl_var_free tbl ==> ileq (H (ALOOKUP tbl) iv (rho_sos tbl)) (rho_sos tbl)
Proof
  rw[ileq_def, H_def] >> CASE_TAC >> rw[] >>
  `var_free x` by metis_tac[tbl_var_free_def] >>
  `Str0 (rho_sos tbl) iv x SUBSET Ssos tbl x` by metis_tac[Str0_rho_sos] >>
  fs[SUBSET_DEF, dup_def, rho_sos_def, Ssos_def] >> rw[] >>
  irule r_step >> metis_tac[r_call]
QED

Theorem Str_SUBSET_Ssos:
  !tbl S0 iv. tbl_var_free tbl /\ var_free S0 ==>
              Str (ALOOKUP tbl) iv S0 SUBSET Ssos tbl S0
Proof
  rw[Str_def] >>
  `ileq (rho0 (ALOOKUP tbl) iv) (rho_sos tbl)`
    by metis_tac[rho0_least, rho_sos_prefix] >>
  irule SUBSET_TRANS >> qexists_tac `Str0 (rho_sos tbl) iv S0` >>
  rw[Str0_rho_sos] >> irule Str0_mono >> rw[ileq_def]
QED

(* Theorem 3.2 *)
Theorem Str_eq_Ssos:
  !tbl S0 iv. tbl_var_free tbl /\ var_free S0 ==>
              Str (ALOOKUP tbl) iv S0 = Ssos tbl S0
Proof
  metis_tac[SUBSET_ANTISYM, Str_SUBSET_Ssos, Ssos_SUBSET_Str]
QED

