(* Example 5.2 / Figure 6: a derivation of even() : stf(even()) for the
   program of Example 2.2, and its validity via soundness. *)

open HolKernel boolLib Parse bossLib;
open pred_setTheory listTheory alistTheory combinTheory
     ottTheory tracesTheory tracesSemTheory tracesSosTheory tracesSoundTheory;

val _ = new_theory "evenOddExample";

(* ------------------------------------------------------------------------ *)
(* The program of Example 2.2                                               *)
(* ------------------------------------------------------------------------ *)

Overload x_is_0 = ``b_eq (a_var "x") (a_num 0)``
Overload x_minus_1 = ``a_minus (a_var "x") (a_num 1)``

(* even {if x = 0 then y := 1 else x := x - 1; odd()} *)
Overload S_even =
  ``S_ifelse x_is_0 (S_assign "y" (a_num 1))
      (S_seq (S_assign "x" x_minus_1) (S_call "odd"))``

(* odd {if x = 0 then y := 0 else x := x - 1; even()} *)
Overload S_odd =
  ``S_ifelse x_is_0 (S_assign "y" (a_num 0))
      (S_seq (S_assign "x" x_minus_1) (S_call "even"))``

Overload evenodd_tbl = ``[("even", S_even); ("odd", S_odd)]``

(* ------------------------------------------------------------------------ *)
(* The strongest trace formula of Example 4.7                               *)
(* ------------------------------------------------------------------------ *)

(* Chop is associated to the right, as rule (Seq) builds it for
   statements x := x - 1; odd() and skip; S. *)

Overload Id_f = ``f_rel R_Id``

(* mu X_odd. (x = 0 /\ Id ^ Sb_y^0) \/ (x <> 0 /\ Id ^ Sb_x^(x-1) ^ Id ^ X_even) *)
Overload phi_odd_open =
  ``f_mu "Xodd"
      (f_or (f_and (f_state (p_b x_is_0))
                   (f_chop Id_f (f_rel (R_Sb (a_num 0) "y"))))
            (f_and (f_state (p_b (b_neg x_is_0)))
                   (f_chop Id_f (f_chop (f_rel (R_Sb x_minus_1 "x"))
                                        (f_chop Id_f (f_recvar "Xeven"))))))``

(* mu X_even. (x = 0 /\ Id ^ Sb_y^1) \/ (x <> 0 /\ Id ^ Sb_x^(x-1) ^ Id ^ phi_odd_open) *)
Overload phi_even =
  ``f_mu "Xeven"
      (f_or (f_and (f_state (p_b x_is_0))
                   (f_chop Id_f (f_rel (R_Sb (a_num 1) "y"))))
            (f_and (f_state (p_b (b_neg x_is_0)))
                   (f_chop Id_f (f_chop (f_rel (R_Sb x_minus_1 "x"))
                                        (f_chop Id_f phi_odd_open)))))``

(* stf(even()) = Id ^ phi_even *)
Overload stf_even = ``f_chop Id_f phi_even``

(* ------------------------------------------------------------------------ *)
(* The entailment oracle and the entailments used by rule (Cons)            *)
(* ------------------------------------------------------------------------ *)

(* semantic entailment, which is trivially a sound oracle *)
Definition sem_ent_def:
  sem_ent relI f1 f2 = (fsem relI f1 SUBSET fsem relI f2)
End

Theorem sem_ent_sound:
  !relI. ent_sound relI (sem_ent relI)
Proof
  rw[ent_sound_def, sem_ent_def]
QED

Theorem chop_cons:
  !A B t. t IN chop A B ==> ?s r. t = s::r
Proof
  rw[chop_def] >> Cases_on `l1` >> rw[]
QED

(* the two premises of rule (If) when the formula has the shape produced by
   stf for conditionals: (b /\ Id ^ F1) \/ (~b /\ Id ^ F2) *)
Theorem if_then_ent:
  !relI b F1 F2.
    sem_ent relI (f_chop Id_f F1)
      (f_or (f_state (p_b (b_neg b)))
            (f_or (f_and (f_state (p_b b)) (f_chop Id_f F1))
                  (f_and (f_state (p_b (b_neg b))) (f_chop Id_f F2))))
Proof
  rw[sem_ent_def, fsem_eqs, SUBSET_DEF, p_sem_def, b_eval_def] >>
  imp_res_tac chop_cons >> rw[] >> metis_tac[]
QED

Theorem if_else_ent:
  !relI b F1 F2.
    sem_ent relI (f_chop Id_f F2)
      (f_or (f_state (p_b b))
            (f_or (f_and (f_state (p_b b)) (f_chop Id_f F1))
                  (f_and (f_state (p_b (b_neg b))) (f_chop Id_f F2))))
Proof
  rw[sem_ent_def, fsem_eqs, SUBSET_DEF, p_sem_def, b_eval_def] >>
  imp_res_tac chop_cons >> rw[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------ *)
(* The derivation                                                           *)
(* ------------------------------------------------------------------------ *)

val calc_rule = let
  val rules = CONJUNCTS calc_defs_rules |> map (SIMP_RULE std_ss [clause_name_def])
in fn n => List.nth (rules, n) end;

val [skip_rule, assign_rule, seq_rule, if_rule, unfold_rule, cons_rule,
     call_rule, ax_rule] = List.tabulate (8, calc_rule);

(* evaluate lookups, substitutions and side conditions on concrete syntax *)
val eval_tac =
  simp[ALOOKUP_def, G_dom_def, subst_calls_def, subst_f_def, fv_f_def,
       list_minus_def];

(* the derivation of Figure 6, with the contract for odd() chosen as the
   formula that the unfolding of phi_even produces, so that no (Cons) step is
   needed at the call of odd() *)
Theorem even_stf_derivable:
  !relI. calc evenodd_tbl (sem_ent relI) {} (S_call "even") stf_even
Proof
  gen_tac >>
  (* (Call) on even() *)
  irule call_rule >> eval_tac >>
  (* (Unfold) phi_even *)
  irule unfold_rule >> eval_tac >>
  (* (If) on the body of even *)
  irule if_rule >> conj_tac
  >- (irule cons_rule >> irule_at Any if_then_ent >>
      irule seq_rule >> conj_tac >- irule skip_rule >> irule assign_rule)
  >- (irule cons_rule >> irule_at Any if_else_ent >>
      irule seq_rule >> conj_tac >- irule skip_rule >>
      irule seq_rule >> conj_tac >- irule assign_rule >>
      (* (Call) on odd() *)
      irule call_rule >> eval_tac >>
      (* (Unfold) the contract for odd *)
      irule unfold_rule >> eval_tac >>
      (* (If) on the body of odd, where even() is now skip; Y_even *)
      irule if_rule >> conj_tac
      >- (irule cons_rule >> irule_at Any if_then_ent >>
          irule seq_rule >> conj_tac >- irule skip_rule >> irule assign_rule)
      >- (irule cons_rule >> irule_at Any if_else_ent >>
          irule seq_rule >> conj_tac >- irule skip_rule >>
          irule seq_rule >> conj_tac >- irule assign_rule >>
          irule seq_rule >> conj_tac >- irule skip_rule >>
          (* (Ax) for Y_even : phi_even *)
          irule ax_rule >> simp[]))
QED

(* ------------------------------------------------------------------------ *)
(* Validity, via soundness                                                  *)
(* ------------------------------------------------------------------------ *)

Theorem evenodd_tbl_var_free:
  tbl_var_free evenodd_tbl
Proof
  rw[tbl_var_free_def, ALOOKUP_def] >> pop_assum mp_tac >> rw[] >>
  rw[var_free_def]
QED

(* every trace of even() satisfies stf(even()) *)
Theorem even_stf_valid:
  !relI iv. Str (ALOOKUP evenodd_tbl) iv (S_call "even") SUBSET fsem relI stf_even
Proof
  metis_tac[calc_sound_empty, sem_ent_sound, evenodd_tbl_var_free,
            even_stf_derivable]
QED

(* ... and so does every trace induced by the SOS *)
Theorem even_stf_valid_sos:
  !relI. Ssos evenodd_tbl (S_call "even") SUBSET fsem relI stf_even
Proof
  rw[] >> irule calc_sound_sos >>
  rw[var_free_def, evenodd_tbl_var_free] >>
  metis_tac[sem_ent_sound, even_stf_derivable]
QED

val _ = export_theory ();
