(* Example 5.2 / Figure 6: a derivation of even() : stf(even()) for the
   program of Example 2.2, and its validity via soundness. *)

Theory evenOddExample
Ancestors
  pred_set list alist combin ott traces tracesSem tracesSos tracesSound
  tracesStf

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

Theorem evenodd_tbl_var_free:
  tbl_var_free evenodd_tbl
Proof
  rw[tbl_var_free_def, ALOOKUP_def] >> pop_assum mp_tac >> rw[] >>
  rw[var_free_def]
QED

(* ------------------------------------------------------------------------ *)
(* The strongest trace formula of Example 4.7                               *)
(* ------------------------------------------------------------------------ *)

(* The recursion variables X_even and X_odd are named even and odd. Chop is
   associated to the right, as Definition 4.6 builds it for
   x := x - 1; odd(). *)

Overload Id_f = ``f_rel R_Id``

(* mu X_odd. (x = 0 /\ Id ^ Sb_y^0) \/ (x <> 0 /\ Id ^ Sb_x^(x-1) ^ Id ^ X_even) *)
Overload phi_odd_open =
  ``f_mu "odd"
      (f_or (f_and (f_state (p_b x_is_0))
                   (f_chop Id_f (f_rel (R_Sb (a_num 0) "y"))))
            (f_and (f_state (p_b (b_neg x_is_0)))
                   (f_chop Id_f (f_chop (f_rel (R_Sb x_minus_1 "x"))
                                        (f_chop Id_f (f_recvar "even"))))))``

(* mu X_even. (x = 0 /\ Id ^ Sb_y^1) \/ (x <> 0 /\ Id ^ Sb_x^(x-1) ^ Id ^ phi_odd_open) *)
Overload phi_even =
  ``f_mu "even"
      (f_or (f_and (f_state (p_b x_is_0))
                   (f_chop Id_f (f_rel (R_Sb (a_num 1) "y"))))
            (f_and (f_state (p_b (b_neg x_is_0)))
                   (f_chop Id_f (f_chop (f_rel (R_Sb x_minus_1 "x"))
                                        (f_chop Id_f phi_odd_open)))))``

(* Example 4.7: stf(even()) = Id ^ phi_even *)
Theorem example_4_7:
  stf evenodd_tbl [] (S_call "even") = f_chop Id_f phi_even
Proof
  EVAL_TAC
QED

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

(* The (Cons) step at odd() in Figure 6: stf(odd()) entails the formula
   for odd() that unfolding phi_even produces. Both denote Str[[odd()]]. *)
Theorem odd_call_ent:
  !relI.
    sem_ent relI (stf evenodd_tbl [] (S_call "odd"))
      (subst_f (f_mu "even" (stf evenodd_tbl ["even"] S_even)) "even"
         (stf evenodd_tbl ["even"] (S_call "odd")))
Proof
  rw[sem_ent_def] >>
  `fsem relI (stf evenodd_tbl [] (S_call "odd")) =
   Str (ALOOKUP evenodd_tbl) (K {}) (S_call "odd")`
    by (irule stf_Str >> rw[var_free_def, evenodd_tbl_var_free]) >>
  `fsem relI (subst_f (f_mu "even" (stf evenodd_tbl ["even"] S_even)) "even"
                (stf evenodd_tbl ["even"] (S_call "odd"))) =
   Str (ALOOKUP evenodd_tbl) (K {}) (S_call "odd")`
    by (irule stf_unfold_Str >>
        rw[var_free_def, evenodd_tbl_var_free] >> EVAL_TAC) >>
  rw[]
QED

(* The (Cons) step at Y_even in Figure 6: phi_even entails the formula for
   Y_even that unfolding phi_odd produces. Both denote Str[[S_even]]. *)
Theorem even_var_ent:
  !relI.
    sem_ent relI (f_mu "even" (stf evenodd_tbl ["even"] S_even))
      (subst_f (f_mu "odd" (stf evenodd_tbl ["odd"] S_odd)) "odd"
         (f_mu "even" (stf evenodd_tbl ["even"; "odd"] S_even)))
Proof
  rw[sem_ent_def] >>
  `fsem relI (subst_f (f_mu "odd" (stf evenodd_tbl ["odd"] S_odd)) "odd"
                (f_mu "even" (stf evenodd_tbl ["even"; "odd"] S_even))) =
   fsem relI (f_mu "even" (stf evenodd_tbl ["even"] S_even))`
    by (irule stf_unfold_mu >> rw[evenodd_tbl_var_free] >> EVAL_TAC) >>
  rw[]
QED

(* ------------------------------------------------------------------------ *)
(* The derivation of Figure 6                                               *)
(* ------------------------------------------------------------------------ *)

val calc_rule = let
  val rules = CONJUNCTS calc_defs_rules |> map (SIMP_RULE std_ss [clause_name_def])
in fn n => List.nth (rules, n) end;

val [skip_rule, assign_rule, seq_rule, if_rule, unfold_rule, cons_rule,
     call_rule, ax_rule] = List.tabulate (8, calc_rule);

(* evaluate stf, lookups, substitutions and side conditions on concrete
   syntax *)
val eval_tac =
  simp[stf_def, ALOOKUP_def, G_dom_def, subst_calls_def, subst_f_def, fv_f_def,
       list_minus_def];

(* the premises of (If) for x = 0: skip; y := n *)
val if_then_tac =
  irule cons_rule >> irule_at Any if_then_ent >>
  irule seq_rule >> conj_tac >- irule skip_rule >> irule assign_rule;

Theorem even_stf_derivable:
  !relI. calc evenodd_tbl (sem_ent relI) {} (S_call "even")
           (stf evenodd_tbl [] (S_call "even"))
Proof
  gen_tac >> eval_tac >>
  (* (Call) on even() *)
  irule call_rule >> eval_tac >>
  (* (Unfold) phi_even *)
  irule unfold_rule >> eval_tac >>
  (* (If) on the body of even *)
  irule if_rule >> conj_tac >- if_then_tac >>
  irule cons_rule >> irule_at Any if_else_ent >>
  irule seq_rule >> conj_tac >- irule skip_rule >>
  irule seq_rule >> conj_tac >- irule assign_rule >>
  (* (Cons) from stf(odd()) *)
  irule cons_rule >> qexists_tac `stf evenodd_tbl [] (S_call "odd")` >>
  conj_tac >- (mp_tac (Q.SPEC `relI` odd_call_ent) >> eval_tac) >>
  eval_tac >>
  (* (Call) on odd() *)
  irule call_rule >> eval_tac >>
  (* (Unfold) phi_odd *)
  irule unfold_rule >> eval_tac >>
  (* (If) on the body of odd, where even() is now skip; Y_even *)
  irule if_rule >> conj_tac >- if_then_tac >>
  irule cons_rule >> irule_at Any if_else_ent >>
  irule seq_rule >> conj_tac >- irule skip_rule >>
  irule seq_rule >> conj_tac >- irule assign_rule >>
  irule seq_rule >> conj_tac >- irule skip_rule >>
  (* (Cons) from Y_even : phi_even *)
  irule cons_rule >>
  qexists_tac `f_mu "even" (stf evenodd_tbl ["even"] S_even)` >>
  conj_tac >- (mp_tac (Q.SPEC `relI` even_var_ent) >> eval_tac) >>
  eval_tac >>
  (* (Ax) for Y_even : phi_even *)
  irule ax_rule >> simp[]
QED

(* Remark: a shorter derivation. If (Call) on odd() uses as its contract
   the formula that unfolding phi_even produces, instead of stf(odd()), then
   neither of the two (Cons) steps above is needed; the hypothesis for
   Y_even then matches the formula for Y_even directly. *)
Theorem even_stf_derivable_short:
  !relI. calc evenodd_tbl (sem_ent relI) {} (S_call "even")
           (stf evenodd_tbl [] (S_call "even"))
Proof
  gen_tac >> eval_tac >>
  irule call_rule >> eval_tac >>
  irule unfold_rule >> eval_tac >>
  irule if_rule >> conj_tac >- if_then_tac >>
  irule cons_rule >> irule_at Any if_else_ent >>
  irule seq_rule >> conj_tac >- irule skip_rule >>
  irule seq_rule >> conj_tac >- irule assign_rule >>
  (* (Call) on odd(), with the unfolded formula as contract *)
  irule call_rule >> eval_tac >>
  irule unfold_rule >> eval_tac >>
  irule if_rule >> conj_tac >- if_then_tac >>
  irule cons_rule >> irule_at Any if_else_ent >>
  irule seq_rule >> conj_tac >- irule skip_rule >>
  irule seq_rule >> conj_tac >- irule assign_rule >>
  irule seq_rule >> conj_tac >- irule skip_rule >>
  irule ax_rule >> simp[]
QED

(* ------------------------------------------------------------------------ *)
(* Validity, via soundness                                                  *)
(* ------------------------------------------------------------------------ *)

(* every trace of even() satisfies stf(even()) *)
Theorem even_stf_valid:
  !relI iv. Str (ALOOKUP evenodd_tbl) iv (S_call "even") SUBSET
            fsem relI (stf evenodd_tbl [] (S_call "even"))
Proof
  metis_tac[calc_sound_empty, sem_ent_sound, evenodd_tbl_var_free,
            even_stf_derivable]
QED

(* ... and so does every trace induced by the SOS *)
Theorem even_stf_valid_sos:
  !relI. Ssos evenodd_tbl (S_call "even") SUBSET
         fsem relI (stf evenodd_tbl [] (S_call "even"))
Proof
  rw[] >> irule calc_sound_sos >>
  rw[var_free_def, evenodd_tbl_var_free] >>
  metis_tac[sem_ent_sound, even_stf_derivable]
QED

