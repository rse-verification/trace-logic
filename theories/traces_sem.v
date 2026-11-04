From stdpp Require Import prelude strings gmap stringmap functions countable sets propset relations.
From RecTraces Require Import traces_defs.

Section Util.

Context {A : Type}.

Definition big_union (P : propset (propset A)) : propset A :=
{[ x | exists s, s ∈ P /\ x ∈ s ]}.

Definition big_inter (P : propset (propset A)) : propset A :=
{[ x | forall s, s ∈ P -> x ∈ s ]}.

End Util.

Section Sem.

Variable T : list M.

Variable b_eval : b -> s -> option v.
Variable a_eval : a -> s -> option n.

Inductive c_red_tr : S -> list s -> Prop :=
| c_red_tr_end : forall s1 s2 S1,
   c_red T b_eval a_eval (c_tuple S1 s1) (c_state s2) ->
   c_red_tr S1 (s1 :: s2 :: [])
| c_red_tr_step : forall s1 s2 S1 S2 sl,
   c_red T b_eval a_eval (c_tuple S1 s1) (c_tuple S2 s2) ->
   c_red_tr S2 (s2 :: sl) ->
   c_red_tr S1 (s1 :: s2 :: sl).

Definition c_red_sem (S0 : S) : propset (list s) :=
{[ sl | c_red_tr S0 sl ]}.

Definition State_b (A : propset (list s)) (b0 : b) : propset (list s) :=
{[ sl | sl ∈ A /\ exists s0, head sl = Some s0 /\ b_eval b0 s0 = Some true ]}.

Definition State_dup (A : propset (list s)) : propset (list s) :=
{[ sl | exists s0 sl0, sl = s0 :: s0 :: sl0 /\ s0 :: sl0 ∈ A ]}.

Definition State_chop (A B : propset (list s)) : propset (list s) :=
{[ sl | exists sa sb s0, sl = sa ++ s0 :: sb /\ sa ++ [s0] ∈ A /\ s0 :: sb ∈ B ]}.

Fixpoint S_0_tr (rho : m -> propset (list s)) (S0 : S) (I : Y -> propset (list s)) : propset (list s) :=
match S0 with
| S_skip =>
    {[ sl | exists s0, sl = s0 :: s0 :: [] ]}
| S_assign x0 a0 =>
    {[ sl | exists s0 n0, a_eval a0 s0 = Some n0 /\ sl = s0 :: <[ x0 := n0 ]> s0 :: [] ]}
| S_seq S1 S2 =>
    State_chop (S_0_tr rho S1 I) (S_0_tr rho S2 I)
| S_ifelse b0 S1 S2 =>
    State_b (State_dup (S_0_tr rho S1 I)) b0 ∪
    State_b (State_dup (S_0_tr rho S2 I)) (b_neg b0)
| S_call m0 =>
    rho m0
| S_var Y0 =>
    I Y0
end.

Definition R_sem (Q_sem : Q -> (s -> s -> Prop)) (R0 : R) : s -> s -> Prop :=
match R0 with
| R_Id => fun s1 s2 => s2 = s1
| R_Sb a0 x0 => fun s1 s2 =>
  match a_eval a0 s1 with
  | Some n0 => s2 = (<[ x0 := n0 ]> s1)
  | None => False
  end
| R_other Q0 => Q_sem Q0
end.

Definition R_tc (R0 : R) : f :=
f_mu "X" (f_or (f_rel R0) (f_chop (f_rel R0) (f_recvar "X"))).

Fixpoint f_sem (Q_sem : Q -> (s -> s -> Prop)) (p_sem : s -> p -> Prop)
 (f0 : f) (V : X -> propset (list s)) : propset (list s) :=
match f0 with
| f_state p0 =>
    {[ sl | exists s0, head sl = Some s0 /\ p_sem s0 p0 ]}
| f_recvar X0 =>
    V X0
| f_rel R0 =>
    {[ sl | exists s0 s1, sl = s0 :: s1 :: [] /\ R_sem Q_sem R0 s0 s1 ]}
| f_and f1 f2 =>
    f_sem Q_sem p_sem f1 V ∩ f_sem Q_sem p_sem f2 V
| f_or f1 f2 =>
    f_sem Q_sem p_sem f1 V ∪ f_sem Q_sem p_sem f2 V
| f_chop f1 f2 =>
    State_chop (f_sem Q_sem p_sem f1 V) (f_sem Q_sem p_sem f2 V)
| f_mu X0 f1 =>
    big_inter {[ g | g ≢ ∅ /\ f_sem Q_sem p_sem f1 (<[ X0 := g ]> V) ⊆ g ]}
end.

End Sem.

Section Meta.

Variable T : list M.

Variable b_eval : b -> s -> option v.
Variable a_eval : a -> s -> option n.

Variable rho : m -> propset (list s).

Variable Q_sem : Q -> (s -> s -> Prop).

Variable p_sem : s -> p -> Prop.

Lemma R_sem_R_tc : forall (R0 : R) V,
 f_sem a_eval Q_sem p_sem (R_tc R0) V ≡
 {[ sl | exists s0 s1, sl = s0 :: s1 :: [] /\ tc (R_sem a_eval Q_sem R0) s0 s1 ]}.
Proof.
intros R0 V; split.
- cbn.
  unfold big_inter.
  intros HX.
  by admit.
- cbn.
  by admit.
Admitted.

Lemma S_tr_subset_c_red_sem : forall S0 I,
 c_red_sem T b_eval a_eval S0 ⊆ S_0_tr b_eval a_eval rho S0 I.
Proof.
Admitted.

Lemma c_red_sem_subset_S_tr : forall S0 I,
 S_0_tr b_eval a_eval rho S0 I ⊆ c_red_sem T b_eval a_eval S0.
Proof.
Admitted.

Lemma S_tr_eq_c_red_sem : forall S0 I,
 c_red_sem T b_eval a_eval S0 ≡ S_0_tr b_eval a_eval rho S0 I.
Proof.
intros S0 x; split.
- by apply S_tr_subset_c_red_sem.
- by apply c_red_sem_subset_S_tr.
Qed.

End Meta.
