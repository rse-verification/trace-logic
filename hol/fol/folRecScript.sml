(* The two-sorted first-order logic of thesis Section 4.1 (Definitions 4.1
   and 4.2), encoded in the one-sorted string FOL of folString. The domain
   is int + state: integers are the sort Z, states (total functions from
   variable names to integers) the sort State. The sort predicates "Int"
   and "State" relativize quantifiers. The structure is parametric in the
   set D of states that the sort State denotes: D = UNIV gives Definition
   4.2 with all states; restricting D to the states over the program
   variables gives the thesis's D_State (see vcXs). The domain consists of
   the integers and the states in D. Function symbols applied to arguments
   of the wrong sorts give 0, and predicate symbols false. *)

Theory folRec
Ancestors
  arithmetic integer list rich_list string ASCIInumbers combin traces
  tracesSem folString
Libs
  intLib

Type rdom = ``:int + state``

(* ------------------------------------------------------------------------ *)
(* The structure M of Definition 4.2                                        *)
(* ------------------------------------------------------------------------ *)

(* Function symbols:
   - the decimal numeral n (no arguments): the integer n;
   - "neg" (Z): unary minus;
   - "+", "-", "*" (Z, Z): arithmetic;
   - "sel_x" (State): the value of program variable x in the state, written
     s(x) in the thesis. *)
Definition rec_fun_def:
  rec_fun (f:string) (l:rdom list) : rdom =
    case l of
      [] => INL (& (@n. f = toString n))
    | [INL i] => if f = "neg" then INL (-i) else INL 0
    | [INR s] => if isPREFIX "sel_" f then INL (s (DROP 4 f)) else INL 0
    | [INL i; INL j] =>
        if f = "+" then INL (i + j)
        else if f = "-" then INL (i - j)
        else if f = "*" then INL (i * j)
        else INL 0
    | _ => INL 0
End

(* Predicate symbols:
   - "Int", "State" (one argument): the sorts, where State denotes the
     states in D;
   - "=" (two arguments of the same sort): equality;
   - "<=" (Z, Z): the order on integers;
   - "Id" (State, State): Id of Definition 4.1;
   - "Sb_x" (Z, State, State): Sb^a_x of Definition 4.1, where the first
     argument is the value of a. The truth values tt and ff are STrue and
     SFalse. *)
Definition rec_pred_def:
  rec_pred (D:state set) (p:string) (l:rdom list) =
    case l of
      [d] => (p = "Int" /\ ISL d) \/ (p = "State" /\ ISR d /\ OUTR d IN D)
    | [INL i; INL j] => (p = "=" /\ i = j) \/ (p = "<=" /\ i <= j)
    | [INR s; INR s'] => (p = "=" \/ p = "Id") /\ s' = s
    | [INL v; INR s; INR s'] =>
        isPREFIX "Sb_" p /\ s' = (DROP 3 p =+ v) s
    | _ => F
End

Definition rec_model_def:
  rec_model D =
    <| SDom := {d | ISL d \/ OUTR d IN D}; SFun := rec_fun;
       SPred := rec_pred D |>
End

(* ------------------------------------------------------------------------ *)
(* Notation                                                                 *)
(* ------------------------------------------------------------------------ *)

(* the integer constant i *)
Definition int_const_def:
  int_const (i:int) =
    if 0 <= i then SFn (toString (Num i)) []
    else SFn "neg" [SFn (toString (Num (-i))) []]
End

(* the state variable s(i) *)
Definition svar_def:
  svar (i:num) = SV ("s" ++ toString i)
End

(* A[[a]](st) as a term of sort Z *)
Definition a2sterm_def:
  (a2sterm st (a_num n) = int_const n) /\
  (a2sterm st (a_var x) = SFn ("sel_" ++ x) [st]) /\
  (a2sterm st (a_uminus a) = SFn "neg" [a2sterm st a]) /\
  (a2sterm st (a_plus a1 a2) = SFn "+" [a2sterm st a1; a2sterm st a2]) /\
  (a2sterm st (a_minus a1 a2) = SFn "-" [a2sterm st a1; a2sterm st a2]) /\
  (a2sterm st (a_times a1 a2) = SFn "*" [a2sterm st a1; a2sterm st a2])
End

(* B[[b]](st) as a formula *)
Definition b2sform_def:
  (b2sform st b_true = STrue) /\
  (b2sform st b_false = SFalse) /\
  (b2sform st (b_eq a1 a2) = SPred "=" [a2sterm st a1; a2sterm st a2]) /\
  (b2sform st (b_leq a1 a2) = SPred "<=" [a2sterm st a1; a2sterm st a2]) /\
  (b2sform st (b_neg b) = SNot (b2sform st b)) /\
  (b2sform st (b_and b1 b2) = SAnd (b2sform st b1) (b2sform st b2))
End

(* Id(st, st') and Sb^a_x(st, st') of Definition 4.1 *)
Definition Id_sform_def:
  Id_sform st st' = SPred "Id" [st; st']
End

Definition Sb_sform_def:
  Sb_sform x a st st' = SPred ("Sb_" ++ x) [a2sterm st a; st; st']
End

(* quantification over states *)
Definition sforall_state_def:
  sforall_state x f = SForall x (SImp (SPred "State" [SV x]) f)
End

(* ------------------------------------------------------------------------ *)
(* Semantics of the notation                                                *)
(* ------------------------------------------------------------------------ *)

Theorem rec_model_fields[simp]:
  (rec_model D).SDom = {d | ISL d \/ OUTR d IN D} /\
  (rec_model D).SFun = rec_fun /\
  (rec_model D).SPred = rec_pred D
Proof
  rw[rec_model_def]
QED

Theorem stermval_int_const:
  !D v i. stermval (rec_model D) v (int_const i) = INL i
Proof
  rw[int_const_def, stermval_def, rec_fun_def, toString_inj]
  >> intLib.ARITH_TAC
QED

Theorem stermval_a2sterm:
  !D a v st s.
    stermval (rec_model D) v st = INR s ==>
    stermval (rec_model D) v (a2sterm st a) = INL (a_eval a s)
Proof
  gen_tac >> Induct >>
  rw[a2sterm_def, stermval_def, stermval_int_const, a_eval_def] >>
  res_tac >> rw[rec_fun_def, isPREFIX_STRCAT, DROP_APPEND]
QED

Theorem sholds_b2sform:
  !D b v st s.
    stermval (rec_model D) v st = INR s ==>
    (sholds (rec_model D) v (b2sform st b) <=> b_eval b s)
Proof
  gen_tac >> Induct >>
  rw[b2sform_def, sholds_def, b_eval_def] >>
  imp_res_tac stermval_a2sterm >> res_tac >> rw[rec_pred_def]
QED

Theorem sholds_Id_sform:
  !D v st st' s s'.
    stermval (rec_model D) v st = INR s /\ stermval (rec_model D) v st' = INR s' ==>
    (sholds (rec_model D) v (Id_sform st st') <=> s' = s)
Proof
  rw[Id_sform_def, sholds_def, rec_pred_def]
QED

Theorem sholds_Sb_sform:
  !D v x a st st' s s'.
    stermval (rec_model D) v st = INR s /\ stermval (rec_model D) v st' = INR s' ==>
    (sholds (rec_model D) v (Sb_sform x a st st') <=>
     s' = (x =+ a_eval a s) s)
Proof
  rw[Sb_sform_def, sholds_def] >> imp_res_tac stermval_a2sterm >>
  rw[rec_pred_def, isPREFIX_STRCAT, DROP_APPEND]
QED

Theorem sholds_sforall_state:
  !D v x f.
    sholds (rec_model D) v (sforall_state x f) <=>
    !s. s IN D ==> sholds (rec_model D) ((x =+ INR s) v) f
Proof
  rw[sforall_state_def, sholds_def, rec_pred_def,
     stermval_def, APPLY_UPDATE_THM] >>
  EQ_TAC >> rw[] >> Cases_on `a` >> fs[] >>
  first_x_assum irule >> rw[]
QED
