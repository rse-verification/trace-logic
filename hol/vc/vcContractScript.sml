(* Syntax of procedure contracts (thesis Definitions 4.5 and 4.6). A
   precondition is a Boolean expression over the initial state. A
   postcondition is a Boolean expression over two states: ta_var x is the
   value of x in the final state, ta_old x its value in the initial state
   (written x0 in the thesis, e.g. Post_m = (x = 0 /\ y = y0)). *)

Theory vcContract
Ancestors
  combin traces tracesSem verifEff

(* arithmetic expressions over two states *)
Datatype:
  ta = ta_num int
     | ta_var string
     | ta_old string
     | ta_uminus ta
     | ta_plus ta ta
     | ta_minus ta ta
     | ta_times ta ta
End

(* Boolean expressions over two states *)
Datatype:
  tb = tb_true
     | tb_false
     | tb_eq ta ta
     | tb_leq ta ta
     | tb_neg tb
     | tb_and tb tb
End

(* evaluation in the initial state s0 and the final state s *)
Definition ta_eval_def:
  (ta_eval (ta_num n) (s0:state) (s:state) = n) /\
  (ta_eval (ta_var x) s0 s = s x) /\
  (ta_eval (ta_old x) s0 s = s0 x) /\
  (ta_eval (ta_uminus a) s0 s = - ta_eval a s0 s) /\
  (ta_eval (ta_plus a1 a2) s0 s = ta_eval a1 s0 s + ta_eval a2 s0 s) /\
  (ta_eval (ta_minus a1 a2) s0 s = ta_eval a1 s0 s - ta_eval a2 s0 s) /\
  (ta_eval (ta_times a1 a2) s0 s = ta_eval a1 s0 s * ta_eval a2 s0 s)
End

Definition tb_eval_def:
  (tb_eval tb_true (s0:state) (s:state) = T) /\
  (tb_eval tb_false s0 s = F) /\
  (tb_eval (tb_eq a1 a2) s0 s = (ta_eval a1 s0 s = ta_eval a2 s0 s)) /\
  (tb_eval (tb_leq a1 a2) s0 s = (ta_eval a1 s0 s <= ta_eval a2 s0 s)) /\
  (tb_eval (tb_neg b) s0 s = ~tb_eval b s0 s) /\
  (tb_eval (tb_and b1 b2) s0 s = (tb_eval b1 s0 s /\ tb_eval b2 s0 s))
End

(* A contract table assigns a contract <Pre_m, Post_m> to procedure names.
   A procedure without a contract has the trivial contract <true, true>. *)
Type ctable = ``:string -> (b # tb) option``

Definition cpre_def:
  cpre (ct:ctable) m s =
    case ct m of SOME (p, q) => b_eval p s | NONE => T
End

Definition cpost_def:
  cpost (ct:ctable) m s0 s =
    case ct m of SOME (p, q) => tb_eval q s0 s | NONE => T
End
