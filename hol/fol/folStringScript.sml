(* First-order logic with string names for variables, functions and
   predicates, and the derived connectives as constructors. Its semantics
   agrees with folcompactness (folLang, folModels), where names are
   numbers and only False, Pred, IMP and FALL are primitive. *)

Theory folString
Ancestors
  combin list string string_num folLang folModels

Datatype:
  sterm = SV string | SFn string (sterm list)
End

Datatype:
  sform = SFalse
        | STrue
        | SPred string (sterm list)
        | SNot sform
        | SAnd sform sform
        | SOr sform sform
        | SImp sform sform
        | SIff sform sform
        | SForall string sform
        | SExists string sform
End

Datatype:
  smodel = <| SDom : 'a set ; SFun : string -> 'a list -> 'a ;
              SPred : string -> 'a list -> bool |>
End

val sterm_size_def = fetch "-" "sterm_size_def";

Theorem sterm_size_lemma[simp]:
  !x l a. MEM a l ==> sterm_size a < 1 + (x + sterm1_size l)
Proof
  rpt gen_tac >> Induct_on `l` >> rw[sterm_size_def] >> res_tac >> rw[]
QED

Theorem sterm_induct:
  !P. (!v. P (SV v)) /\ (!f ts. (!t. MEM t ts ==> P t) ==> P (SFn f ts)) ==>
      !t. P t
Proof
  rpt strip_tac >>
  qspecl_then [`P`, `\ts. !t. MEM t ts ==> P t`]
    (assume_tac o SIMP_RULE bool_ss []) (TypeBase.induction_of ``:sterm``) >>
  rfs[] >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Definition stermval_def:
  (stermval M v (SV x) = v x) /\
  (stermval M v (SFn f l) = M.SFun f (MAP (stermval M v) l))
Termination
  WF_REL_TAC `measure (sterm_size o SND o SND)` >> rw[]
End

Definition sholds_def:
  (sholds M v SFalse <=> F) /\
  (sholds M v STrue <=> T) /\
  (sholds M v (SPred p l) <=> M.SPred p (MAP (stermval M v) l)) /\
  (sholds M v (SNot f) <=> ~sholds M v f) /\
  (sholds M v (SAnd f1 f2) <=> sholds M v f1 /\ sholds M v f2) /\
  (sholds M v (SOr f1 f2) <=> sholds M v f1 \/ sholds M v f2) /\
  (sholds M v (SImp f1 f2) <=> (sholds M v f1 ==> sholds M v f2)) /\
  (sholds M v (SIff f1 f2) <=> (sholds M v f1 <=> sholds M v f2)) /\
  (sholds M v (SForall x f) <=> !a. a IN M.SDom ==> sholds M ((x =+ a) v) f) /\
  (sholds M v (SExists x f) <=> ?a. a IN M.SDom /\ sholds M ((x =+ a) v) f)
End

(* ------------------------------------------------------------------------ *)
(* Translation to folcompactness                                            *)
(* ------------------------------------------------------------------------ *)

Definition sterm2term_def:
  (sterm2term (SV x) = V (s2n x)) /\
  (sterm2term (SFn f l) = Fn (s2n f) (MAP sterm2term l))
Termination
  WF_REL_TAC `measure sterm_size` >> rw[]
End

Definition sform2form_def:
  (sform2form SFalse = False) /\
  (sform2form STrue = True) /\
  (sform2form (SPred p l) = Pred (s2n p) (MAP sterm2term l)) /\
  (sform2form (SNot f) = Not (sform2form f)) /\
  (sform2form (SAnd f1 f2) = And (sform2form f1) (sform2form f2)) /\
  (sform2form (SOr f1 f2) = Or (sform2form f1) (sform2form f2)) /\
  (sform2form (SImp f1 f2) = IMP (sform2form f1) (sform2form f2)) /\
  (sform2form (SIff f1 f2) = Iff (sform2form f1) (sform2form f2)) /\
  (sform2form (SForall x f) = FALL (s2n x) (sform2form f)) /\
  (sform2form (SExists x f) = Exists (s2n x) (sform2form f))
End

Definition smodel2model_def:
  smodel2model M =
    <| Dom := M.SDom ; Fun := M.SFun o n2s ; Pred := M.SPred o n2s |>
End

Theorem update_n2s[local]:
  !x a v. ((x =+ a) v) o n2s = ((s2n x =+ a) (v o n2s))
Proof
  rw[FUN_EQ_THM, APPLY_UPDATE_THM] >> metis_tac[s2n_n2s, n2s_s2n]
QED

Theorem stermval_termval:
  !M v t. stermval M v t = termval (smodel2model M) (v o n2s) (sterm2term t)
Proof
  ntac 2 gen_tac >> ho_match_mp_tac sterm_induct >>
  rw[stermval_def, sterm2term_def, smodel2model_def, MAP_MAP_o] >>
  AP_TERM_TAC >> irule MAP_CONG >> rw[]
QED

(* the semantics agree *)
Theorem sholds_holds:
  !f M v. sholds M v f <=> holds (smodel2model M) (v o n2s) (sform2form f)
Proof
  Induct >>
  rw[sholds_def, sform2form_def, smodel2model_def, MAP_MAP_o,
     update_n2s] >>
  TRY (AP_TERM_TAC >> irule MAP_CONG >> rw[stermval_termval] >>
       rw[smodel2model_def] >> NO_TAC) >>
  metis_tac[]
QED

(* hence so do validity in a model and truth in it under all valuations *)
Theorem sholds_satisfies:
  !M f. (!v. sholds M v f) ==> smodel2model M satisfies {sform2form f}
Proof
  rw[satisfies_def, sholds_holds] >>
  first_x_assum (qspec_then `v o s2n` mp_tac) >>
  `v o s2n o n2s = v` by rw[FUN_EQ_THM, n2s_s2n] >>
  rw[]
QED
