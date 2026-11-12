(* Statements in normal form: sequences associated to the right, with
   only atomic statements as left operands (thesis Lemma 4.11 and
   Definition 4.33, corrected). *)

Theory verifNorm
Ancestors
  pred_set list combin traces tracesSem verifChop verifEff

Definition atomic_def:
  (atomic S_skip = T) /\
  (atomic (S_assign x a) = T) /\
  (atomic (S_call m) = T) /\
  (atomic (S_var Y) = T) /\
  (atomic (S_seq S1 S2) = F) /\
  (atomic (S_ifelse b S1 S2) = F)
End

(* the left operand of every sequence is atomic *)
Definition nf_def:
  (nf (S_seq S1 S2) = (atomic S1 /\ nf S2)) /\
  (nf (S_ifelse b S1 S2) = (nf S1 /\ nf S2)) /\
  (nf _ = T)
End

(* the thesis's shape condition: no conditional is a left operand of a
   sequence (Lemma 4.11 and the text after it) *)
Definition no_if_left_def:
  (no_if_left (S_seq S1 S2) =
     ((!b S3 S4. S1 <> S_ifelse b S3 S4) /\ no_if_left S1 /\ no_if_left S2)) /\
  (no_if_left (S_ifelse b S1 S2) = (no_if_left S1 /\ no_if_left S2)) /\
  (no_if_left _ = T)
End

(* sequential composition of statements in normal form *)
Definition seqn_def:
  (seqn (S_seq S1 S2) S3 = S_seq S1 (seqn S2 S3)) /\
  (seqn (S_ifelse b S1 S2) S3 = S_ifelse b (seqn S1 S3) (seqn S2 S3)) /\
  (seqn S1 S3 = S_seq S1 S3)
End

Definition norm_def:
  (norm (S_seq S1 S2) = seqn (norm S1) (norm S2)) /\
  (norm (S_ifelse b S1 S2) = S_ifelse b (norm S1) (norm S2)) /\
  (norm S0 = S0)
End

Theorem Str0_seqn:
  !S1 S3 rho iv.
    Str0 rho iv (seqn S1 S3) = chop (Str0 rho iv S1) (Str0 rho iv S3)
Proof
  recInduct seqn_ind >>
  rw[seqn_def, Str0_def, chop_assoc, chop_union_l, chop_restrict_l,
     chop_dup_l]
QED

(* Lemma 4.11, generalized to normalization *)
Theorem Str0_norm:
  !S0 rho iv. Str0 rho iv (norm S0) = Str0 rho iv S0
Proof
  Induct >> rw[norm_def, Str0_def, Str0_seqn]
QED

Theorem nf_seqn:
  !S1 S3. nf S1 /\ nf S3 ==> nf (seqn S1 S3)
Proof
  recInduct seqn_ind >> rw[seqn_def, nf_def, atomic_def]
QED

Theorem nf_norm:
  !S0. nf (norm S0)
Proof
  Induct >> rw[norm_def, nf_def, nf_seqn, atomic_def]
QED

(* normalizing the bodies of a procedure table *)
Definition norm_lk_def:
  norm_lk (lk:lookup) = \m. OPTION_MAP norm (lk m)
End

Theorem norm_lk_nf:
  !lk m body. norm_lk lk m = SOME body ==> nf body
Proof
  rw[norm_lk_def] >> rw[nf_norm]
QED

Theorem rho0_norm_lk:
  !lk iv. rho0 (norm_lk lk) iv = rho0 lk iv
Proof
  rw[rho0_def] >> AP_TERM_TAC >>
  CONV_TAC FUN_EQ_CONV >> qx_gen_tac `rho` >>
  CONV_TAC FUN_EQ_CONV >> qx_gen_tac `m` >>
  rw[H_def, norm_lk_def] >> Cases_on `lk m` >> rw[Str0_norm]
QED

Theorem Str_norm:
  !lk iv S0. Str (norm_lk lk) iv (norm S0) = Str lk iv S0
Proof
  rw[Str_def, rho0_norm_lk, Str0_norm]
QED

Theorem Str_norm_lk:
  !lk iv S0. Str (norm_lk lk) iv S0 = Str lk iv S0
Proof
  rw[Str_def, rho0_norm_lk]
QED

Theorem conforms_norm_lk:
  !lk pre post. conforms (norm_lk lk) pre post <=> conforms lk pre post
Proof
  rw[conforms_def, Str_norm_lk]
QED
