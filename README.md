# Trace logic for recursive programs in HOL4

This repository formalizes in HOL4 core parts of the paper [An Expressive
Trace Logic for Recursive Programs](https://doi.org/10.48550/arXiv.2411.13125)
by D. Gurov and R. Hähnle. This includes the Rec programming language,
a trace logic for specifying Rec programs, and corresponding semantics.
The formalization goes up to the soundness of the proof calculus (Theorem 5.6),
together with the characterisation of strongest trace formulas (Theorem 4.9)
and the example derivation of Figure 6 (see `doc/note.tex` and the table
under [Note to HOL4](#note-to-hol4)).

On top of this formalization, reusing its language, trace logic, and semantics,
the repository also formalizes Chapter 4 of the master's thesis of
F. Stevanovic, [Automated Verification of Finite-trace Properties for
Recursive Programs](https://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Akth%3Adiva-368044)
(KTH, 2025), which verifies Rec programs against trace
formulas by reduction to first-order validity: the soundness of the
finite-trace calculus (see [Finite-trace calculus](#finite-trace-calculus)),
and the first-order encoding with end-to-end soundness (see
[First-order encoding](#first-order-encoding)).

## File layout

The Ott file and the theories directly in `hol/` (apart from the Ott support
library) formalize the paper; the directories `hol/verif`, `hol/fol` and
`hol/vc` formalize the thesis.

- `ott/traces.ott`: syntax of Rec and of trace formulas, the SOS (Figure 1),
  SOS-induced traces (Definition 2.6), and the proof calculus (Figure 5 plus
  explicit structural rules). This file is the source of truth for these
  definitions.
- `hol/tracesScript.sml`: generated from the Ott file (`make hol/tracesScript.sml`).
  Do not edit it by hand.
- `hol/tracesSemScript.sml`: trace set operators, the denotational semantics
  of statements (Definition 3.1) and of formulas (Definition 4.2), the
  substitution lemma and fixed-point unfolding (Proposition 4.3).
- `hol/tracesSosScript.sml`: Theorem 3.2 (`Str_eq_Ssos`).
- `hol/tracesSoundScript.sml`: soundness (`calc_sound`, `calc_sound_empty`,
  `calc_sound_sos`) and a counterexample to soundness w.r.t. the paper's
  Definition 5.4 (`original_validity_counterexample`).
- `hol/tracesStfScript.sml`: strongest trace formulas (Definition 4.6,
  `stf`), Theorem 4.9 (`stf_Str`, and `stf_Ssos` for the SOS), Corollary 5.5
  (`stf_strongest`), lemmas about unfolding strongest trace formulas, and
  Example 4.8 (`example_4_8`, by evaluation).
- `hol/evenOddExampleScript.sml`: Example 4.7 (`example_4_7`, by
  evaluation) and Example 5.2 / Figure 6. It derives
  `⊢ even() : stf(even())` for the program of Example 2.2 in the calculus as
  in Figure 6 (`even_stf_derivable`), and by a shorter derivation without
  (Cons) at calls (`even_stf_derivable_short`). Soundness then gives validity
  for the denotational semantics (`even_stf_valid`) and for the SOS
  (`even_stf_valid_sos`).
- `doc/note.tex`: a short note that describes, in the notation of the
  paper, how the formalization differs from it. The table under
  [Note to HOL4](#note-to-hol4) maps its numbered items to HOL4 names.
- `hol/verif/`: formalization of the soundness results of Chapter 4 of
  the thesis, on top of the theories above. See
  [Finite-trace calculus](#finite-trace-calculus).
- `hol/fol/`: first-order logic with string names, proved equivalent to the
  deep embedding of HOL4's `examples/logic/folcompactness`, and the
  structure of the thesis's first-order logic (Section 4.1).
- `hol/vc/`: procedure contracts, the procedure contract condition
  (thesis Section 4.4), the encodings as first-order formulas, and end-to-end
  soundness of the resulting verification conditions. See
  [First-order encoding](#first-order-encoding).
- `hol/ott*.sml`: Ott support library for HOL4.

## Building

Dependencies: [HOL4](https://github.com/HOL-Theorem-Prover/HOL) at tag
`trindemossen-2-v9` with Poly/ML 5.9.2, and [Ott](https://github.com/ott-lang/ott)
0.34 to regenerate `hol/tracesScript.sml` from `ott/traces.ott`.

With `Holmake` from a HOL4 installation in your path, build all HOL4 files by
running this at the repository root:

```
Holmake
```

Holmake regenerates `hol/tracesScript.sml` when `ott/traces.ott` is newer.
This needs `ott` in your path. The theories in `hol/fol` and `hol/vc` use
`examples/logic/folcompactness` of the HOL4 distribution, which Holmake
builds inside the HOL4 installation.

Alternatively, build with [holbuild](https://github.com/hol-theorem-prover/holbuild).
It fetches and builds the HOL4 commit pinned in `holbuild.toml`, with
`folcompactness` as a dependency through the manifest in `shims/`, and does
not run Ott:

```
make hol/tracesScript.sml   # after changing ott/traces.ott
holbuild build
```

To typeset the Ott definitions and rules as `ott/traces.pdf` (needs `pdflatex`):

```
make ott/traces.pdf
```

To typeset the note as `doc/note.pdf` (needs Ott and `pdflatex`; the rule
figures are generated from `ott/traces.ott`):

```
make doc/note.pdf
```

## Note to HOL4

Numbered items of `doc/note.tex` and the corresponding HOL4 definitions and
theorems. Theory `traces` is generated from the Ott file.

| Note | HOL4 name | Theory |
|------|-----------|--------|
| Definition 2.1 (procedure tables) | `Tab` (type), `ALOOKUP`, `tbl_var_free` | `traces`, `tracesSos` |
| Definition 2.2 (relative trace semantics) | `Str0`, `ovr`, `H`, `rho0`, `Str` | `tracesSem`, `tracesSound` |
| Theorem 2.3 (paper Thm 3.2) | `Str_eq_Ssos` | `tracesSos` |
| Lemma 3.1 (substitution, paper Prop 4.3) | `f_sem_subst`, `fsem_unfold` | `tracesSem` |
| Definition 4.1 (paper Def 4.6) | `stf` | `tracesStf` |
| Lemma 4.2 (Bekič step) | `rho0_bekic` | `tracesStf` |
| Lemma 4.3 (open stf) | `stf_sem_ovr` | `tracesStf` |
| Theorem 4.4 (paper Thm 4.9) | `stf_Str`, `stf_Ssos` | `tracesStf` |
| Lemma 4.5 (exact hypotheses) | `rho0_ovr_solution`, `Str_ovr_solution` | `tracesStf` |
| Lemma 4.6 (unfolding stf) | (a) `stf_unfold_Str`, (b) `stf_unfold_mu` | `tracesStf` |
| Example 4.7 (paper Ex 4.7, 4.8) | `example_4_7`, `example_4_8` | `evenOddExample`, `tracesStf` |
| Figure 1 (calculus) | `calc` (rules `calc_skip`, …) | `traces` |
| Proposition 5.1 (counterexample) | `original_validity_counterexample` | `tracesSound` |
| Definition 5.2 (corrected validity) | `valid` (paper's version: `valid_orig`) | `tracesSound` |
| Proposition 5.3 | `valid_orig_empty` | `tracesSound` |
| Theorem 5.4 (paper Thm 5.6) | `calc_sound` | `tracesSound` |
| Corollary 5.5 | `calc_sound_empty`, `calc_sound_sos` | `tracesSound` |
| Lemma 5.6 (fixed-point induction) | `call_fixpoint_induction`, `call_sound` | `tracesSound` |
| Corollary 5.7 (paper Cor 5.5) | `stf_strongest` | `tracesStf` |
| Theorem 6.1 (paper Ex 5.2, Fig 6) | `even_stf_derivable`, `even_stf_valid`, `even_stf_valid_sos`; (Cons) steps `if_then_ent`, `if_else_ent`, `odd_call_ent`, `even_var_ent` | `evenOddExample` |
| Remark 6.2 | `even_stf_derivable_short` | `evenOddExample` |
| Figure 2 (SOS) | `c_red`, `sos_tr`, `Ssos` | `traces`, `tracesSos` |

## Deviations from the paper

- **Validity of sequents (Definition 5.4).** The paper's definition makes the
  (Call) rule unsound for a non-empty antecedent:
  `original_validity_counterexample` derives `Y_m1 : false ⊢ m() : Id⌢Id⌢false`
  for `T = {m {m1()}, m1 {skip}}`, which is invalid. The corrected `valid`
  interprets procedures `m` with `Y_m ∈ dom Γ` as their continuation
  `skip;Y_m`, and the other procedures by the least fixed point relative to
  these. For `Γ = ∅` the two definitions coincide (`valid_orig_empty`).
  Soundness is proved for all sequents w.r.t. the corrected definition. For
  `Γ = ∅` that gives the paper's statement, both for the denotational
  semantics and, via Theorem 3.2, for the SOS.
- **Multiple procedures.** The proof of (Call) does fixed-point induction on
  the whole procedure system at once (`call_fixpoint_induction`), instead of
  the paper's single-procedure argument plus Bekič's principle.
- **Antecedents.** Γ contains only judgments `Y : φ` about statement variables.
  `Y_m` is identified with the name `m`. The (Call) side condition is
  `Y_m ∉ dom Γ` rather than `Y_m : φ_m ∉ Γ`.
- **Structural rules.** The paper omits them. The calculus has (Ax), (Weak),
  (Cut), (∧R), (∧L) and (ConsL). Weakening and cut must preserve `dom Γ`,
  because the corrected semantics depends on `dom Γ`. ∨L is unsound for trace
  judgments and is not included.
- **(Cons)** takes an entailment oracle `E` as a parameter of the calculus.
  Soundness assumes `ent_sound`: E only answers yes for semantically valid
  entailments.
- **(Unfold)** requires `µX.φ` to be closed, so that Ott's substitution
  (which is not capture-avoiding) agrees with semantic substitution. Judgment
  formulas are otherwise not required to be closed; open variables are
  interpreted as `∅`.

  Plain substitution is enough here. (Unfold) is the only rule that
  substitutes, and it only substitutes the formula `µX.φ` itself. When that
  formula is closed, nothing can be captured, so plain and capture-avoiding
  substitution give the same result (up to renaming of bound variables). The
  side condition costs nothing for the paper's derivations: Definition 5.1
  requires judgment formulas to be closed, and the body of a closed `µX.φ`
  has no free variables other than `X`. The strongest trace formulas
  `stf(∅, S)` used for completeness (Theorem 5.7) are closed as well.
  Capture-avoiding substitution would only matter for rules that substitute
  open formulas, such as the fixed-point induction rule for entailment in
  Section 8.
- **Procedure tables** are association lists, looked up with `ALOOKUP`
  (first match), so duplicate names need no well-formedness side condition.
  Soundness and Theorem 3.2 assume that procedure bodies contain no statement
  variables (`tbl_var_free`).
- **States** are total functions `string -> int`. Arithmetic and Boolean
  expressions are concrete (as in the earlier Ott file). Other relation
  symbols `Q` are interpreted by a parameter `relI`.
- **Strongest trace formulas (Definition 4.6).** The recursion variable
  `X_m` is named `m`, as `Y_m` is, and the set X of Figure 4 is a list.
  Termination is by the number of declared procedures not in X, then by the
  size of S. For a statement variable `Y`, `stf(Y) = X_Y`. Theorem 4.9 is
  proved for programs without statement variables, as for soundness. Its
  proof does not use modal equation systems (Appendix A.2). Instead,
  `stf_sem_ovr` generalizes it to open formulas: with the procedures in X
  treated as statement variables (as in the corrected validity), `stf(X, S)`
  denotes the traces of S. The case of a call is one step of Bekič's
  principle (`rho0_bekic`). Corollary 5.5 is proved as an equivalence:
  `S : φ` is valid iff `stf(S)` entails φ.
- **Examples 4.7 and 4.8.** With the naming above, the formulas are those of
  the paper, with chop associated to the right, as Definition 4.6 builds it.
  In Example 4.8, `x > 0` is written `¬(x ≤ 0)`, since Boolean expressions
  have no `>`, and so `x ≤ 0` appears as `¬¬(x ≤ 0)`.
- **Example 5.2 / Figure 6.** The oracle for (Cons) is semantic entailment
  (`sem_ent`). The derivation follows Figure 6, with explicit steps in place
  of the vertical dots. Each of the two (Cons) steps at `odd()` and `Y_even`
  relates a strongest trace formula to its unfolding; both formulas have the
  same semantics by Theorem 4.9 and the unfolding lemmas (`stf_unfold_Str`,
  `stf_unfold_mu`). The other (Cons) steps are the premises of (If). Their
  entailments hold for any formulas of the shape `(b ∧ Id⌢F₁) ∨ (¬b ∧
  Id⌢F₂)` (`if_then_ent`, `if_else_ent`). A shorter derivation
  (`even_stf_derivable_short`) uses the unfolded formula as the contract for
  `odd()`, which makes the two (Cons) steps unnecessary.

## Finite-trace calculus

The directory `hol/verif` formalizes Lemma 4.16, Theorem 4.29 and Lemma 4.30
of the thesis: the trace constraints `tc(S)` hold for every effective trace
of `S`, a trace whose effective trace satisfies the finite-trace calculus
`ftc(S, φ)` is in `||φ||`, and validity of `tc(S) ⇒ ftc(S, φ)` implies
`Str[[S]] ⊆ ||φ||`. The encodings are embedded shallowly, as predicates on
state sequences `num -> state`; the first-order logic of Section 4.1 is
formalized separately (see [First-order encoding](#first-order-encoding)).
Several thesis definitions are corrected, and counterexamples show why; in particular, Theorem 4.29 and Lemma 4.30 fail with the thesis's
`distr`, which distributes chop over conjunction. Examples of the thesis,
among them the motivating Example 3.1 and Examples 4.31 and 4.32, are
verified with the corrected definitions. Examples 6.5 and 6.6 show that
the method is incomplete: every trace satisfies the specification, but the
verification condition fails for every contract the procedures conform
with. `doc/verif.tex` (`make doc/verif.pdf`) describes the changes; the
table maps its numbered items to HOL4 names.

| Note | HOL4 name | Theory |
|------|-----------|--------|
| Definition 3.1 (contracts, thesis Def 4.5, 4.6) | `conforms` | `verifEff` |
| Proposition 3.2 (thesis Def 4.8 inadequate) | `Seff_thesis`, `Seff_thesis_counterexample` | `verifCounterexamples` |
| Definition 3.3 (effective traces) | `eff` (rules `eff_skip`, …), `eff_props`, `eff_Str` | `verifEff` |
| Lemma 3.4 (replaces thesis Lemma 4.9) | `Str_eff` | `verifEff` |
| Placing a trace in a state sequence | `agree`, `agree_exists` | `verifEff` |
| Definition 4.1 (normal form) | `atomic`, `nf` | `verifNorm` |
| Definition 4.2 (thesis Def 4.13) | `tc` | `verifTc` |
| Proposition 4.3 (shape condition too weak) | `no_if_left`, `no_if_left_counterexample` | `verifNorm`, `verifCounterexamples` |
| Lemma 4.4 (thesis Lemma 4.16) | `eff_tc` | `verifTc` |
| Definition 4.5 (normalization) | `seqn`, `norm`, `norm_lk` | `verifNorm` |
| Lemma 4.6 (thesis Lemma 4.11, generalized) | `Str0_seqn`, `Str0_norm`, `nf_norm`, `Str_norm`, `conforms_norm_lk` | `verifNorm` |
| Definition 5.1 (thesis Def 4.17) | `pred` | `verifPred` |
| Lemma 5.2 (thesis Lemma 4.19) | `pred_sound` | `verifPred` |
| Proposition 5.3 (thesis Lemma 2.22, 4.24 fail for ∧) | `distr_and_counterexample` | `verifCounterexamples` |
| Definition 5.4 (thesis Def 4.20) | `expand` | `verifPred` |
| Lemma 5.5 (thesis Lemma 4.21) | `expand_sem`, `fv_f_expand` | `verifPred` |
| Definition 5.6 (thesis Def 4.23, corrected) | `distr`, `chopd` | `verifPred` |
| Lemma 5.7 (thesis Lemma 4.24) | `distr_sem`, `fv_f_distr` | `verifPred` |
| Definition 6.1 (thesis Def 4.28) | `ftc`, `ftc0` | `verifFtc` |
| Theorem 6.2 (thesis Theorem 4.29) | `ftc_sound` (via `ftc_claim_all`, `ftc0_sound`, `good`) | `verifFtc` |
| Lemma 6.3 (first call) | `side_condition_sound` | `verifFtc` |
| Theorem 6.4 (thesis Lemma 4.30) | `vc_sound`; thesis version `vc_sound_nf` | `verifFtc` |
| Definition 7.1 (thesis Def 4.23, 4.26 as stated) | `distr_thesis`, `normalised`, `ftc_thesis` | `verifFtcThesis` |
| Theorem 7.2 (thesis Theorem 4.29, Lemma 4.30 fail with thesis `distr`) | `phi0_empty`, `ftc_thesis_unsound`, `vc_thesis_unsound` | `verifFtcThesis` |
| Lemma 8.1 (conformance of `m`) | `m_call_inv`, `m_conforms` | `verifExamples` |
| Theorem 8.2 (thesis Example 3.1) | `ex31_vc`, `ex31`, `ex31_nonvacuous` | `verifExamples` |
| Theorem 8.3 (thesis Examples 4.31, 4.32) | `ex431_vc`, `ex431`, `ex432_weak_fails`, `ex432_vc`, `ex432` | `verifExamples` |
| Proposition 8.4 (thesis Examples 4.12, 4.15, 4.18, 4.25) | `ex412`, `ex415`, `ex418`, `ex425` | `verifExamples` |
| Theorem 9.1 (thesis Example 6.5) | `ex65_incomplete` (via `ex65_Str`, `m65_call_phi`, `m65_terminates`) | `verifIncompleteness` |
| Theorem 9.2 (thesis Example 6.6) | `ex66_fsem`, `ex66_normalised`, `ex66_ftc_fails`, `ex66_incomplete`, `ex66_mu_fsem`, `ex66_mu_vc`, `ex66_mu` | `verifIncompleteness` |
| Chop lemmas | `IN_chop`, `chop_assoc`, `chop_union_l`, `chop_union_r`, `chop_restrict_l`, `chop_dup_l` | `verifChop` |

## First-order encoding

The directories `hol/fol` and `hol/vc` formalize the first-order logic of
Section 4.1 of the thesis as a deep embedding, the procedure contract
condition and Lemmas 4.35 and 4.36 of Section 4.4, and a conversion of a
program, its contracts and a specification to first-order verification
conditions. The end-to-end theorems state that if the verification
conditions hold in the thesis's structure (integers and states), every
trace of the program satisfies the specification; one version has states
over the program variables and `Id`, `Sb` as conjunctions, as in the Z3
encoding of the [tool accompanying the thesis](https://github.com/F200907/ftc-tool).
`doc/fol.tex` (`make doc/fol.pdf`) describes the design and the relation
to the thesis; the table maps its numbered items to HOL4 names.

| Note | HOL4 name | Theory |
|------|-----------|--------|
| Definition 2.1 (string syntax) | `sterm`, `sform`, `smodel`, `stermval`, `sholds` | `folString` |
| Theorem 2.2 (agreement with folcompactness) | `sform2form`, `smodel2model`, `sholds_holds`, `sholds_satisfies` | `folString` |
| Definition 2.3 (thesis Def 4.1, 4.2) | `rec_fun`, `rec_pred`, `rec_model`, `int_const`, `svar`, `a2sterm`, `b2sform`, `Id_sform`, `Sb_sform`, `sforall_state` | `folRec` |
| Lemma 2.4 | `stermval_a2sterm`, `sholds_b2sform`, `sholds_Id_sform`, `sholds_Sb_sform`, `sholds_sforall_state` | `folRec` |
| Definition 3.1 (thesis Def 4.5, 4.6) | `ta`, `tb`, `ta_eval`, `tb_eval`, `cpre`, `cpost` | `vcContract` |
| Definition 3.2 (thesis Def 4.34) | `pcc` | `vcPcc` |
| Lemma 3.3 | `eff_tc_below` | `vcPcc` |
| Lemma 3.4 | `pcc_sound` | `vcPcc` |
| Theorem 3.5 | `pcc_conforms_set` | `vcPcc` |
| Corollary 3.6 (thesis Lemma 4.35, 4.36) | `pcc_conforms_one`, `pcc_conforms`, `pcc_conforms_norm` | `vcPcc` |
| Definition 4.1 | `stb`, `pred_fol`, `tc_fol`, `ftc_fol`, `ftc0_fol`, `pcc_fol`, `pcc_valid_fol`, `sforall_from`; shallow `ftc_dom`, `ftc_dom_univ` | `vcGen` |
| Theorem 4.2 | `vagree`, `pred_fol_sem`, `tc_fol_sem`, `ftc_fol_sem`, `pcc_fol_sem`, `sholds_side_condition`, `sholds_pcc_valid_fol` | `vcGen` |
| Definition 5.1 | `vc_main`, `vc_fols` | `vcSound` |
| Theorem 5.2 | `sholds_vc_main`, `vc_fols_sound`, `vc_fols_sound_fol`, `satisfies_sholds` | `vcSound` |
| Definition 6.1 | `xs_states`, `proj`, `svars`, `fvars`, `ct_over` | `vcXs` |
| Lemma 6.2 | `tc_proj`, `ftc_proj`, `pcc_proj`, `pred_proj` | `vcXs` |
| Definition 6.3 (thesis Def 4.1) | `Id_xs`, `Sb_xs`, `expand_atoms`, `vc_fols_xs`; `sholds_expand_atoms` | `vcXs` |
| Theorem 6.4 | `vc_fols_sound_xs`, `vc_fols_xs_sound`, `vc_fols_xs_sound_fol` | `vcXs` |
| Proposition 7.1 | `ct31_pcc_valid`, `ct31_conforms`, `ct_wrong_not_pcc_valid` | `vcExamples` |
| Proposition 7.2 | `ex31_vc_fols`, `ex31_fol`, `ex31_xs_vc`, `ex31_xs`, `ex432_fol_weak_fails`, `ex432_fol` | `vcExamples` |
| Proposition 7.3 (thesis Section 5.4, Examples 5.5, 5.6, 5.8, 5.10, 5.12) | `ex55_tc_shape`, `ex55`, `ex55_xs`, `ex56_rejected`, `ex56_violation`, `ex58`, `ex58_xs`, `ex510`, `ex510_xs`, `ex512`, `ex512_xs` (via `vc_fols_of_shallow`, `vc_fols_xs_of_shallow`) | `vcEval` |
