# Trace logic for recursive programs in HOL4

A HOL4 formalization of parts of D. Gurov and R. Hähnle, [An Expressive
Trace Logic for Recursive Programs](https://arxiv.org/abs/2411.13125),
up to soundness of the proof calculus (Theorem 5.6), together with the
characterisation of strongest trace formulas (Theorem 4.9) and the example
derivation of Figure 6.

## Layout

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
  F. Stevanovic, *Automated Verification of Finite-trace Properties for
  Recursive Programs* (master's thesis, KTH, 2025), on top of the theories
  above. See [Finite-trace calculus](#finite-trace-calculus).
- `hol/ott*.sml`: Ott support library for HOL4, from HolBA
  (`examples/bir/compute/src/theory`).

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
This needs `ott` in your path.

Alternatively, build with [holbuild](https://github.com/hol-theorem-prover/holbuild).
It fetches and builds the HOL4 commit pinned in `holbuild.toml` and does not
run Ott:

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

## Finite-trace calculus

The directory `hol/verif` formalizes Lemma 4.16, Theorem 4.29 and Lemma 4.30
of the thesis: the trace constraints `tc(S)` hold for every effective trace
of `S`, a trace whose effective trace satisfies the finite-trace calculus
`ftc(S, φ)` is in `||φ||`, and validity of `tc(S) ⇒ ftc(S, φ)` implies
`Str[[S]] ⊆ ||φ||`. The encodings are embedded shallowly, as predicates on
state sequences `num -> state`; the first-order logic of Section 4.1 is not
formalized. Several thesis definitions are corrected, and counterexamples
show why; in particular, Theorem 4.29 and Lemma 4.30 fail with the thesis's
`distr`, which distributes chop over conjunction. `doc/verif.tex` (`make doc/verif.pdf`) describes the changes; the
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
| Definition 5.4 (thesis Def 4.23, corrected) | `distr` | `verifPred` |
| Lemma 5.5 (thesis Lemma 4.24) | `distr_sem`, `fv_f_distr` | `verifPred` |
| Definition 6.1 (thesis Def 4.28) | `ftc`, `ftc0` | `verifFtc` |
| Theorem 6.2 (thesis Theorem 4.29) | `ftc_sound` (via `ftc_claim_all`, `ftc0_sound`, `good`) | `verifFtc` |
| Lemma 6.3 (first call) | `side_condition_sound` | `verifFtc` |
| Theorem 6.4 (thesis Lemma 4.30) | `vc_sound`; thesis version `vc_sound_nf` | `verifFtc` |
| Definition 7.1 (thesis Def 4.20, 4.23, 4.26 as stated) | `expand`, `distr_thesis`, `normalised`, `ftc_thesis` | `verifFtcThesis` |
| Theorem 7.2 (thesis Theorem 4.29, Lemma 4.30 fail with thesis `distr`) | `phi0_empty`, `ftc_thesis_unsound`, `vc_thesis_unsound` | `verifFtcThesis` |
| Chop lemmas | `IN_chop`, `chop_assoc`, `chop_union_l`, `chop_restrict_l`, `chop_dup_l` | `verifChop` |

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
