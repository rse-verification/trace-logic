# Trace logic for recursive programs in HOL4

A HOL4 formalization of parts of D. Gurov and R. Hähnle, *An Expressive
Trace Logic for Recursive Programs* (arXiv:2411.13125, `trace-logic.pdf`),
up to soundness of the proof calculus (Theorem 5.6).

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
- **Procedure tables** are association lists, looked up with `ALOOKUP`
  (first match), so duplicate names need no well-formedness side condition.
  Soundness and Theorem 3.2 assume that procedure bodies contain no statement
  variables (`tbl_var_free`).
- **States** are total functions `string -> int`. Arithmetic and Boolean
  expressions are concrete (as in the earlier Ott file). Other relation
  symbols `Q` are interpreted by a parameter `relI`.
