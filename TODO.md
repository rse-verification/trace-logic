# TODO

Extensions of the formalization, in two parts: extensions of the paper
formalization (items 1.x) and of the thesis formalization (items 2.x),
each roughly in the suggested order. Paper references are to D. Gurov and
R. Hähnle, [An Expressive Trace Logic for Recursive
Programs](https://doi.org/10.48550/arXiv.2411.13125); thesis references are
to F. Stevanovic, [Automated Verification of Finite-trace Properties for
Recursive Programs](https://urn.kb.se/resolve?urn=urn%3Anbn%3Ase%3Akth%3Adiva-368044)
(master's thesis, KTH, 2025).

Every item is done only when:

- the theories build cleanly (`Holmake cleanAll && Holmake`), with no
  `cheat` and no oracles besides `DISK_THM` in the main theorems (see
  `AGENTS.md`);
- new directories are added to `INCLUDES` in the root `Holmakefile` and to
  `members` in `holbuild.toml`;
- deviations from the paper or thesis are described in `doc/note.tex` (or the
  note of the relevant part, `doc/verif.tex`, `doc/fol.tex`, or a new one),
  and the README tables map the note's items to HOL4 names.

## 1. Paper formalization extensions

### 1.1. Relative completeness (paper Theorem 5.7, Corollary 5.8)

For Rec as currently formalized, before any Rec\* changes (item 1.2 only
adds one case to the proof afterwards).

- [ ] Move `sem_ent` (and `sem_ent_sound`) from `evenOddExample` to a core
      theory, e.g. `tracesSound` or a new `tracesComplete`.
- [ ] Define the completeness assumption on the oracle, mirroring
      `ent_sound`: `ent_complete relI E` if `E` answers yes for every
      semantically valid entailment (`sem_ent relI f1 f2 ==> E f1 f2`).
- [ ] Define a well-formedness condition saying that every procedure called
      in the program (statement and table bodies) is declared. Without it
      Corollary 5.8 fails: an undeclared call has the empty trace set (`H`
      gives `{}`), so `m() : φ` is valid for every φ, but no rule derives it.
- [ ] Generalize Theorem 5.7 to any set D of procedures: with
      Γ_D = {Y_m : µX_m.stf({m}, S_m) | m ∈ D}, derive
      Γ_D ⊢ S[Γ_D] : stf(∅, S). Suggested proof: induction on the
      termination measure of `stf` (procedures not in D, then size of S); in
      the call case for m ∉ D use (Call), and bridge the open formulas
      `stf(X, S)` to the closed ones by (Cons) with semantic entailment, via
      `stf_unfold_Str` / `stf_unfold_mu`. Then (Unfold), with its closedness
      side condition, is not needed.
- [ ] Theorem 5.7 as stated in the paper (D = all declared procedures).
- [ ] Corollary 5.8: for a table without statement variables, a declared,
      variable-free S and closed φ, validity of `S : φ` implies derivability,
      using `stf_strongest` and (Cons). Also the version for the SOS
      (via `Str_eq_Ssos`), and soundness plus completeness as an equivalence.
- [ ] Record the deviations (complete oracle, declared calls, generalized
      Theorem 5.7) in `doc/note.tex`.

### 1.2. Rec\* in Ott (paper Section 6.1)

Extend `ott/traces.ott` with the statement `if * then S1 else S2`, its SOS
rules (∗-i), its denotational semantics `♯Str[[S1]] ∪ ♯Str[[S2]]`, its `stf`
clause `Id⌢stf(S1) ∨ Id⌢stf(S2)` and the rule (If-∗).

- [ ] Decide the representation. Suggestion, not decided: one datatype `S`
      with the new constructor, Rec as an Ott subrule (in HOL a predicate
      such as `is_rec S`), and the paper results carried over to Rec\*
      (item 1.3). The thesis theorems in `hol/verif` and `hol/vc` then
      get an `is_rec` hypothesis (cheap); extending them is item 2.1.
      Alternatives: a separate Rec\* type with an embedding of Rec, or a
      separate Ott file. Weigh how many functions and inductions over `S` change (`Str0`,
      `stf`, `var_free`, `subst_calls`, SOS, `eff`, `tc`, `norm`, `pred`,
      the FOL encodings).
- [ ] Define the restricted formula fragment of Section 6.1
      (`Id | Sb | X | p ∧ φ | φ ∨ ψ | φ⌢ψ | µX.φ`), e.g. as an Ott subrule
      of `f`. Note that it also excludes the `Q` relations (`relI`), which
      the paper does not have.
- [ ] Regenerate `hol/traces/tracesScript.sml` and repair the existing theories
      (adding the new cases, or `is_rec` hypotheses where item 2.1 is
      postponed).

### 1.3. Metatheory of Rec\* outside Section 6

Carry over the existing results to Rec\* (paper Section 6.1 claims each is
straightforward).

- [ ] Theorem 3.2 (`Str_eq_Ssos`) for Rec\*; the ∗-step is a stuttering step.
- [ ] Theorem 4.9 (`stf_Str`, `stf_sem_ovr`, `stf_Ssos`) and Corollary 5.5
      (`stf_strongest`) for Rec\*.
- [ ] Theorem 5.6 (`calc_sound` and corollaries) with (If-∗).
- [ ] Theorem 5.7 and Corollary 5.8 (item 1.1) with (If-∗).
- [ ] Show that `stf` only produces formulas of the restricted fragment of
      Section 6.1 (no bare `p`, conjunction only as `p ∧ φ`).

### 1.4. Section 6: new metatheory of Rec only

Results of Section 6 that need no non-determinism.

- [ ] Determinism of Rec: for a Rec program, each initial state has at most
      one trace (in `Str` and in the SOS).
- [ ] Example 6.1: the formula `Sb^0_y⌢µX.(Id ∨ Sb^{y+1}_y⌢X)` is not
      equivalent to any Rec program, not even modulo stuttering (by
      determinism); and the given Rec program `y := 0; m()` produces the same
      traces up to the auxiliary variable `x` (make "up to auxiliary
      variables" precise, e.g. by projection).
- [ ] Prop 6.4: `Str[[diverge]] = ∅` for `abort {abort()}`.
- [ ] Definition 6.6: stutter-free version of a trace, stuttering
      equivalence of trace sets, refinement `⪯` and its stuttering version,
      entailment modulo stuttering. Basic lemmas: `A = B` implies
      stutter-equivalence; interaction of destuttering with `chop`,
      `restrict` and `dup` (note that `‖Id‖` and `‖Sb^x_x‖` destutter to
      single states).
- [ ] Example 2.3 (`down`), used again in Example 8.1 (item 1.6).

### 1.5. Section 6: new metatheory touching both Rec and Rec\*

Canonical programs. The most demanding paper item; expect corrections to
the paper's statements.

- [ ] Definition 6.2: `can(φ) = ⟨S_φ, T_φ⟩` on the restricted fragment,
      with `diverge` and the `abort` declaration. Make the assumptions
      explicit: unique names of recursion variables (Ott's substitution is
      not capture-avoiding), and how concatenated tables `T_φ T_ψ` behave
      under `ALOOKUP` (first match).
- [ ] Example 6.3, by evaluation.
- [ ] Prop 6.5: for an open φ and declarations of its free recursion
      variables, `⟨S_φ, T_φ T'_φ⟩` is a well-defined Rec\* program (all calls
      declared, no statement variables, names unique).
- [ ] Theorem 6.7: for closed φ, `Str[[S_φ]]` is stutter-equivalent to
      `‖φ‖`. Needs a fixed-point argument modulo stuttering for `m_X()`
      versus `µX.φ`.
- [ ] Corollary 6.8 (Galois connection): `stf(S) ⊨~ φ` iff `S ⪯~ S_φ`, from
      Theorem 4.9 (for Rec\*, item 1.3) and Theorem 6.7.

### 1.6. Section 8: future work of the paper

One item for now; split it into finer items when starting on it.

- 8.1: reinstate `p`, the derived connective `φ · · ψ`, relations `R_b`,
  the statement `havoc` with its axiom and `stf`, and `can(p)`.
- 8.2: a calculus for implication of trace formulas with (FP-Ind) and
  (Cons-Left), its soundness, and Example 8.1
  (`stf(down()) ⇒ Id⌢Dec⁺_x`); compare with Heidler's calculus [16]. Such
  a calculus could discharge some (Cons) premises without an oracle.
- 8.3: termination measures in the calculus (total correctness for finite
  traces). Infinite traces and greatest fixed points change the semantic
  domain and are probably out of scope.

## 2. Thesis formalization extensions

### 2.1. Thesis encodings for Rec\*

Extend the formalization of the thesis (`hol/verif`, `hol/fol`, `hol/vc`)
from Rec to Rec\*, removing the `is_rec` hypotheses of item 1.2.

- [ ] Effective traces, trace constraints `tc` and normal form (`eff`, `tc`,
      `nf`, `norm`) with non-deterministic choice; `eff_tc`, `Str_eff`,
      `Str_norm`.
- [ ] `ftc` and `vc_sound` for Rec\*.
- [ ] Procedure contract condition and FOL encodings (`pcc`, `vc_fols`,
      `vc_fols_xs`) and their end-to-end soundness.
- [ ] An example with non-deterministic choice, verified end to end.

### 2.2. Discharging verification conditions with HolSmtLib

Orthogonal to the CakeML tool (item 2.3), but probably done before it;
lessons (term shapes Z3 handles, quantifiers, states as functions) carry
over.

- [ ] Translate the output of `vc_fols_xs` (`sform`) for concrete programs
      into HOL terms over `int`, extending `vc_fols_xs_of_shallow`.
- [ ] Discharge the verification conditions of the thesis examples
      (`vcEval`, `vcExamples`) with `HolSmtLib`, preferably with Z3 proof
      replay rather than as an oracle, and compare with the current proofs.
- [ ] Run the SMT calls on all tool examples as represented in HOL4,
      including those that do not "work": rejected or failing ones such as
      `ex56_rejected`, `ex432_fol_weak_fails` and the incompleteness
      examples of `verifIncompleteness`. Check that Z3's answer (unsat,
      sat, unknown, timeout) matches the expected outcome, and keep the
      runs as a regression test.
- [ ] Record which conditions Z3 cannot prove or replay (quantifiers over
      states, non-linear arithmetic) and why.
- [ ] Keep it in its own directory (e.g. `hol/smt`), in `holbuild.toml`.

### 2.3. A (partly) verified tool in CakeML

Mirror the [Haskell tool of the
thesis](https://doi.org/10.5281/zenodo.17093405) as closely as possible.

- [ ] Set up a separate directory (e.g. `cakeml/`) with its own holbuild
      member, depending on the CakeML tag that matches the HOL4 tag in
      `holbuild.toml` (`trindemossen-2-v10`), declared as for
      `folcompactness` (manifest in `shims/` if needed). Keep it out of the
      default build if it is too heavy.
- [ ] An SMT-LIB printer for `sform`, defined in HOL. State what is trusted:
      there is no SMT-LIB semantics in HOL4, so either document the mapping
      from `sform` to SMT-LIB, or prove a round trip with a parser.
- [ ] Translate the pipeline (`vc_fols_xs` and the printer) with the CakeML
      translator, giving a certificate theorem for the extracted code.
- [ ] Input: a parser for the tool's concrete syntax (verified or trusted).
- [ ] Calling Z3: either through the FFI (custom C code), or by writing a
      `.smt2` file and calling Z3 from a wrapper script; the latter keeps the
      process handling outside CakeML.
- [ ] Differential testing: carry over a small test suite from the thesis
      tool (its examples, including failing ones), run both tools on it, and
      compare the verdicts (and, where comparable, the generated SMT-LIB).
- [ ] End-to-end statement: if Z3 reports the negated verification
      conditions unsatisfiable, every trace of the input program satisfies
      its specification (modulo the trusted printer mapping and Z3).
