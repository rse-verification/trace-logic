# Trace logic for recursive programs in HOL4 - Notes for agents

This repository formalizes a paper in HOL4, with syntax, operational semantics
and proof rules written in Ott and exported to HOL4. See `README.md` for the
layout, the main theorems, and the deviations from the paper. Most of the
notes below apply to any Ott + HOL4 formalization.

## Building

- `Holmake` at the repository root builds all HOL4 files. The root
  `Holmakefile` has `CLINE_OPTIONS = -r` and lists the HOL directories in
  `INCLUDES`.
- A new HOL directory (e.g. `hol/verif`) must be added in two places: to
  `INCLUDES` in the root `Holmakefile` for Holmake, and to `members` in
  `holbuild.toml` for holbuild. It also needs its own `Holmakefile` with
  `INCLUDES = ..` to see the theories in `hol`.
- Theories from HOL's `examples` (e.g. `examples/logic/folcompactness`) are
  not in HOL's sigobj. For Holmake, add `$(HOLDIR)/examples/...` to
  `INCLUDES` of each directory that uses them; Holmake then builds them
  inside the HOL installation. For holbuild, declare a dependency with
  `from = "hol"`, the `path`, and a `manifest` in `shims/`, since the
  example has no `holbuild.toml` of its own.
- `holbuild build` builds against the HOL4 commit pinned in `holbuild.toml`.
  `rev` must be the commit of the tag (`git ls-remote
  https://github.com/HOL-Theorem-Prover/HOL.git 'refs/tags/<tag>^{}'`), not the
  SHA of the annotated tag object.
- if Ott is installed in the opam switch `my-switch`, then outside that switch,
  call it as `opam exec --switch=my-switch -- ott`, as the `Makefile` does.
- `make hol/tracesScript.sml` regenerates the HOL script from `ott/traces.ott`.
  `make ott/traces.pdf` typesets the Ott file. The generated script is
  committed; never edit it by hand.
- Hand-written theory scripts start with a `Theory` / `Ancestors` header
  and have no `new_theory` or `export_theory` call. Two scripts keep the old
  style: the generated `hol/tracesScript.sml`, and `hol/ottScript.sml`,
  which is kept as in Ott repository upstream as far as possible.
- Before finishing, do a clean build: `Holmake cleanAll && Holmake`. Then check
  that no main theorem depends on a cheat or oracle: `grep -rn cheat hol`,
  and `Tag.dest_tag (Thm.tag th)` should list no oracles besides `DISK_THM`.

## Using holbuild effectively when developing proofs

- Use `holbuild build --tactic-timeout 60 <theory>Theory` so a looping tactic
  fails within a minute. The default timeout is 600 s.
- When a proof fails, holbuild prints the failing tactic fragment, its
  position in the source and the goal it was applied to, then resumes from a
  checkpoint on the next build. Read the printed goal and fix that step,
  rather than rewriting the whole proof.
- A theory built with a short timeout is reused by later builds with a longer
  timeout. So a plain `holbuild build` afterwards may do nothing; use a clean
  Holmake build as the final check.
- To inspect theorems, types or goals non-interactively, pipe commands into
  the REPL:
  `printf 'load "fooTheory"; open fooTheory;\nprint_thm bar;\n' | holbuild repl`.
  Check how a generated constant and its rules look before proving anything
  about them.
- A REPL session has no tactic timeout, and a diverging `EVAL` can use
  15 GB of memory or more. Bound it:
  `printf '...' | (ulimit -v 4000000; timeout 120 hol)`. Load the libraries
  the theory uses (e.g. `intLib`) before `EVAL`: without `intLib`, `EVAL`
  cannot decide `0 <= -3`, evaluates both branches of the conditional, and
  `toString` on an unreduced argument unfolds forever.

## Ott to HOL4 export

- Every metaproduction (`:: M ::`) and every nonterminal defined only by a
  type needs a `{{ hol ... }}` hom. Ott refuses to export otherwise.
- **Name clashes with HOL constants.** Ott uses metavariable and nonterminal
  names as HOL variable names, e.g. `!(T:T)`. Names like `T`, `F`, `S`, `I`,
  `K`, `C`, `W` and `o` are HOL constants. They are parsed as the constant,
  and the definition either fails or silently changes meaning: a procedure
  table nonterminal named `T` turned into `bool`, which made `ALOOKUP` a
  variable. Use another name and keep the paper's notation for LaTeX:
  `Tab {{ tex T }} :: Tab_ ::= ...`. The same clash happens in hand-written
  HOL: a free `S` in a quotation (`qexists_tac`, `Definition`, `case ... of
  SOME S =>`) is the S combinator. Use `S0`, `body`, `Fn` and similar names.
- **Parameters of relations.** A free variable in a hol hom (e.g. an oracle
  `ent`, or a procedure table) is universally quantified separately in each
  rule. It does not become a parameter of the relation. Make such parameters
  explicit arguments of the judgement (`Tab ; E ; G |- S : f`), and hide them
  in LaTeX with a tex hom on the `defn`:
  `defn ... :: :: calc :: calc_ {{ tex [[G]] \vdash [[S]] : [[f]] }}`.
- A nonterminal that is only a HOL type (e.g. `E :: E_ ::= {{ hol (f -> f ->
  bool) }}`) still needs at least one production. A dummy `:: M ::`
  production is enough.
- Generated function names are `<name>_<nonterminal>`:
  `substitutions single f X :: subst` gives `subst_f`, and
  `freevars f X :: fv` gives `fv_f`. Hol homs must use those names. The
  generated substitution is not capture-avoiding; it only stops at a binder
  for the same variable (`bind X in f`).
- Run ott from the directory of the generated script
  (`cd hol && ott -i ../ott/traces.ott -o tracesScript.sml`). Otherwise
  `new_theory` gets the output path, e.g. `"../hol/traces"`.
- Theories needed by homs must be opened in an `embed {{ hol ... }}` block
  before use, e.g. `alistTheory` for `ALOOKUP`. Embeds appear in the output
  after the datatypes, in file order, so definitions in embeds can use the
  generated types, and rules can use those definitions.
- Each `defns` block becomes one `Inductive`. Its relations share
  `<block>_rules`, `<block>_ind`, `<block>_strongind` and `<block>_cases`, and
  each rule is also stored under its own name. Every rule has a
  `clause_name "..."` premise; remove it with
  `SIMP_RULE std_ss [clause_name_def]`.
- To prove a property of one relation in a mutual block, give
  `ho_match_mp_tac <block>_strongind` a conjunction where the other relation's
  property is trivial: `(!... . c_red ... ==> P) /\ (!... . sos_tr ... ==> T)`.
- Use `*_strongind` rather than `*_ind` when a case needs a premise whose
  induction hypothesis is vacuous, e.g. a step into a final configuration.

## HOL4 proof engineering

- After `rw`, bound variables may be renamed (e.g. `m` to `m'`). Before naming
  them in `qspec_then` or `qexists_tac`, fix the name with `qx_gen_tac` or
  `rename1`.
- The order of subgoals after `Induct >> rw[...]` is hard to predict. Prefer a
  battery like `FIRST [tac1 >> NO_TAC, tac2, ...]`, or `TRY (... >> NO_TAC)`,
  over long `>-` chains.
- Do not end a proof with a blanket `TRY (metis_tac[])` over many goals: on a
  goal it cannot solve, metis can run until the tactic timeout.
- Do not use `rw[FUN_EQ_THM]` on functions into sets: it unfolds the sets
  too. Use `AP_TERM_TAC >> CONV_TAC FUN_EQ_CONV >> gen_tac >> BETA_TAC`.
- `rw` normalizes set comprehensions (e.g. `{t | ?s s'. t = [s;s'] /\ s' = s}`
  becomes `{t | ?s. t = [s;s]}`), so rewriting with an equation stated in the
  original form may fail. Prove such facts directly with `EXTENSION` and the
  definitions.
- Give fixed-point operators a name (e.g. `mu_sem Fn = BIGINTER {g | Fn g
  SUBSET g}`) and prove generic lemmas about them (least, greatest, monotone,
  fixed point). The cases for binders then reduce to `AP_TERM_TAC` plus a
  pointwise equation.
- Least fixed points defined as intersections of pre-fixed points need no
  continuity argument. To show `lfp H <= r`, show that `r` is a pre-fixed
  point.
- `rw` does not rewrite with assumptions; `fs` does. Use `fs` when a case
  split depends on a hypothesis such as `m NOTIN D`.
- Rule induction on an `Inductive` relation: use `ho_match_mp_tac
  <rel>_strongind` when a case needs the premises themselves (e.g. to invert
  them or apply another lemma to them); `<rel>_ind` keeps only the induction
  hypotheses. If the relation has a parameter (a variable free in every rule,
  such as a procedure table `lk`), state the goal as `!lk x y. rel lk x y ==>
  ...` and do `gen_tac` before `ho_match_mp_tac`; otherwise matching fails
  with `match: safe_insert`.
- After `rw[..., PULL_EXISTS]` the order of the existentials in the goal is
  hard to predict, so witnesses in `qexistsl_tac` often land in the wrong
  places. Read the goal holbuild prints first, or select and name things by
  pattern: `>~ [`fsem relI (f_chop f1 f2)`]` picks the goal and renames its
  variables, `qmatch_goalsub_rename_tac` names subterms of the goal.
- With `intLib` loaded (`Libs intLib`), an unannotated numeral defaults to
  `int`. A definition like `stb S_skip = 1` then gets type `S -> int`, and
  `decide_tac` fails on it. Annotate: `stb S_skip = 1:num`.
- `CONV_TAC FUN_EQ_CONV >> gen_tac` may name the new variable unexpectedly
  (e.g. `l` for a string argument); name it with `qx_gen_tac` before
  referring to it.
- `imp_res_tac` on an equivalence `A ==> (B <=> C)` adds `B <=> C` and both
  implications; `fs` can then rewrite back and forth until the tactic
  timeout. Add only the equivalence, e.g. with `MATCH_MP` on the known
  premises.
- `rw`/`fs` evaluate string tests on literals such as `isPREFIX "Sb_" p` into
  nested `case p of ...` terms, which later rewrites no longer match. Put
  the test in a small definition (e.g. `sb_name p`) with one characterizing
  lemma (`sb_name p = SOME x <=> p = "Sb_" ++ x`), and case split on it.
- Do not rewrite with `GSYM LIST_TO_SET_EQ_EMPTY` in `fs`: it loops. To show
  `l = []` from facts about `set l`, use `Cases_on `l`` and `EXTENSION`.
