# CLAUDE.md: working instructions for the AI assistant

Read this file and `README.md` §1, §6, §8, §9 at the start of every session.

## 1. What I am doing here

I am helping formalize **Theorem B of Campos–Samotij** in Lean 4 / mathlib,
**conditional on Proposition 2.2**, following the paper's Section 4. I am
also keeping the roadmap accurate enough that a person, or a later session
of me with no memory of this one, can continue from `README.md` alone.

Success means the Definition of Done in README §1. Anything else, such as
elegant generality, mathlib PRs, or proving Prop 2.2, is secondary until then.

## 2. Hard rules (never break without explicit human approval)

1. **Never change a frozen statement** in `Statement.lean` to make a proof go
   through. If a statement looks wrong, stop and report it (§5).
2. **Never use `axiom`.** Proposition 2.2 is the hypothesis
   `(hProp22 : Prop22Statement)`. Nothing else may be assumed.
3. **Never weaken the theorem silently.** This covers: adding hypotheses,
   changing $\ge$/$>$, changing the exponent, restricting $p,\delta$, or
   replacing $\mathcal I(H)$ with $\mathcal I(H_J)$ in a conclusion.
4. **Never report a milestone done** unless its file builds and
   `grep -n "sorry" <file>` is empty. Before claiming M8, run
   `#print axioms CamposSamotij.theoremB`.
5. **Never invent mathlib lemma names in final code.** Search first
   (`exact?`, `apply?`, `#check`, Loogle, grep the mathlib source). If I
   write a name from memory, I compile it before relying on it.
6. **Paper over README.** If the README's math and the paper disagree, the
   paper wins. Log the discrepancy in README §8.
7. **Record every divergence from the paper in [`divergence.md`](divergence.md)**
   (paper / Lean / why / effect / status). This covers extra hypotheses, representation
   choices, and choice rules. Required by the human (2026-09-29).

## 3. Uncertainty protocol (required)

Whenever I am unsure about a step, I say so **explicitly and visibly**. I do
not bury it. Use this format in chat and as a Lean comment:

```
⚠ UNSURE: <what> — <why> — <how to resolve: check paper p.?, test, ask>
```

Cases that always trigger it:

- a statement I reconstructed rather than read in the paper (Prop 2.2
  currently, the eligibility condition, strictness in Theorem B(3));
- a mathlib API whose name or signature I have not compiled at the pinned version;
- a proof step I believe but have not seen Lean accept;
- any design choice that deviates from README §7 "Decided" rows.

## 4. Session workflow

1. **Orient.** Read README §8 (open discrepancies) and §9 (status). Pick
   the lowest-numbered unfinished milestone whose dependencies are done.
2. **State before proving.** Write the lemma in paper notation in a comment,
   then its Lean statement, then `sorry`, then build. The statement must
   typecheck before any proof work starts.
3. **Small lemmas first.** Membership characterizations → `simp` lemmas →
   equivalences → main lemma. Target 5–30 lines per proof. If a proof grows
   past ~60 lines, extract lemmas.
4. **Build often.** `lake build CamposSamotij.<Folder>.<File>` after each lemma.
5. **Close out.** Update README §9 status and §8 log if anything changed.
   Then summarize for the human: what was proved, what is `sorry`, and
   every ⚠ UNSURE item.

## 5. When to stop and ask the human

- A frozen statement appears false or unprovable (give a counterexample if possible).
- The paper and README disagree and the choice changes a statement.
- A design decision marked **Proposed** in README §7 needs to become **Decided**.
- I need a hypothesis the paper does not state (for example $V$ nonempty, $H$ without $\varnothing$).
- A milestone needs substantial new general probability infrastructure.
  Propose isolating it in its own file first.

## 6. Lean conventions for this project

- Namespace `CamposSamotij`. One file per milestone, grouped in subfolders (README §6 Layout).
- Variables: `{V : Type*} [Fintype V] [LinearOrder V]`. Never add `[DecidableEq V]` next to
  `[LinearOrder V]`, since that gives two instances. Files below `Algorithm/` that need no order
  (`Hypergraph/`, `Probability/`, `Prop22/Statement.lean`) take `[DecidableEq V]` alone.
- Hypergraphs: `Finset (Finset V)`. Independence:
  `def IsIndep (H : Finset (Finset V)) (I : Finset V) : Prop := ∀ e ∈ H, ¬ e ⊆ I`.
- Link: `def link H v := (H.filter (v ∈ ·)).image (·.erase v)`, with update
  `H ∪ link H v`. Prove `mem_link : A ∈ link H v ↔ ∃ B ∈ H, v ∈ B ∧ B.erase v = A`
  first, and mark it `@[simp]`.
- Probability (if README §7 proposal accepted): a `weight` / `probOn` /
  `condProb` / `condExp` API over `Finset` sums. Downstream proofs use only
  API lemmas and never unfold `probOn`.
- Keep `Algorithm/Defs.lean` free of probability *proofs*. It may *use* `condProb`
  in `eligible`, but the lemmas about it live elsewhere.
- Use `Classical` for decidability of `eligible`. Mark defs `noncomputable`
  as needed. "Deterministic" means "a function of `(H_i, S_i)`". It does not
  mean computable.
- Name lemmas after the paper when they correspond: `lemma41_invariant`,
  `lemma42_card_S`, `lemma43_prob`, `theoremB`.
- Keep `decide`-checkable toy examples (3–4 vertices) in `Examples.lean` to
  sanity-check definitions such as `link` before proving things about them.

## 7. Known traps

- **Eligibility must exclude singleton-edge vertices**, or `run` never stabilizes (README §4.2).
- **Conditional probability needs $P_i > 0$.** Carry it as a lemma from
  $\varnothing \in \mathcal I(H_i)$ and $p<1$. Do not assume it.
- **Strictness.** $C' = \varnothing$ makes strict inequalities false. Prove $\ge$.
- **Coupling identity (Lemma 4.3 step 3)** is the hardest probabilistic step.
  Do it as a finite-sum factorization over $V = S \sqcup C' \sqcup (V\setminus C)$,
  not with measure theory.
- **Real exponents.** $(1-p)^{\delta|C'|}$ has a real exponent, so use
  `Real.rpow` and keep $0<1-p$ available as a hypothesis.
- **Replay lemma.** `f` is defined by rerunning on `S`. Prove
  `run H I = run H (run H I).S` by induction on the iteration count, with the
  invariant "the states agree up to stage $k$".

## 8. Tone of reports to the human

Short, factual, and in this order: **done / in progress (`sorry` count) /
⚠ UNSURE items / questions needing a decision.** Do not overstate progress.
"Compiles with 3 sorries" is a precise and acceptable report.
