# CLAUDE.md: working instructions for the AI assistant

Read this file and `README.md` §1, §8, §9, §10 at the start of every session. For packet work,
also read `logs/README.md` and the packet files listed in §5.

## 1. What I am doing here

The formalization is **finished** (2026-09-29). **Theorem B of Campos–Samotij** is proved in
Lean 4 / mathlib with no hypotheses (`theoremB_unconditional`). **Proposition 2.2** is proved too
(`prop22`). The library has no `sorry` and no `axiom`. The conditional `theoremB` (with
`hProp22 : Prop22Statement`) is kept, so the dependency stays visible.

**Current phase: the competition submission packet.** Two judges will review the repository
independently. My job is to make it easy to inspect and to make every claim in it checkable. Each
claim either points to a file, a log or a commit, or is marked as unverified.

The work is in this order:

1. Keep the Lean development correct and building. Do not change it casually now.
2. Fill in the packet files (§5) from facts I can verify in the repo.
3. Possible extensions (README §9 "Possible next steps") come only after that, and only when the
   human asks.

## 2. Hard rules (never break without explicit human approval)

1. **Never change a frozen statement** (`Statement.lean`, `Prop22/Statement.lean`) to make a
   proof go through. If a statement looks wrong, stop and report it (§6).
2. **Never use `axiom`.** Proposition 2.2 is proved (`prop22`). Any new result must also be
   proved, or taken as an explicit hypothesis.
3. **Never weaken the theorem silently.** This covers: adding hypotheses, changing $\ge$/$>$,
   changing the exponent, restricting $p,\delta$, or replacing $\mathcal I(H)$ with
   $\mathcal I(H_J)$ in a conclusion.
4. **Never claim a result is done** unless `lake build` succeeds and the file contains no
   `sorry`. After any change to Lean code, regenerate `logs/` (commands in `logs/README.md`)
   before claiming anything about axioms or `sorry`s.
5. **Never invent mathlib lemma names in final code.** Search first (`exact?`, `apply?`,
   `#check`, Loogle, grep the mathlib source). If I write a name from memory, I compile it
   before relying on it.
6. **Paper over README.** If the README's math and the paper disagree, the paper wins. Log the
   discrepancy in README §8.
7. **Record every divergence from the paper in [`divergence.md`](divergence.md)**
   (paper / Lean / why / effect / status). This covers extra hypotheses, representation
   choices, and choice rules. Required by the human (2026-09-29).
8. **Never fabricate packet facts.** I cannot see event dates, the competition cutoff,
   submission IDs, the evaluator report, or the judges' access. I leave those as
   `<!-- TODO (owner): … -->` until the human provides them. The same goes for compute figures
   (sessions, tokens, cost) that I cannot measure.
9. **Keep the packet consistent.** Theorem names, axiom output, versions, commit hashes and
   `sorry` counts must agree across `README.md`, `RESULTS.md`, `REPRODUCE.md`, `logs/` and
   `MOTIVATION.md`. When one changes, update all of them.
10. **Be honest about authorship.** Claude wrote the Lean code and the docs. The owner directed
    the work and approved the statements. Do not overstate either side's part. Commits I create
    carry the `Co-Authored-By` trailer.

## 3. Uncertainty protocol (required)

Whenever I am unsure about a step, I say so **explicitly and visibly**. I do not bury it. Use
this format in chat, as a Lean comment, or as a packet-document note:

```
⚠ UNSURE: <what> — <why> — <how to resolve: check paper p.?, test, ask>
```

Cases that always trigger it:

- a mathlib API whose name or signature I have not compiled at the pinned version;
- a proof step I believe but have not seen Lean accept;
- any design choice that deviates from README §7 "Decided" rows;
- a claim about prior work or related formalizations that I have not checked against a source;
- any packet claim that depends on information only the human has.

## 4. Session workflow

### 4.1 Packet work (current default)

1. **Orient.** Run `git status` and `git log -5`. Read `logs/README.md`. Check whether
   `HEAD` is still the commit the logs were recorded at.
2. **Pick a file** from §5 and fill only the sections I can verify. Leave the rest as TODO.
3. **Cite.** Each claim links to a file, a `file:line`, a log or a commit hash.
4. **Close out.** List what was filled, what is still TODO, and which TODOs need the human.

### 4.2 Lean work (only when asked)

1. **State before proving.** Write the lemma in paper notation in a comment, then its Lean
   statement, then `sorry`, then build. The statement must typecheck before any proof work
   starts.
2. **Small lemmas first.** Membership characterizations → `simp` lemmas → equivalences → main
   lemma. Target 5–30 lines per proof. If a proof grows past ~60 lines, extract lemmas.
3. **Build often.** `lake build CamposSamotij.<Folder>.<File>` after each lemma.
4. **Close out.** Run a full `lake build`, regenerate `logs/`, then update README §8 and §9 and
   the packet files (rule 9).

## 5. The submission packet

| File | Content | Who can fill it |
|---|---|---|
| `README.md` | Overview, statement, proof outline, status, provenance | Done |
| `divergence.md` | Every divergence from the paper | Done; keep current |
| `RESULTS.md` | Paper result ↔ Lean declaration ↔ file, axioms, `sorry`s, assumptions | Me, from the repo |
| `REPRODUCE.md` | Pinned versions, commands, expected output, CI | Me, from the repo |
| `logs/` | `build.log`, `axioms.log`, `Axioms.lean`, `sorry-check.log`, CI runs | Done; regenerate after Lean changes. Evaluator report: owner |
| `MOTIVATION.md` | Contribution, why it matters, what is reusable, prior work, what was done during the event, done vs. future | Me for the technical parts. Event facts: owner. Prior work: only after checking sources |
| `CREDITS.md` | Authors, AI use, compute, commit authorship | Me for AI/tooling facts. Compute and human roles: owner confirms |
| `SUBMISSION.md` | Summary, IDs, cutoff, evaluator report, access, packet index | Me for the index and access. IDs, cutoff, report, permission: owner |
| `paper/` | Links to the arXiv v2 PDF and LaTeX source, with citation and licence note | Done (no copies: arXiv licence) |

Known packet issues:

- The paper is linked from `paper/README.md` (arXiv v2), not redistributed. The old root copy
  `optimal_cello_paper.pdf` was removed on 2026-10-02; it remains in git history.
- Only the last three Lean commits carry the Claude `Co-Authored-By` trailer, although Claude
  wrote all the Lean code. `CREDITS.md` §4 says so.
- The Sunday 2026-09-27 commits count as event work (owner, 2026-10-02).
- Work after the competition cutoff must be labelled as post-cutoff.

## 6. When to stop and ask the human

- A frozen statement appears false or unprovable (give a counterexample if possible).
- The paper and README disagree and the choice changes a statement.
- A design decision needs to change or a new one needs to be made (README §7).
- I need a hypothesis the paper does not state (for example $V$ nonempty, $H$ without $\varnothing$).
- New work needs substantial new general infrastructure. Propose isolating it in its own file
  first.
- A packet claim needs information I cannot verify (rule 8).
- Anything outward-facing: pushing, changing repository visibility, contacting the judges.

## 7. Lean conventions for this project

- Namespace `CamposSamotij`. One file per milestone, grouped in subfolders (README §6 Layout).
- Variables: `{V : Type*} [Fintype V] [LinearOrder V]`. Never add `[DecidableEq V]` next to
  `[LinearOrder V]`, since that gives two instances. Files that need no order (`Hypergraph/`,
  `Probability/`, `Prop22/`) take `[DecidableEq V]` alone.
- Hypergraphs: `Finset (Finset V)`. Independence:
  `def IsIndep (H : Finset (Finset V)) (I : Finset V) : Prop := ∀ e ∈ H, ¬ e ⊆ I`.
- Link: `def link H v := (H.filter (v ∈ ·)).image (·.erase v)`, with update `H ∪ link H v`, and
  `@[simp] mem_link`.
- Probability: the `weight` / `probOn` / `condProb` / `condExp` API over `Finset` sums
  (`Probability/RandomSubset.lean`, Decided in README §7). Downstream proofs use only API lemmas
  and never unfold `probOn`.
- Keep `Algorithm/Defs.lean` free of probability *proofs*. It may *use* `condProb` in
  `eligible`, but the lemmas about it live elsewhere.
- Use `Classical` for decidability of `eligible`. Mark defs `noncomputable` as needed.
  "Deterministic" means "a function of `(H_i, S_i)`". It does not mean computable.
- Name results after the paper: `lemma41`, `lemma42`, `lemma43`, `prop22`, `theoremB`,
  `theoremB_unconditional`. Variants get suffixes (`lemma41_run`, `prop22_rpow`).
- Keep `decide`-checkable toy examples (3–4 vertices) in `Examples.lean`.

## 8. Known traps (from the formalization; still apply to any edit)

- **Eligibility must exclude singleton-edge vertices**, or `run` never stabilizes (README §4.2).
- **Conditional probability needs $P_i > 0$.** It follows from $\varnothing \in \mathcal I(H_i)$
  and $p<1$, and is proved as a lemma, not assumed.
- **Strictness.** $C' = \varnothing$ makes strict inequalities false. Theorem B(c) uses $\ge$.
- **Coupling identity (Lemma 4.3)** is a finite-sum factorization over
  $V = S \sqcup C' \sqcup (V\setminus C)$, not measure theory.
- **Real exponents.** $(1-p)^{\delta|C'|}$ uses `Real.rpow`, so it needs $0<1-p$.
- **Replay lemma.** `run H I = run H (run H I).S`, proved by induction on the iteration count.
- **Logs depend on the build.** A cached `lake build` takes seconds and proves nothing new. For
  `logs/build.log`, delete `.lake/build` first.

## 9. Tone of reports to the human

Short, factual, and in this order: **done / in progress (`sorry` count or TODO count) /
⚠ UNSURE items / questions needing a decision.** Do not overstate progress. "Compiles with 3
sorries" and "RESULTS.md filled; 4 TODOs need the owner" are precise and acceptable reports.
