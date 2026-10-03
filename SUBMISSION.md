# Submission

**In one line.** Theorem B of Campos–Samotij, *Towards an Optimal Hypergraph Container Lemma*
(Combinatorica **46** (2026), Art. 24), the hard-core container lemma, is fully formalized in
Lean 4 / mathlib with no hypotheses (`theoremB_unconditional`). Proposition 2.2 and Lemmas 4.1–4.3
are formalized along the way. The library has no `sorry` and no project axiom. Details:
[`RESULTS.md`](RESULTS.md).

## 1. Identifiers

| | |
|---|---|
| Repository | <https://github.com/lazyluca/hyprgraph_containers> |
| Formalization finished at | `816f7e31a9edec91db5be9a218fd29406fbaa1e3` (2026-09-29 16:46 −03:00) |
| Competition | Openmath |
| Entrant / team | Leanification |
| Date submitted | 2026-10-02 |

## 2. Cutoff

**Official cutoff: end of Friday 2026-10-02 (midnight).**

All commits, with dates (from `git log`):

| Commits | Date | What |
|---|---|---|
| `c5df8e8`, `eb4be58` | Sunday 2026-09-27 | Setup and infrastructure (counts as event work; see [`MOTIVATION.md`](MOTIVATION.md) §5) |
| `f9973c5` … `816f7e3` | Tuesday 2026-09-29 | Statements, Lemmas 4.1–4.3, Proposition 2.2, Theorem B |
| `669d14f` and later | Friday 2026-10-02 | Submission packet only; no Lean code changed |

Every commit up to and including `669d14f` (2026-10-02 16:28 −03:00) is before the cutoff. Any
commit made after midnight at the end of 2026-10-02 is post-cutoff and will be labelled as such
here.

The commit that adds Matheus and Tiago as statement reviewers to [`CREDITS.md`](CREDITS.md) was
made on 2026-10-02 after 22:00 −03:00, which is after 01:00 UTC on 2026-10-03. It changes credits
only. It is before the cutoff if the cutoff is midnight in −03:00, and after it if the cutoff is
midnight UTC.

## 3. Evaluator report

See [`logs/`](logs/README.md). It has the clean build ([`build.log`](logs/build.log)), the axiom
check ([`axioms.log`](logs/axioms.log)) and the `sorry` search
([`sorry-check.log`](logs/sorry-check.log)), recorded at `816f7e3`.

## 4. Access

The repository is public (checked with `gh repo view` on 2026-10-02):
<https://github.com/lazyluca/hyprgraph_containers>. Anyone, including both judges, can clone and
build it without being granted access. [`REPRODUCE.md`](REPRODUCE.md) has the commands. I grant both judges full permission to review this repository.

## 5. Packet contents

**Start here**

| File | What it contains |
|---|---|
| [`RESULTS.md`](RESULTS.md) | Paper result ↔ Lean declaration ↔ `file:line`; statements side by side; axiom output; `sorry` check; assumptions and divergences; what is *not* formalized |
| [`REPRODUCE.md`](REPRODUCE.md) | Pinned Lean/mathlib versions, commands to build and check, expected output, CI |
| [`MOTIVATION.md`](MOTIVATION.md) | Contribution, why it matters, what is reusable, prior work, what was done during the event, completed vs. future work |
| [`CREDITS.md`](CREDITS.md) | Authors and roles, AI use (models, which files), compute, commit authorship |
| [`divergence.md`](divergence.md) | Every difference from the paper: paper / Lean / why / effect / status |
| [`README.md`](README.md) | Project overview, proof outline, design decisions, provenance |

**Evidence**

| File | What it contains |
|---|---|
| [`logs/`](logs/README.md) | `build.log` (clean build), `axioms.log` + `Axioms.lean`, `sorry-check.log`; recorded at `816f7e3` |
| [`paper/`](paper/README.md) | Citation and links to the arXiv v2 PDF and LaTeX source |
| [`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) | CI: builds every push and pull request |

**Lean code** (`CamposSamotij.lean` and `CamposSamotij/`: 14 files, 1695 lines)

| File | Contents |
|---|---|
| [`Statement.lean`](CamposSamotij/Statement.lean) | `TheoremBStatement`, frozen |
| [`Prop22/Statement.lean`](CamposSamotij/Prop22/Statement.lean) | `Prop22Statement`, frozen; `prop22_rpow` |
| [`TheoremB.lean`](CamposSamotij/TheoremB.lean) | Replay lemma, `theoremB`, `theoremB_unconditional` |
| [`Prop22/Proof/Induction.lean`](CamposSamotij/Prop22/Proof/Induction.lean) | `prop22` |
| [`Section4/Lemma41.lean`](CamposSamotij/Section4/Lemma41.lean), [`Lemma42.lean`](CamposSamotij/Section4/Lemma42.lean), [`Lemma43.lean`](CamposSamotij/Section4/Lemma43.lean) | Lemmas 4.1–4.3 |
| [`Algorithm/Defs.lean`](CamposSamotij/Algorithm/Defs.lean) | The container algorithm of §4.1 and its termination |
| [`Hypergraph/Basic.lean`](CamposSamotij/Hypergraph/Basic.lean), [`Updates.lean`](CamposSamotij/Hypergraph/Updates.lean) | Hypergraphs, independence, link |
| [`Probability/RandomSubset.lean`](CamposSamotij/Probability/RandomSubset.lean), [`RealAux.lean`](CamposSamotij/Probability/RealAux.lean) | Finite-sum random-subset probability API; real inequalities |
| [`Examples.lean`](CamposSamotij/Examples.lean) | `decide`-checked toy examples |

Build configuration: [`lean-toolchain`](lean-toolchain), [`lakefile.lean`](lakefile.lean),
[`lake-manifest.json`](lake-manifest.json). Licence: [`LICENSE`](LICENSE). AI working rules:
[`CLAUDE.md`](CLAUDE.md).

## 6. Certificates

There are no separate certificates. Every proof is checked by Lean's kernel: see
[`logs/build.log`](logs/build.log) and the `#print axioms` output in
[`logs/axioms.log`](logs/axioms.log).
