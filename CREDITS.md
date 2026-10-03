# Credits and AI disclosure

## 1. Authors and roles

**The mathematics.** Marcelo Campos and Wojciech Samotij, *Towards an Optimal Hypergraph
Container Lemma*, Combinatorica **46** (2026), no. 3, Article 24
([doi:10.1007/s00493-026-00214-1](https://doi.org/10.1007/s00493-026-00214-1);
[arXiv:2408.06617](https://arxiv.org/abs/2408.06617)). Every theorem formalized here is theirs.
The one exception is the proof route for Proposition 2.2 (see [`divergence.md`](divergence.md)
D12).

**Repository owner: Luca (GitHub `lazyluca`).** The owner (the first four items are recorded in
[`README.md`](README.md), Authorship note and §10):

- chose the target (Theorem B) and the scope;
- wrote the working rules for the AI ([`CLAUDE.md`](CLAUDE.md)), with assistance from ChatGPT
  (free version);
- made the design decisions (README §7);
- reviewed against the paper, and approved, the two frozen statements (`TheoremBStatement`,
  `Prop22Statement`) and every entry in [`divergence.md`](divergence.md) before anything relied on
  it (approvals dated 2026-09-29);
- wrote [`MOTIVATION.md`](MOTIVATION.md), with assistance from Claude (stated by the owner,
  2026-10-02);
- co-wrote [`RESULTS.md`](RESULTS.md) and this file with Claude.

**Statement reviewers: Matheus and Tiago.** They also checked the formal statement of Theorem B
(`TheoremBStatement`, [`Statement.lean`](CamposSamotij/Statement.lean)) against the paper (stated
by the owner, 2026-10-02).

**Claude (Anthropic), the AI model, working in Claude Code.** Wrote the Lean code and most of the
documentation (§2).

## 2. AI use

**Tool.** [Claude Code](https://claude.com/claude-code), Anthropic's coding agent, run in
VS Code on the owner's machine. Each session followed the rules in
[`CLAUDE.md`](CLAUDE.md): no `axiom`; never change a frozen statement to make a proof go through;
the paper wins over the README; log every divergence; flag any uncertainty in writing.

**Model.** Claude Opus 5.5 (`claude-opus-5-5`) in every Claude Code session (stated by the owner,
2026-10-02). It is also the model named in the `Co-Authored-By` trailers of `94c5af9`, `839efdb`
and `816f7e3`. The earlier commits do not record a model.

**Other AI.** The owner used ChatGPT (free version, OpenAI) to help write [`CLAUDE.md`](CLAUDE.md).

**What the AI wrote.**

| Artifact | Written by |
|---|---|
| All Lean code: `CamposSamotij.lean` and `CamposSamotij/**/*.lean` (1695 lines in 14 files) | Claude |
| [`README.md`](README.md), [`divergence.md`](divergence.md) | Claude; divergence *approvals* by the owner |
| [`RESULTS.md`](RESULTS.md), this file | Claude and the owner together; Claude drafted from facts in the repository, and the owner contributed to the text |
| [`SUBMISSION.md`](SUBMISSION.md) | Claude, at the owner's request; identifiers, cutoff, evaluator report and review permission come from the owner |
| [`REPRODUCE.md`](REPRODUCE.md), [`logs/README.md`](logs/README.md) | Claude, from facts in the repository |
| [`logs/`](logs/) outputs | Produced by running `lake`, `lean` and `grep` (commands in `logs/README.md`) |
| [`MOTIVATION.md`](MOTIVATION.md) | The owner, with assistance from Claude |
| [`CLAUDE.md`](CLAUDE.md) | The owner, with assistance from ChatGPT (free version) |

**How the output was checked.**

- **Proofs:** checked by Lean's kernel. `#print axioms` on the main theorems shows only
  `propext`, `Classical.choice` and `Quot.sound` ([`logs/axioms.log`](logs/axioms.log)), so the
  proofs do not depend on trusting the AI.
- **Statements:** *not* machine-checked. The owner read `TheoremBStatement` and `Prop22Statement`
  against the paper and approved them. Matheus and Tiago also checked `TheoremBStatement`. See [`RESULTS.md`](RESULTS.md) §1.2 and §4.
- **Mathlib names:** compiled at the pinned version, never taken on trust (`CLAUDE.md` rule 5).
  The build succeeds ([`logs/build.log`](logs/build.log)).

## 3. Compute

**Builds.** Local: Linux 7.2.7 (Arch), 8 cores, 7 GB RAM. With mathlib taken from the prebuilt
cache, a full project build takes about 16 s ([`logs/build.log`](logs/build.log)). CI: GitHub
Actions `ubuntu-latest`, about 4 min per run, including the mathlib cache download
([`REPRODUCE.md`](REPRODUCE.md) §4). No mathlib was built from source.

**AI usage.** 10 Claude Code sessions, about 23 million tokens in total (stated by the owner,
2026-10-02; not measurable from the repository).

## 4. Note on commit authorship

All commits on `main` are authored by the owner's account (`lazyluca`; the initial commit as
`Luca`). Claude has no account of its own, so its code was committed from the owner's account.

Of the 9 commits up to `816f7e3` (the formalization), only the last three carry a `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
trailer:

| Commit | Date | Message | Content | Trailer |
|---|---|---|---|---|
| `c5df8e8` | 2026-09-27 | Initial commit | `LICENSE` only | — |
| `eb4be58` | 2026-09-27 | definitions and auxiliary results… | Lean infrastructure, README, pins, paper | **missing** |
| `f9973c5` | 2026-09-29 | add divergence and formaliazation of the stament | Algorithm, Prop. 2.2 statement, `divergence.md` | **missing** |
| `4035e29` | 2026-09-29 | formalized the statement of the theorem | `TheoremBStatement` | **missing** |
| `62e3c34` | 2026-09-29 | formalized lemma 4.2 | Lemma 4.1 (despite the message) | **missing** |
| `2bb6320` | 2026-09-29 | formalized lemma 4.2 and 4.3 | Lemmas 4.2, 4.3 | **missing** |
| `94c5af9` | 2026-09-29 | formalized theorem B (replay lemma and assembly) | Theorem B | yes |
| `839efdb` | 2026-09-29 | finish formalization… (Theorem B) | Prop. 2.2, `theoremB_unconditional` | yes |
| `816f7e3` | 2026-09-29 | rewrite README… | README | yes |

**The missing trailers do not mean a human wrote those commits.** Claude wrote the Lean code in
all of them. Git history was not rewritten to add the trailers. Later commits that Claude creates, starting with
the one that added this packet, carry the trailer (`CLAUDE.md` rule 10).
