# Reproducing the build

This file explains how to check, from a clean machine, that the Lean development builds, contains
no `sorry`, and uses only Lean's standard axioms. Every expected output below was recorded in
[`logs/`](logs/) at commit `816f7e31a9edec91db5be9a218fd29406fbaa1e3`.

## 1. Pinned versions

| Component | Version | Source |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.1` | [`lean-toolchain`](lean-toolchain) |
| Lake | `5.0.0` (ships with Lean 4.34.1) | `lake --version` |
| mathlib | tag `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` | [`lakefile.lean`](lakefile.lean), [`lake-manifest.json`](lake-manifest.json) |
| Transitive deps (plausible, LeanSearchClient, import-graph, ProofWidgets4, aesop, …) | pinned by commit | [`lake-manifest.json`](lake-manifest.json) |
| elan (toolchain manager) | any recent version; logs used `4.2.1` | <https://github.com/leanprover/elan> |

`lake-manifest.json` is committed, so `lake` fetches exactly these commits. You do not need to
install Lean yourself: elan reads `lean-toolchain` and downloads the right version.

**Machines it has been built on:**

- Local (the logs): Linux 7.2.7 (Arch), 8 cores, 7 GB RAM.
- CI: GitHub Actions `ubuntu-latest` (§4).

macOS and Windows have not been tested.

## 2. Commands

Prerequisites: `git`, `curl`, and about 5 GB of free disk space for the prebuilt mathlib cache.

```sh
# 0. Install elan (skip if `elan --version` already works)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env

# 1. Get the code at the recorded commit
git clone https://github.com/lazyluca/hyprgraph_containers.git
cd hyprgraph_containers
git checkout 816f7e31a9edec91db5be9a218fd29406fbaa1e3   # or a later commit; see note below

# 2. Download prebuilt mathlib (otherwise mathlib builds from source, which takes hours)
lake exe cache get

# 3. Build the project from scratch
rm -rf .lake/build
lake build

# 4. Axiom check for the main theorems
lake env lean logs/Axioms.lean

# 5. Search the project sources for sorry / admit / axiom
grep -rnwE "sorry|admit|axiom" CamposSamotij --include=*.lean
```

To regenerate the files in `logs/` instead of printing to the terminal, use the redirecting
versions in [`logs/README.md`](logs/README.md#commands).

Note on commits: the logs were recorded at `816f7e3`. Commits after it change only the packet
documents, not Lean code. You can confirm this with
`git diff --stat 816f7e3 HEAD -- CamposSamotij CamposSamotij.lean lakefile.lean lake-manifest.json lean-toolchain`.

## 3. Expected output

**Step 3, `lake build`.** It ends with:

```text
Build completed successfully (2074 jobs).
```

It exits with status 0, with no errors and no `declaration uses 'sorry'` warnings. Full log:
[`logs/build.log`](logs/build.log). With mathlib taken from the cache, this took about 16 s of wall
time locally and about 29 s on CI. Downloading the mathlib cache in step 2 took about 2.5 min on
CI.

**Step 4, axiom check.** The output is exactly this (also in [`logs/axioms.log`](logs/axioms.log)):

```text
'CamposSamotij.theoremB_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.prop22' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.lemma41' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.lemma42' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.lemma43' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. **This is the decisive check.** If any proof these
theorems depend on contained a `sorry`, `sorryAx` would show up in this list. If the project had
declared an axiom, its name would show up too.

**Step 5, text search.** There is exactly one match, and it is in a doc comment, not in code
(see [`logs/sorry-check.log`](logs/sorry-check.log)):

```text
CamposSamotij/Prop22/Statement.lean:8:Never an `axiom`. **Frozen** (approved 2026-09-29; see `divergence.md` D1, D2).
```

## 4. CI

[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) runs
[`leanprover/lean-action@v1`](https://github.com/leanprover/lean-action) on `ubuntu-latest`. It is
triggered by every push (on any branch), every pull request, and manual dispatch. The run log of
36621581715 shows what the action does:

1. installs elan and the toolchain from `lean-toolchain`;
2. runs `lake exe cache get` (mathlib detected);
3. runs `lake build`, which ends with `Build completed successfully (2074 jobs).`;
4. skips `lake test` and `lake lint`, because the project defines neither (`lake check-test failed`,
   `lake check-lint failed` in the log).

**What CI does not check:** it does not run the axiom check (§3 step 4) or the `sorry` search
(§3 step 5). A `sorry` in the code would only produce a warning, so the build would still pass. CI
therefore shows that the project compiles from a fresh checkout. That the proofs are complete is
shown by `logs/axioms.log`, or by running step 4 yourself.

Recent runs, all `success`, all on `main` (from `gh run list`):

| Run ID | Commit | Created (UTC) |
|---|---|---|
| [36621581715](https://github.com/lazyluca/hyprgraph_containers/actions/runs/36621581715) | `816f7e3` README rewrite | 2026-09-29 19:46 |
| [36616483355](https://github.com/lazyluca/hyprgraph_containers/actions/runs/36616483355) | `839efdb` finish formalization (Theorem B) | 2026-09-29 19:03 |
| [36615913236](https://github.com/lazyluca/hyprgraph_containers/actions/runs/36615913236) | `94c5af9` replay lemma and assembly | 2026-09-29 18:58 |
| [36579018563](https://github.com/lazyluca/hyprgraph_containers/actions/runs/36579018563) | `2bb6320` Lemmas 4.2 and 4.3 | 2026-09-29 13:57 |
| [36574441187](https://github.com/lazyluca/hyprgraph_containers/actions/runs/36574441187) | `62e3c34` Lemma 4.1 (message says 4.2) | 2026-09-29 13:21 |

All runs: <https://github.com/lazyluca/hyprgraph_containers/actions>
