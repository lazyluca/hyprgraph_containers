# Logs

Raw outputs from checking this repository, so the claims in the top-level README can be verified
without rebuilding. To regenerate them, run the commands below from the repository root.

**Recorded:** 2026-10-02T16:51Z, at commit `816f7e31a9edec91db5be9a218fd29406fbaa1e3`, on Linux
7.2.7 (Arch). Lean `v4.34.1`, Lake `5.0.0`, mathlib `v4.34.1`
(commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, from `lake-manifest.json`).

| File | What it is | Result |
|---|---|---|
| [`build.log`](build.log) | Full `lake build` of the project, after deleting `.lake/build` (mathlib from the prebuilt cache) | Exit 0, `Build completed successfully (2074 jobs)`, no warnings or errors, about 16 s wall time |
| [`axioms.log`](axioms.log) | `#print axioms` for the main theorems | Only `propext`, `Classical.choice`, `Quot.sound` |
| [`Axioms.lean`](Axioms.lean) | The script that produced `axioms.log` | |
| [`sorry-check.log`](sorry-check.log) | Search for `sorry`, `admit` and `axiom` in all project Lean files | One match, in a doc comment (`Prop22/Statement.lean:8`, "Never an `axiom`"). No `sorry`, `admit` or `axiom` in code. |

## Commands

```sh
lake exe cache get                                   # prebuilt mathlib
rm -rf .lake/build && lake build > logs/build.log 2>&1
lake env lean logs/Axioms.lean > logs/axioms.log 2>&1
grep -rnwE "sorry|admit|axiom" CamposSamotij --include=*.lean > logs/sorry-check.log
```

## Axiom output

```text
'CamposSamotij.theoremB_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.prop22' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.lemma41' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.lemma42' depends on axioms: [propext, Classical.choice, Quot.sound]
'CamposSamotij.lemma43' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are Lean's standard axioms, which mathlib uses throughout. No project-specific axiom
is used.

## Continuous integration

GitHub Actions (`.github/workflows/lean_action_ci.yml`) builds every push (any branch), every pull request, and manual dispatch. The last
three runs all passed:

| Run ID | Commit | Date (UTC) | Result |
|---|---|---|---|
| 36621581715 | `816f7e3` README rewrite | 2026-09-29 19:46 | success (4m14s) |
| 36616483355 | `839efdb` finish formalization (Theorem B) | 2026-09-29 19:03 | success (4m13s) |
| 36615913236 | `94c5af9` replay lemma and assembly | 2026-09-29 18:58 | success (4m23s) |

Runs: <https://github.com/lazyluca/hyprgraph_containers/actions>

