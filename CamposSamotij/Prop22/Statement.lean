import CamposSamotij.Probability.RandomSubset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 2.2: statement only (M7)

`Prop22Statement : Prop`, used only as the hypothesis `hProp22`.
Never an `axiom`. **Frozen** (approved 2026-09-29; see `divergence.md` D1, D2).
A proof, if any, goes in `Prop22/Proof/` (M9).

## The paper's statement (p. 5)

> **Proposition 2.2.** Suppose that `C` is a finite set and let `𝓘 ⊆ 2^C` be a decreasing
> family of subsets. For every `p ∈ (0, 1)`, we have
> `log P(C_p ∈ 𝓘) ≥ (|C| - E[|C_p| | C_p ∈ 𝓘] / p) · log(1 - p)`.

## Formalization

* `C : Finset V` over an arbitrary type `V` with `DecidableEq`, so that the statement can
  be applied directly to `C' ⊆ V` in Lemma 4.3.
* "decreasing" is `IsLowerSet (𝓘 : Set (Finset V))`, and `𝓘 ⊆ 2^C` is `𝓘 ⊆ C.powerset`.
* `P` and `E[· | ·]` are `probOn` and `condExp` from `RandomSubset.lean`.
* We add the hypothesis `𝓘.Nonempty`, which the paper leaves implicit (for `𝓘 = ∅` the
  left side is `log 0`). Adding a hypothesis to an *assumed* statement only weakens what we
  assume, so this is safe.

The added `𝓘.Nonempty` is divergence D1 in `divergence.md` (approved 2026-09-29).

## Results

* `prop22_rpow`: the exponentiated form `P(C_p ∈ 𝓘) ≥ (1-p)^(|C| - E[|C_p| | C_p ∈ 𝓘]/p)`
  (README §5), which is what Lemma 4.3 uses.
-/

namespace CamposSamotij

universe u

/-- **Proposition 2.2** (Campos–Samotij), for vertex types in universe `u`.
For finite `C`, a nonempty decreasing family `𝓘 ⊆ 2^C` and `p ∈ (0, 1)`:
`log P(C_p ∈ 𝓘) ≥ (|C| - E[|C_p| | C_p ∈ 𝓘] / p) · log(1 - p)`. -/
def Prop22Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (C : Finset V) (𝓘 : Finset (Finset V)) (p : ℝ),
    0 < p → p < 1 →
    IsLowerSet (𝓘 : Set (Finset V)) → 𝓘 ⊆ C.powerset → 𝓘.Nonempty →
    ((C.card : ℝ) - condExp C p (fun A ↦ (A.card : ℝ)) (· ∈ 𝓘) / p) * Real.log (1 - p) ≤
      Real.log (probOn C p (· ∈ 𝓘))

/-- Proposition 2.2 after exponentiating (README §5):
`P(C_p ∈ 𝓘) ≥ (1 - p)^(|C| - E[|C_p| | C_p ∈ 𝓘] / p)`. -/
theorem prop22_rpow (hProp22 : Prop22Statement.{u}) {V : Type u} [DecidableEq V]
    {C : Finset V} {𝓘 : Finset (Finset V)} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hdown : IsLowerSet (𝓘 : Set (Finset V))) (hsub : 𝓘 ⊆ C.powerset) (hne : 𝓘.Nonempty) :
    (1 - p) ^ ((C.card : ℝ) - condExp C p (fun A ↦ (A.card : ℝ)) (· ∈ 𝓘) / p) ≤
      probOn C p (· ∈ 𝓘) := by
  have hP : 0 < probOn C p (· ∈ 𝓘) := probOn_pos_of_isLowerSet hp0.le hp1 hdown hne
  rw [Real.rpow_def_of_pos (sub_pos.mpr hp1), ← Real.exp_log hP, Real.exp_le_exp, mul_comm]
  exact hProp22 C 𝓘 p hp0 hp1 hdown hsub hne

end CamposSamotij
