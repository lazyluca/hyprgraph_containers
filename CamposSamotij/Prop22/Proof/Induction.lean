import CamposSamotij.Prop22.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Proposition 2.2: an elementary proof (M9)

A proof of `Prop22Statement` by induction on `|C|`. It is the paper's *first proof*
(Appendix A: chain rule for relative entropy plus convexity of `i_p`) unrolled one coordinate
at a time, so that only finite sums and one-variable facts about `log` are needed.
See `divergence.md` D12.

## The argument

Write `P(E) := P(E(X_p))`, `M(E) := ∑_{A ⊆ X, E A} P(X_p = A)·|A|` (so `E[|X_p| | E] = M/P`),
`n := |X|` and `ℓ := log(1 - p) < 0`. For every down-closed `E` (possibly empty) we show

  `ℓ · (n·P - M/p) ≤ P · log P`.                                                   (∗)

Dividing by `P > 0` gives Proposition 2.2.

*Base* `X = ∅`: both sides are `0`.

*Step* `X = Y ⊔ {v}`: let `E₀ := E` and `E₁ := E(· ∪ {v})` on `Y`, with `a := P(E₀)`,
`b := P(E₁)`. Down-closure gives `E₁ ⊆ E₀`, so `b ≤ a`, and
`P = (1-p)a + pb`, `M = (1-p)M₀ + p(M₁ + b)`. Applying (∗) to `E₀`, `E₁` on `Y`,
the left side of (∗) for `X` is at most
`(1-p)·a log a + p·b log b + (1-p)(a - b)·log(1-p)`,
which is at most `P log P` by `two_point`:

  `(1-p)a log a + pb log b + (1-p)(a-b) log(1-p)`
  ` = (1-p)(a-b)·log((1-p)a) + b·((1-p) log a + p log b)`
  ` ≤ (1-p)(a-b)·log P + b·log P = P log P`,

using `(1-p)a ≤ P` and concavity of `log`.

## Results

* `two_point`: the one-step inequality above.
* `moment`, `probOn_insert`, `moment_insert`: `P` and `M` split over `X = Y ⊔ {v}`.
* `prop22_unnormalized`: (∗).
* `prop22`: `Prop22Statement` holds, so the hypothesis of `theoremB` is discharged.
-/

namespace CamposSamotij

universe u

/-! ### The one-step inequality -/

/-- For `0 < p < 1` and `0 ≤ b ≤ a`:
`(1-p)a log a + pb log b + (1-p)(a-b) log(1-p) ≤ P log P`, with `P = (1-p)a + pb`. -/
theorem two_point {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hb : 0 ≤ b) (hba : b ≤ a) :
    (1 - p) * (a * Real.log a) + p * (b * Real.log b) + (1 - p) * (a - b) * Real.log (1 - p) ≤
      ((1 - p) * a + p * b) * Real.log ((1 - p) * a + p * b) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  rcases (hb.trans hba).eq_or_lt with ha | ha
  · -- `a = 0`, hence `b = 0`
    obtain rfl : b = 0 := le_antisymm (ha ▸ hba) hb
    subst ha; simp
  set P := (1 - p) * a + p * b with hP
  have hqa : 0 < (1 - p) * a := mul_pos hq ha
  have hqaP : (1 - p) * a ≤ P := le_add_of_nonneg_right (mul_nonneg hp0.le hb)
  -- first part: `log((1-p)a) ≤ log P`
  have h1 : (1 - p) * (a - b) * Real.log ((1 - p) * a) ≤ (1 - p) * (a - b) * Real.log P :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hqa hqaP)
      (mul_nonneg hq.le (sub_nonneg.mpr hba))
  -- second part: `(1-p) log a + p log b ≤ log P`
  have h2 : b * ((1 - p) * Real.log a + p * Real.log b) ≤ b * Real.log P := by
    rcases hb.eq_or_lt with rfl | hb'
    · simp
    refine mul_le_mul_of_nonneg_left ?_ hb
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb')
      hq.le hp0.le (by ring)
    simpa [smul_eq_mul] using this
  have key : (1 - p) * (a * Real.log a) + p * (b * Real.log b) +
      (1 - p) * (a - b) * Real.log (1 - p) =
      (1 - p) * (a - b) * Real.log ((1 - p) * a) +
        b * ((1 - p) * Real.log a + p * Real.log b) := by
    rw [Real.log_mul hq.ne' ha.ne']; ring
  rw [key]
  calc _ ≤ (1 - p) * (a - b) * Real.log P + b * Real.log P := add_le_add h1 h2
    _ = P * Real.log P := by rw [hP]; ring

/-! ### Splitting `P` and `M` over `X = Y ⊔ {v}` -/

variable {V : Type*} [DecidableEq V] {p : ℝ}

/-- `M(E) = ∑_{A ⊆ X, E A} P(X_p = A)·|A|`, so that `E[|X_p| | E] = M(E) / P(E)`. -/
def moment (X : Finset V) (p : ℝ) (E : Finset V → Prop) [DecidablePred E] : ℝ :=
  ∑ A ∈ X.powerset with E A, weight p X A * A.card

omit [DecidableEq V] in
theorem condExp_card_eq (X : Finset V) (p : ℝ) (E : Finset V → Prop) [DecidablePred E]
    [DecidableEq V] : condExp X p (fun A ↦ (A.card : ℝ)) E = moment X p E / probOn X p E :=
  rfl

/-- `P(E) = (1-p)·P(E₀) + p·P(E₁)` for `X = Y ⊔ {v}`. -/
theorem probOn_insert {v : V} {Y : Finset V} (hv : v ∉ Y) (E : Finset V → Prop)
    [DecidablePred E] :
    probOn (insert v Y) p E =
      (1 - p) * probOn Y p E + p * probOn Y p (fun B ↦ E (insert v B)) := by
  rw [probOn_split v, probOn_insert_mem hv, probOn_insert_notMem hv, add_comm]

/-- `M(E) = (1-p)·M(E₀) + p·(M(E₁) + P(E₁))` for `X = Y ⊔ {v}`. -/
theorem moment_insert {v : V} {Y : Finset V} (hv : v ∉ Y) (E : Finset V → Prop)
    [DecidablePred E] :
    moment (insert v Y) p E =
      (1 - p) * moment Y p E +
        p * (moment Y p (fun B ↦ E (insert v B)) + probOn Y p (fun B ↦ E (insert v B))) := by
  simp only [moment, probOn, Finset.sum_filter]
  rw [Finset.sum_powerset_insert hv]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    rw [weight_insert_of_notMem hv (Finset.mem_powerset.mp hA)]
    split_ifs <;> ring
  · rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB ↦ ?_
    have hB := Finset.mem_powerset.mp hB
    rw [weight_insert_insert hv hB, Finset.card_insert_of_notMem fun h ↦ hv (hB h)]
    split_ifs <;> push_cast <;> ring

/-! ### The induction -/

/-- (∗): for a down-closed event `E` on `X` (possibly empty) and `p ∈ (0, 1)`,
`log(1-p)·(|X|·P(E) - M(E)/p) ≤ P(E)·log P(E)`. -/
theorem prop22_unnormalized (hp0 : 0 < p) (hp1 : p < 1) (X : Finset V) (E : Finset V → Prop)
    [hE : DecidablePred E] (hdown : ∀ A B, B ⊆ A → E A → E B) :
    Real.log (1 - p) * (X.card * probOn X p E - moment X p E / p) ≤
      probOn X p E * Real.log (probOn X p E) := by
  induction X using Finset.induction_on generalizing E hE with
  | empty => by_cases h : E ∅ <;> simp [probOn, moment, Finset.sum_filter, weight, h]
  | @insert v Y hv ih =>
    set E₁ : Finset V → Prop := fun B ↦ E (insert v B)
    have ih₀ := ih E hdown
    have ih₁ := ih E₁ fun A B hBA h ↦ hdown _ _ (Finset.insert_subset_insert v hBA) h
    have hba : probOn Y p E₁ ≤ probOn Y p E :=
      probOn_mono hp0.le hp1.le fun A _ h ↦ hdown _ _ (Finset.subset_insert v A) h
    have hb : 0 ≤ probOn Y p E₁ := probOn_nonneg hp0.le hp1.le _ _
    have htwo := two_point hp0 hp1 hb hba
    rw [probOn_insert hv, moment_insert hv, Finset.card_insert_of_notMem hv]
    calc _ = (1 - p) * (Real.log (1 - p) * (Y.card * probOn Y p E - moment Y p E / p)) +
          p * (Real.log (1 - p) * (Y.card * probOn Y p E₁ - moment Y p E₁ / p)) +
          (1 - p) * (probOn Y p E - probOn Y p E₁) * Real.log (1 - p) := by
          field_simp; push_cast; ring
      _ ≤ (1 - p) * (probOn Y p E * Real.log (probOn Y p E)) +
          p * (probOn Y p E₁ * Real.log (probOn Y p E₁)) +
          (1 - p) * (probOn Y p E - probOn Y p E₁) * Real.log (1 - p) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left ih₀ (sub_pos.mpr hp1).le)
          (mul_le_mul_of_nonneg_left ih₁ hp0.le)) le_rfl
      _ ≤ _ := htwo

/-- **Proposition 2.2** (Campos–Samotij), proved: the hypothesis `hProp22` of `theoremB`
holds. -/
theorem prop22 : Prop22Statement.{u} := by
  intro V _ C 𝓘 p hp0 hp1 hdown _ hne
  have hP : 0 < probOn C p (· ∈ 𝓘) := probOn_pos_of_isLowerSet hp0.le hp1 hdown hne
  have h := prop22_unnormalized hp0 hp1 C (· ∈ 𝓘) fun A B hBA hA ↦ hdown hBA hA
  rw [condExp_card_eq]
  calc _ = Real.log (1 - p) * (C.card * probOn C p (· ∈ 𝓘) - moment C p (· ∈ 𝓘) / p) /
        probOn C p (· ∈ 𝓘) := by field_simp
    _ ≤ Real.log (probOn C p (· ∈ 𝓘)) := by
      rw [div_le_iff₀ hP]; linarith

end CamposSamotij
