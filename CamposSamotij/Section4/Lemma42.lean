import CamposSamotij.Section4.Lemma41
import CamposSamotij.Probability.RealAux

/-!
# Lemma 4.2: fingerprint size (M6)

See README §4.4; paper, Section 4 (p. 12–13).

> **Lemma 4.2.** We have `δ|S| ≤ p|V|`.

Proof (paper): `Pᵢ := P(V_p ∈ 𝓘(Hᵢ))` satisfies `Pᵢ₊₁ ≤ (1 - δ)^{[vᵢ ∈ I]} Pᵢ`, so
`(1 - p)^|V| = P(V_p = ∅) ≤ P_J ≤ (1 - δ)^|S| P₀ ≤ (1 - δ)^|S|`, and then
`delta_mul_le_of_pow_le`.

## Definitions

* `probIndep p H`: `P(V_p ∈ 𝓘(H))`.

## Results

* `probOn_insert_eq_erase`: an event of `A ∪ {v}` does not see `v ∈ A`.
* `mul_probIndep_union_link`: `p · P(V_p ∈ 𝓘(H ∪ ∂_v H)) = P(v ∈ V_p ∈ 𝓘(H))`.
* `probIndep_pos`: `Pᵢ > 0` (from `I ∈ 𝓘(Hᵢ)`, so `∅ ∈ 𝓘(Hᵢ)`).
* `probIndep_step_le`: `Pᵢ ≤ (1-δ)^|Sᵢ| → Pᵢ₊₁ ≤ (1-δ)^|Sᵢ₊₁|`.
* `probIndep_stage_le`: `Pᵢ ≤ (1 - δ)^|Sᵢ|` for every `i`.
* `lemma42`: `δ|S| ≤ p|V|`.
-/

namespace CamposSamotij

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- `P(V_p ∈ 𝓘(H))`, with `V_p` the `p`-random subset of the whole vertex set. -/
noncomputable def probIndep (p : ℝ) (H : Hypergraph V) : ℝ :=
  probOn Finset.univ p (IsIndep H)

variable {p δ : ℝ} {H : Hypergraph V} {I : Finset V} {st : State V} {v : V}

omit [Fintype V] in
/-- For `v ∈ X`, the event `E(X_p ∪ {v})` has the law of `E((X \ {v})_p ∪ {v})`. -/
theorem probOn_insert_eq_erase {X : Finset V} (hv : v ∈ X) (E : Finset V → Prop)
    [DecidablePred E] :
    probOn X p (fun A ↦ E (insert v A)) = probOn (X.erase v) p (fun B ↦ E (insert v B)) := by
  rw [probOn_split v, probOn_mem_and hv, probOn_notMem_and hv]
  simp only [Finset.insert_idem]
  ring

/-- **(Link) in probability**: `p · P(V_p ∈ 𝓘(H ∪ ∂_v H)) = P(v ∈ V_p ∧ V_p ∈ 𝓘(H))`
(paper, proof of Lemma 4.2: `V_p ∪ {v}` has the law of `V_p` conditioned on `v ∈ V_p`). -/
theorem mul_probIndep_union_link (H : Hypergraph V) (v : V) :
    p * probIndep p (H ∪ link H v) =
      probOn Finset.univ p (fun A ↦ v ∈ A ∧ IsIndep H A) := by
  have h1 : probIndep p (H ∪ link H v) =
      probOn Finset.univ p (fun A ↦ IsIndep H (insert v A)) :=
    probOn_congr fun A _ ↦ isIndep_union_link
  rw [h1, probOn_insert_eq_erase (Finset.mem_univ v), probOn_mem_and (Finset.mem_univ v)]

/-- `Pᵢ > 0`: `I ∈ 𝓘(Hᵢ)` gives `∅ ∈ 𝓘(Hᵢ)` (README §4.2, CLAUDE.md §7). -/
theorem probIndep_pos (hp0 : 0 ≤ p) (hp1 : p < 1) (hinv : Invariant H I st) :
    0 < probIndep p st.H :=
  probOn_pos_of_empty hp0 hp1 (hinv.indep.mono (Finset.empty_subset I))

/-- One round: if `Pᵢ ≤ (1 - δ)^|Sᵢ|` then `Pᵢ₊₁ ≤ (1 - δ)^|Sᵢ₊₁|`. -/
theorem probIndep_step_le (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ < 1) (hinv : Invariant H I st)
    (h : probIndep p st.H ≤ (1 - δ) ^ st.S.card) :
    probIndep p (step p δ I st).H ≤ (1 - δ) ^ (step p δ I st).S.card := by
  cases hv : nextVertex p δ st with
  | none => rwa [step_of_stopped hv]
  | some v =>
    obtain ⟨hvS, -, hlt⟩ := eligible_nextVertex hv
    rw [step_of_nextVertex hv]
    by_cases hvI : v ∈ I
    · -- `vᵢ ∈ I`: `p Pᵢ₊₁ = P(vᵢ ∈ V_p ∈ 𝓘(Hᵢ)) < (1 - δ) p Pᵢ`
      rw [update_of_mem hvI]
      simp only
      have hP := probIndep_pos hp0.le hp1 hinv
      rw [condProbIndep, condProb] at hlt
      change _ / probIndep p st.H < _ at hlt
      rw [div_lt_iff₀ hP, ← mul_probIndep_union_link] at hlt
      rw [Finset.card_insert_of_notMem hvS, pow_succ]
      have hlt' : probIndep p (st.H ∪ link st.H v) < (1 - δ) * probIndep p st.H := by
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hδ.le)]
    · -- `vᵢ ∉ I`: `Hᵢ ⊆ Hᵢ₊₁`, so `Pᵢ₊₁ ≤ Pᵢ`
      rw [update_of_notMem hvI]
      refine le_trans (probOn_mono hp0.le hp1.le fun A _ hA ↦ ?_) h
      exact hA.anti Finset.subset_union_left

/-- `Pᵢ ≤ (1 - δ)^|Sᵢ|` for every stage `i` (paper, display (4)). -/
theorem probIndep_stage_le (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ < 1) (hI : IsIndep H I)
    (i : ℕ) : probIndep p (stage p δ H I i).H ≤ (1 - δ) ^ (stage p δ H I i).S.card := by
  induction i with
  | zero =>
    simp only [stage_zero, State.init, Finset.card_empty, pow_zero]
    exact probOn_le_one hp0.le hp1.le _ _
  | succ i ih =>
    rw [stage_succ]
    exact probIndep_step_le hp0 hp1 hδ (lemma41 hI i) ih

/-- **Lemma 4.2.** `δ|S| ≤ p|V|`. -/
theorem lemma42 (hp0 : 0 < p) (hpδ : p ≤ δ) (hδ : δ < 1) (hI : IsIndep H I) :
    δ * (fingerprint p δ H I).card ≤ p * Fintype.card V := by
  have hp1 : p < 1 := hpδ.trans_lt hδ
  refine delta_mul_le_of_pow_le hp0 hpδ hδ ?_
  -- `(1 - p)^|V| = P(V_p = ∅) ≤ P_J ≤ (1 - δ)^|S|`
  have hlow : (1 - p) ^ Fintype.card V ≤ probIndep p (run p δ H I).H := by
    rw [← Finset.card_univ]
    exact probOn_ge_of_empty hp0.le hp1.le ((lemma41_run hI).indep.mono (Finset.empty_subset I))
  exact hlow.trans (probIndep_stage_le hp0 hp1 hδ hI _)

end CamposSamotij
