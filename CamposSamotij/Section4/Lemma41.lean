import CamposSamotij.Algorithm.Defs

/-!
# Lemma 4.1: the invariant (M5)

See README §4.3; paper, Section 4.

> **Lemma 4.1.** For each `i`, we have `Sᵢ ⊆ I ∈ 𝓘(Hᵢ)` and
> `I' ∈ 𝓘(Hᵢ) ⟺ Sᵢ ∪ I' ∈ 𝓘(Hᵢ)`.

We also carry `H ⊆ Hᵢ` (README §4.3 item 4), which the paper notes in the proof of
Lemma 4.3 ("`H = H₀ ⊆ H₁ ⊆ ⋯ ⊆ H_J`").

## Definitions

* `Invariant H I st`: the four properties above for a state `st = (Hᵢ, Sᵢ)`.

## Results

* `Invariant.init`, `Invariant.update`, `Invariant.step`: base case and induction step.
  The induction step does not use eligibility: any vertex `v` preserves the invariant.
* `lemma41`: the invariant holds at every stage. `lemma41_run`: it holds for the output.
* `subset_container`: `I ∈ 𝓘(H') → I ⊆ {v : {v} ∉ H'}`.
* `fingerprint_subset`, `subset_containerOf`: `S ⊆ I ⊆ C` (paper, after Lemma 4.1).
-/

namespace CamposSamotij

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The invariant of Lemma 4.1 for a state `st = (Hᵢ, Sᵢ)` on input `I`. -/
structure Invariant (H : Hypergraph V) (I : Finset V) (st : State V) : Prop where
  /-- `Sᵢ ⊆ I`. -/
  S_subset : st.S ⊆ I
  /-- `I ∈ 𝓘(Hᵢ)`. -/
  indep : IsIndep st.H I
  /-- `I' ∈ 𝓘(Hᵢ) ⟺ Sᵢ ∪ I' ∈ 𝓘(Hᵢ)`. -/
  indep_iff : ∀ I', IsIndep st.H I' ↔ IsIndep st.H (st.S ∪ I')
  /-- `H ⊆ Hᵢ`. -/
  H_subset : H ⊆ st.H

namespace Invariant

variable {H : Hypergraph V} {I : Finset V} {st : State V}

omit [Fintype V] in
/-- Base case: `(H₀, S₀) = (H, ∅)`. -/
theorem init (hI : IsIndep H I) : Invariant H I (State.init H) where
  S_subset := Finset.empty_subset I
  indep := hI
  indep_iff I' := by simp [State.init]
  H_subset := subset_rfl

omit [Fintype V] in
/-- Induction step, case `v ∈ I` (step (2b)), via **(Link)**. -/
theorem update_of_mem (h : Invariant H I st) {v : V} (hv : v ∈ I) :
    Invariant H I (update I st v) := by
  rw [CamposSamotij.update_of_mem hv]
  refine ⟨Finset.insert_subset hv h.S_subset, ?_, fun I' ↦ ?_,
    h.H_subset.trans Finset.subset_union_left⟩
  · rw [isIndep_union_link, Finset.insert_eq_of_mem hv]
    exact h.indep
  · -- `{v} ∪ I' ∈ 𝓘(Hᵢ) ⟺ Sᵢ ∪ {v} ∪ I' ∈ 𝓘(Hᵢ) ⟺ {v} ∪ (Sᵢ ∪ {v} ∪ I') ∈ 𝓘(Hᵢ)`
    have hset : insert v (insert v st.S ∪ I') = st.S ∪ insert v I' := by
      ext x; simp only [Finset.mem_insert, Finset.mem_union]; tauto
    simp only [isIndep_union_link, hset]
    exact h.indep_iff _

omit [Fintype V] in
/-- Induction step, case `v ∉ I` (step (2c)), via **(Single)**. -/
theorem update_of_notMem (h : Invariant H I st) {v : V} (hv : v ∉ I) :
    Invariant H I (update I st v) := by
  rw [CamposSamotij.update_of_notMem hv]
  have hvS : v ∉ st.S := fun h' ↦ hv (h.S_subset h')
  refine ⟨h.S_subset, isIndep_union_singleton.mpr ⟨h.indep, hv⟩, fun I' ↦ ?_,
    h.H_subset.trans Finset.subset_union_left⟩
  simp only [isIndep_union_singleton, Finset.mem_union, hvS, false_or]
  rw [h.indep_iff I']

omit [Fintype V] in
/-- Induction step for an arbitrary vertex `v` (eligibility is not needed). -/
theorem update (h : Invariant H I st) (v : V) : Invariant H I (CamposSamotij.update I st v) := by
  by_cases hv : v ∈ I
  · exact h.update_of_mem hv
  · exact h.update_of_notMem hv

/-- Induction step: one round of the loop preserves the invariant. -/
theorem step {p δ : ℝ} (h : Invariant H I st) : Invariant H I (CamposSamotij.step p δ I st) := by
  cases hv : nextVertex p δ st with
  | none => rwa [step_of_stopped hv]
  | some v => rw [step_of_nextVertex hv]; exact h.update v

end Invariant

variable {p δ : ℝ} {H : Hypergraph V} {I : Finset V}

/-- **Lemma 4.1.** For each stage `i`: `Sᵢ ⊆ I ∈ 𝓘(Hᵢ)`,
`I' ∈ 𝓘(Hᵢ) ⟺ Sᵢ ∪ I' ∈ 𝓘(Hᵢ)`, and `H ⊆ Hᵢ`. -/
theorem lemma41 (hI : IsIndep H I) (i : ℕ) : Invariant H I (stage p δ H I i) := by
  induction i with
  | zero => exact Invariant.init hI
  | succ i ih => rw [stage_succ]; exact ih.step

/-- Lemma 4.1 for the final stage `(H_J, S_J)`. -/
theorem lemma41_run (hI : IsIndep H I) : Invariant H I (run p δ H I) :=
  lemma41 hI _

/-! ### Consequences (paper, after Lemma 4.1): `S ⊆ I ⊆ C` -/

/-- An independent set of `H'` avoids every `v` with `{v} ∈ H'`, so `𝓘(H') ⊆ 2^C`
with `C = {v : {v} ∉ H'}`. -/
theorem subset_container {H' : Hypergraph V} {I' : Finset V} (hI' : IsIndep H' I') :
    I' ⊆ container H' :=
  fun _ hu ↦ mem_container.mpr fun hmem ↦ not_isIndep_of_singleton_mem hmem hu hI'

/-- `S ⊆ I`. -/
theorem fingerprint_subset (hI : IsIndep H I) : fingerprint p δ H I ⊆ I :=
  (lemma41_run hI).S_subset

/-- `I ⊆ C`. -/
theorem subset_containerOf (hI : IsIndep H I) : I ⊆ containerOf p δ H I :=
  subset_container (lemma41_run hI).indep

end CamposSamotij
