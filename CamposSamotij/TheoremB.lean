import CamposSamotij.Statement
import CamposSamotij.Section4.Lemma41
import CamposSamotij.Section4.Lemma42
import CamposSamotij.Section4.Lemma43

/-!
# Theorem B (M8)

Replay lemma, `g`, `f`, `𝒮`, and the assembly of Theorem B,
conditional on `hProp22 : Prop22Statement`. See README §4.6.

## Construction

* `g(I) := fingerprint p δ H I`, the fingerprint `S` output on input `I`;
* `f(S) := containerOf p δ H S`, the container obtained by **rerunning** the algorithm on `S`;
* `𝒮 := g(𝓘(H))`.

## Results

* `S_subset_step`, `stage_S_mono`: the fingerprint only grows along the run.
* `stage_fingerprint` (**replay lemma**): for `I ∈ 𝓘(H)` with `S = g(I)`, the runs on `I`
  and on `S` pass through the same states, since at every round `vᵢ ∈ I ↔ vᵢ ∈ S`.
* `containerOf_fingerprint`: hence `f(g(I)) = C(I)`, the container output on `I`.
* `theoremB`: (a) from Lemma 4.1, (b) from Lemma 4.2, (c) from Lemma 4.3.
-/

namespace CamposSamotij

universe u

section Replay

variable {V : Type*} [Fintype V] [LinearOrder V] {p δ : ℝ} {H : Hypergraph V}
  {I : Finset V}

omit [Fintype V] in
/-- `update` never removes vertices from the fingerprint. -/
theorem S_subset_update (I : Finset V) (st : State V) (v : V) :
    st.S ⊆ (update I st v).S := by
  by_cases hv : v ∈ I
  · rw [update_of_mem hv]; exact Finset.subset_insert v st.S
  · rw [update_of_notMem hv]

/-- `Sᵢ ⊆ Sᵢ₊₁`. -/
theorem S_subset_step (I : Finset V) (st : State V) : st.S ⊆ (step p δ I st).S := by
  cases hv : nextVertex p δ st with
  | none => rw [step_of_stopped hv]
  | some v => rw [step_of_nextVertex hv]; exact S_subset_update I st v

/-- `i ≤ j → Sᵢ ⊆ Sⱼ`. -/
theorem stage_S_mono (H : Hypergraph V) (I : Finset V) :
    Monotone fun i ↦ (stage p δ H I i).S :=
  monotone_nat_of_le_succ fun i ↦ by
    simp only [stage_succ]; exact S_subset_step I _

/-- **Replay lemma.** For `I ∈ 𝓘(H)` and `S = g(I)`, the runs on `I` and on `S` agree up to
stage `|V|`: at each round `vᵢ ∈ I ↔ vᵢ ∈ S` ("→" since `vᵢ` joins `Sᵢ₊₁ ⊆ S`,
"←" since `S ⊆ I`), and the choice of `vᵢ` does not look at the input. -/
theorem stage_fingerprint (hI : IsIndep H I) :
    ∀ i ≤ Fintype.card V, stage p δ H (fingerprint p δ H I) i = stage p δ H I i
  | 0, _ => rfl
  | i + 1, hi => by
    rw [stage_succ, stage_succ, stage_fingerprint hI i (Nat.le_of_succ_le hi)]
    cases hv : nextVertex p δ (stage p δ H I i) with
    | none => rw [step_of_stopped hv, step_of_stopped hv]
    | some v =>
      rw [step_of_nextVertex hv, step_of_nextVertex hv]
      suffices hvI : v ∈ fingerprint p δ H I ↔ v ∈ I by simp only [update, hvI]
      refine ⟨fun h ↦ fingerprint_subset hI h, fun h ↦ ?_⟩
      -- `vᵢ ∈ Sᵢ₊₁ ⊆ S_{|V|} = S`
      have hmem : v ∈ (stage p δ H I (i + 1)).S := by
        rw [stage_succ, step_of_nextVertex hv, update_of_mem h]
        exact Finset.mem_insert_self v _
      exact stage_S_mono H I hi hmem

/-- `run(H, g(I)) = run(H, I)`. -/
theorem run_fingerprint (hI : IsIndep H I) :
    run p δ H (fingerprint p δ H I) = run p δ H I :=
  stage_fingerprint hI _ le_rfl

/-- `f(g(I)) = C(I)`: rerunning on the fingerprint recovers the container. -/
theorem containerOf_fingerprint (hI : IsIndep H I) :
    containerOf p δ H (fingerprint p δ H I) = containerOf p δ H I := by
  rw [containerOf, containerOf, run_fingerprint hI]

end Replay

/-- **Theorem B**, conditional on Proposition 2.2. -/
theorem theoremB (hProp22 : Prop22Statement.{u}) : TheoremBStatement.{u} := by
  intro V _ _ H p δ hp0 hpδ hδ
  have hp1 : p < 1 := hpδ.trans_lt hδ
  have hδ0 : 0 < δ := hp0.trans_le hpδ
  refine ⟨(Finset.univ.filter (IsIndep H)).image (fingerprint p δ H),
    fingerprint p δ H, containerOf p δ H, fun I hI ↦ ?_, fun I hI ↦ ?_, ?_, ?_⟩
  · -- `g : 𝓘(H) → 𝒮`
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ I, hI⟩)
  · -- (a) Lemma 4.1 and replay
    rw [containerOf_fingerprint hI]
    exact ⟨fingerprint_subset hI, subset_containerOf hI⟩
  · -- (b) Lemma 4.2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro _ ⟨I, hI, rfl⟩
    rw [le_div_iff₀ hδ0, mul_comm]
    exact lemma42 hp0 hpδ hδ hI
  · -- (c) Lemma 4.3 and replay
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro _ ⟨I, hI, rfl⟩
    rw [containerOf_fingerprint hI]
    exact lemma43 hProp22 hp0 hp1 hI

end CamposSamotij
