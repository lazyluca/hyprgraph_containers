import CamposSamotij.Hypergraph.Basic

/-!
# Update operations (M2)

`link H v` (paper: ∂_v H) and `addSingleton H v` (paper: H ∪ {{v}}),
with the equivalences (Link) and (Single). See README §4.1.

## Definitions

* `link H v` (paper: `∂_v H`): the edges of `H` containing `v`, with `v` removed.
* Union of hypergraphs: `H ∪ H'` is `Finset` union; no new definition is needed.

## Results

* `mem_link`: `A ∈ ∂_v H ↔ ∃ B ∈ H, v ∈ B ∧ B \ {v} = A`.
* `isIndep_union`: `𝓘(H ∪ H') = 𝓘(H) ∩ 𝓘(H')`, pointwise.
* `isIndep_union_link` **(Link)**: `I' ∈ 𝓘(H ∪ ∂_v H) ↔ {v} ∪ I' ∈ 𝓘(H)`.
* `isIndep_union_singleton` **(Single)**: `I' ∈ 𝓘(H ∪ {{v}}) ↔ I' ∈ 𝓘(H) ∧ v ∉ I'`.
-/

namespace CamposSamotij

variable {V : Type*} [DecidableEq V]

/-! ### Link -/

/-- The *link* of `v` in `H` (paper, §2.1, with `L = {v}`):
`∂_v H := {E \ {v} : v ∈ E ∈ H}`.
These are the edges of `H` that contain `v`, **with `v` removed**. -/
def link (H : Hypergraph V) (v : V) : Hypergraph V :=
  (H.filter (v ∈ ·)).image (·.erase v)

@[simp]
theorem mem_link {H : Hypergraph V} {v : V} {A : Finset V} :
    A ∈ link H v ↔ ∃ B ∈ H, v ∈ B ∧ B.erase v = A := by
  simp [link, and_assoc]

/-- No edge of the link contains `v`. -/
theorem not_mem_of_mem_link {H : Hypergraph V} {v : V} {A : Finset V}
    (hA : A ∈ link H v) : v ∉ A := by
  obtain ⟨B, -, -, rfl⟩ := mem_link.mp hA
  exact Finset.notMem_erase v B

/-! ### Union of hypergraphs -/

/-- `I` is independent in `H ∪ H'` iff it is independent in both. -/
theorem isIndep_union {H H' : Hypergraph V} {I : Finset V} :
    IsIndep (H ∪ H') I ↔ IsIndep H I ∧ IsIndep H' I := by
  simp only [IsIndep, Finset.mem_union]
  exact ⟨fun h ↦ ⟨fun e he ↦ h e (.inl he), fun e he ↦ h e (.inr he)⟩,
    fun ⟨h, h'⟩ e he ↦ he.elim (h e) (h' e)⟩

/-! ### The equivalences (Link) and (Single) (README §4.1) -/

/-- **(Link)** `I' ∈ 𝓘(H ∪ ∂_v H) ↔ {v} ∪ I' ∈ 𝓘(H)` (paper, proof of Lemma 4.1).
An edge `A ⊆ {v} ∪ I'` of `H` either avoids `v` (then `A ⊆ I'`) or contains it
(then `A \ {v} ∈ ∂_v H` lies in `I'`). -/
theorem isIndep_union_link {H : Hypergraph V} {v : V} {I' : Finset V} :
    IsIndep (H ∪ link H v) I' ↔ IsIndep H (insert v I') := by
  rw [isIndep_union]
  constructor
  · rintro ⟨hH, hL⟩ e he heI
    by_cases hve : v ∈ e
    · exact hL (e.erase v) (mem_link.mpr ⟨e, he, hve, rfl⟩) (Finset.subset_insert_iff.mp heI)
    · exact hH e he ((Finset.subset_insert_iff_of_notMem hve).mp heI)
  · intro h
    refine ⟨h.mono (Finset.subset_insert v I'), fun A hA hAI ↦ ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := mem_link.mp hA
    exact h B hB (Finset.subset_insert_iff.mpr hAI)

omit [DecidableEq V] in
/-- `I` is independent in the one-edge hypergraph `{{v}}` iff `v ∉ I`. -/
@[simp]
theorem isIndep_singleton_hypergraph {v : V} {I : Finset V} :
    IsIndep ({{v}} : Hypergraph V) I ↔ v ∉ I := by
  simp [IsIndep]

/-- **(Single)** `I' ∈ 𝓘(H ∪ {{v}}) ↔ I' ∈ 𝓘(H) ∧ v ∉ I'`. -/
theorem isIndep_union_singleton {H : Hypergraph V} {v : V} {I' : Finset V} :
    IsIndep (H ∪ {{v}}) I' ↔ IsIndep H I' ∧ v ∉ I' := by
  rw [isIndep_union, isIndep_singleton_hypergraph]

end CamposSamotij
