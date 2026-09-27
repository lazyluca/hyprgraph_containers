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

end CamposSamotij
