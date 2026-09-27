import Mathlib.Data.Fintype.Powerset

/-!
# Hypergraphs and independent sets (M1)

Hypergraphs on a finite vertex type as `Finset (Finset V)`, `IsIndep`,
heredity (down-closure), antitonicity in `H`, `∅` and singletons.
See README §3, §4.1.

## Definitions

* `Hypergraph V`: a hypergraph on the finite vertex set `V`.
* `IsIndep H I`: `I` is independent in `H`.
* `IsUniform H k`: every edge of `H` has exactly `k` vertices.
* `supersets e`: all `A ⊆ V` with `e ⊆ A`.
* `upClosure H` (paper: `⟨H⟩`): the union of `supersets e` over the edges `e ∈ H`.
* `Covers G H` (paper: "`G` covers `H`"): `H ⊆ ⟨G⟩`.
* `indepSets H` (paper: `𝓘(H)`): the family of all independent sets of `H`.

## Results

* `not_isIndep_of_singleton_mem`: if `{v} ∈ H` then no set containing `v` is
  independent; in particular `{v}` itself is not (`not_isIndep_singleton`).
-/

namespace CamposSamotij

variable {V : Type*}

/-! ### Definitions -/

/-- A hypergraph on the finite vertex set `V` is a family `E ⊆ 𝒫(V)` of subsets
of `V`, its *edges*. The vertex set is the whole type `V`, so vertices lying in
no edge are allowed. There are no repeated edges, and the empty edge `∅` is
allowed (then no set is independent). -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- `I ⊆ V` is *independent* in `H` if no edge of `H` is contained in `I`:
`∀ e ∈ E(H), e ⊄ I`. -/
def IsIndep (H : Hypergraph V) (I : Finset V) : Prop := ∀ e ∈ H, ¬ e ⊆ I

/-- `H` is `k`-*uniform* if every edge has exactly `k` vertices. -/
def IsUniform (H : Hypergraph V) (k : ℕ) : Prop := ∀ e ∈ H, e.card = k

section Closure

variable [Fintype V] [DecidableEq V]

instance decidableIsIndep (H : Hypergraph V) (I : Finset V) : Decidable (IsIndep H I) := by
  unfold IsIndep; infer_instance

/-- The *supersets* of `e ⊆ V`: all `A ⊆ V` with `e ⊆ A` (including `e`). -/
def supersets (e : Finset V) : Finset (Finset V) := Finset.univ.filter (e ⊆ ·)

/-- The *up-closure* `⟨H⟩` of `H`: the union of `supersets e` over all edges `e ∈ H`,
i.e. all `A ⊆ V` that contain some edge. The independent sets of `H` are exactly
the sets outside `⟨H⟩` (`isIndep_iff_not_mem_upClosure`). -/
def upClosure (H : Hypergraph V) : Finset (Finset V) := H.biUnion supersets

/-- `G` *covers* `H` if `H ⊆ ⟨G⟩`, i.e. every edge of `H` contains some edge of `G`
(paper, §1, just before Theorem A). -/
def Covers (G H : Hypergraph V) : Prop := H ⊆ upClosure G

instance decidableCovers (G H : Hypergraph V) : Decidable (Covers G H) := by
  unfold Covers; infer_instance

/-- The family `𝓘(H)` of all independent sets of `H`. -/
def indepSets (H : Hypergraph V) : Finset (Finset V) := Finset.univ.filter (IsIndep H)

/-! ### Membership lemmas -/

@[simp]
theorem mem_supersets {e A : Finset V} : A ∈ supersets e ↔ e ⊆ A := by
  simp [supersets]

@[simp]
theorem mem_upClosure {H : Hypergraph V} {A : Finset V} :
    A ∈ upClosure H ↔ ∃ e ∈ H, e ⊆ A := by
  simp [upClosure]

theorem covers_iff {G H : Hypergraph V} : Covers G H ↔ ∀ e ∈ H, ∃ f ∈ G, f ⊆ e := by
  simp [Covers, Finset.subset_iff]

@[simp]
theorem mem_indepSets {H : Hypergraph V} {I : Finset V} : I ∈ indepSets H ↔ IsIndep H I := by
  simp [indepSets]

theorem isIndep_iff_not_mem_upClosure {H : Hypergraph V} {I : Finset V} :
    IsIndep H I ↔ I ∉ upClosure H := by
  simp [IsIndep]

/-- `𝓘(H)` is the complement of the up-set `⟨H⟩` in `2^V`. -/
theorem indepSets_eq_compl_upClosure (H : Hypergraph V) :
    indepSets H = (upClosure H)ᶜ := by
  ext I; simp [isIndep_iff_not_mem_upClosure]

end Closure

/-! ### Results -/

/-- If `{v} ∈ E(H)`, then no set `I` with `v ∈ I` is independent in `H`. -/
theorem not_isIndep_of_singleton_mem {H : Hypergraph V} {v : V} {I : Finset V}
    (hv : {v} ∈ H) (hvI : v ∈ I) : ¬ IsIndep H I :=
  fun hI ↦ hI {v} hv (Finset.singleton_subset_iff.mpr hvI)

/-- If `{v} ∈ E(H)`, then `{v}` is not independent in `H`. -/
theorem not_isIndep_singleton {H : Hypergraph V} {v : V} (hv : {v} ∈ H) :
    ¬ IsIndep H {v} :=
  not_isIndep_of_singleton_mem hv (Finset.mem_singleton_self v)

end CamposSamotij
