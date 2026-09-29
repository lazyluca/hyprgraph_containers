import CamposSamotij.Section4.Lemma41
import CamposSamotij.Prop22.Statement

/-!
# Lemma 4.3: container probability (M7)

Coupling identity and the application of Proposition 2.2.
See README §4.5; paper, Section 4 (p. 13).

> **Lemma 4.3.** We have `P(S ∪ C_p ∈ 𝓘(H)) ≥ (1 - p)^{δ|C \ S|}`.

Proof (paper), with `C' := C \ S` and `(H_J, S)` the final state:

1. `P(S ∪ C_p ∈ 𝓘(H)) ≥ P(S ∪ C_p ∈ 𝓘(H_J)) = P(S ∪ C'_p ∈ 𝓘(H_J))`.
2. `𝓕 := {X ⊆ C' : S ∪ X ∈ 𝓘(H_J)}` is a nonempty down-set.
3. (coupling) for `v ∈ C'`: `P(v ∈ C'_p | S ∪ C'_p ∈ 𝓘(H_J)) = P(v ∈ V_p | V_p ∈ 𝓘(H_J))`.
4. (stopping) this is `≥ (1 - δ)p`, since `v ∉ S`, `{v} ∉ H_J`, and `v` is not eligible.
5. Summing: `E[|C'_p| | C'_p ∈ 𝓕] ≥ (1 - δ)p|C'|`.
6. Proposition 2.2 (`prop22_rpow`).

## Results

* `union_inter_sdiff_eq`, `isIndep_iff_split`: `V_p ∈ 𝓘(G)` splits into a condition on
  `V_p \ C'` and one on `V_p ∩ C'`.
* `condProb_coupling`: step 3, as a finite-sum factorization over `V = (V \ C') ⊔ C'`.
* `lemma43_of`: the lemma for any state `(G, S)` satisfying the invariant and stopped.
* `lemma43`: the lemma for the output of the algorithm.

Note: `lemma43` needs only `0 < p < 1`, not `p ≤ δ < 1`.
-/

namespace CamposSamotij

universe u

section Coupling

variable {V : Type*} [Fintype V] [LinearOrder V] {p : ℝ} {G : Hypergraph V} {S : Finset V}
  {v : V}

omit [Fintype V] in
/-- If every element of `A` outside `C \ S` lies in `S`, then `S ∪ (A ∩ (C \ S)) = S ∪ A`. -/
theorem union_inter_sdiff_eq {C A : Finset V} (h : ∀ x ∈ A, x ∉ C \ S → x ∈ S) :
    S ∪ (A ∩ (C \ S)) = S ∪ A := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (hx | ⟨hx, -⟩)
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inl hx
    · by_cases hxC : x ∈ C \ S
      · exact Or.inr ⟨hx, hxC⟩
      · exact Or.inl (h x hx hxC)

omit [Fintype V] in
/-- `condProb` only sees the conditioning event on subsets of `X`. -/
theorem condProb_congr_right {X : Finset V} {E F F' : Finset V → Prop} [DecidablePred E]
    [DecidablePred F] [DecidablePred F'] (h : ∀ A ⊆ X, (F A ↔ F' A)) :
    condProb X p E F = condProb X p E F' := by
  unfold condProb
  rw [probOn_congr (E := fun A ↦ E A ∧ F A) (E' := fun A ↦ E A ∧ F' A)
      fun A hA ↦ by rw [h A hA], probOn_congr h]

/-- Under Lemma 4.1(3) and `S ⊆ C` (with `C = container G`, `C' = C \ S`):
`A ∈ 𝓘(G) ↔ A \ C' ⊆ S ∧ S ∪ (A ∩ C') ∈ 𝓘(G)`. -/
theorem isIndep_iff_split (hS : ∀ I', IsIndep G I' ↔ IsIndep G (S ∪ I'))
    (A : Finset V) :
    IsIndep G A ↔ A ∩ (Finset.univ \ (container G \ S)) ⊆ S ∧
      IsIndep G (S ∪ (A ∩ (container G \ S))) := by
  have key : ∀ A : Finset V, A ∩ (Finset.univ \ (container G \ S)) ⊆ S →
      S ∪ (A ∩ (container G \ S)) = S ∪ A := fun A h ↦
    union_inter_sdiff_eq fun x hx hx' ↦
      h (Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx'⟩⟩)
  constructor
  · intro hA
    have h1 : A ∩ (Finset.univ \ (container G \ S)) ⊆ S := by
      intro x hx
      obtain ⟨hxA, hxC'⟩ := Finset.mem_inter.mp hx
      by_contra hxS
      exact (Finset.mem_sdiff.mp hxC').2
        (Finset.mem_sdiff.mpr ⟨subset_container hA hxA, hxS⟩)
    exact ⟨h1, (key A h1).symm ▸ (hS A).mp hA⟩
  · rintro ⟨h1, h2⟩
    rw [key A h1] at h2
    exact (hS A).mpr h2

/-- **Coupling identity** (Lemma 4.3, step 3). For `v ∈ C' = C \ S`:
`P(v ∈ C'_p | S ∪ C'_p ∈ 𝓘(G)) = P(v ∈ V_p | V_p ∈ 𝓘(G))`.
Both events factor over `V = (V \ C') ⊔ C'` as `[V_p \ C' ⊆ S] × (event of V_p ∩ C')`,
and the common factor `P((V \ C')_p ⊆ S) > 0` cancels. -/
theorem condProb_coupling (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hS : ∀ I', IsIndep G I' ↔ IsIndep G (S ∪ I')) (hv : v ∈ container G \ S) :
    condProb (container G \ S) p (v ∈ ·) (fun T ↦ IsIndep G (S ∪ T)) =
      condProbIndep p G v := by
  have hdisj : Disjoint (Finset.univ \ (container G \ S)) (container G \ S) :=
    Finset.sdiff_disjoint
  have hU : (Finset.univ \ (container G \ S)) ∪ (container G \ S) = Finset.univ :=
    Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have hD : 0 < probOn (Finset.univ \ (container G \ S)) p (· ⊆ S) :=
    probOn_pos_of_empty hp0 hp1 (Finset.empty_subset S)
  have hden : probOn Finset.univ p (IsIndep G) =
      probOn (Finset.univ \ (container G \ S)) p (· ⊆ S) *
        probOn (container G \ S) p (fun T ↦ IsIndep G (S ∪ T)) := by
    have := probOn_union_inter (p := p) hdisj (· ⊆ S) (fun T ↦ IsIndep G (S ∪ T))
    rw [hU] at this
    rw [← this]
    exact probOn_congr fun A _ ↦ isIndep_iff_split hS A
  have hnum : probOn Finset.univ p (fun A ↦ v ∈ A ∧ IsIndep G A) =
      probOn (Finset.univ \ (container G \ S)) p (· ⊆ S) *
        probOn (container G \ S) p (fun T ↦ v ∈ T ∧ IsIndep G (S ∪ T)) := by
    have := probOn_union_inter (p := p) hdisj (· ⊆ S) (fun T ↦ v ∈ T ∧ IsIndep G (S ∪ T))
    rw [hU] at this
    rw [← this]
    refine probOn_congr fun A _ ↦ ?_
    rw [isIndep_iff_split hS A, Finset.mem_inter]
    simp only [hv, and_true]
    tauto
  rw [condProbIndep, condProb, condProb, hden, hnum, mul_div_mul_left _ _ hD.ne']

end Coupling

section Main

variable {V : Type u} [Fintype V] [LinearOrder V] {p δ : ℝ}

/-- **Lemma 4.3** for any state `(G, S)` with `H ⊆ G`, `S ∈ 𝓘(G)`, `S ⊆ C = container G`,
Lemma 4.1(3), and the stopping condition on `C' = C \ S`:
`P(S ∪ C_p ∈ 𝓘(H)) ≥ (1 - p)^{δ|C'|}`. -/
theorem lemma43_of (hProp22 : Prop22Statement.{u}) {H G : Hypergraph V} {S : Finset V}
    (hp0 : 0 < p) (hp1 : p < 1) (hHG : H ⊆ G) (hSind : IsIndep G S)
    (hS : ∀ I', IsIndep G I' ↔ IsIndep G (S ∪ I')) (hSC : S ⊆ container G)
    (hstop : ∀ v ∈ container G \ S, (1 - δ) * p ≤ condProbIndep p G v) :
    (1 - p) ^ (δ * ((container G \ S).card : ℝ)) ≤
      probOn (container G) p (fun A ↦ IsIndep H (S ∪ A)) := by
  -- Step 1: `P(S ∪ C'_p ∈ 𝓘(G)) ≤ P(S ∪ C_p ∈ 𝓘(H))`
  have step1 : probOn (container G \ S) p (fun T ↦ IsIndep G (S ∪ T)) ≤
      probOn (container G) p (fun A ↦ IsIndep H (S ∪ A)) := by
    have e : probOn (container G) p (fun A ↦ IsIndep G (S ∪ A)) =
        probOn (container G \ S) p (fun T ↦ IsIndep G (S ∪ T)) := by
      have := probOn_union_right (p := p) (Finset.disjoint_sdiff : Disjoint S (container G \ S))
        (fun T ↦ IsIndep G (S ∪ T))
      rw [Finset.union_sdiff_of_subset hSC] at this
      rw [← this]
      refine probOn_congr fun A hA ↦ ?_
      rw [union_inter_sdiff_eq fun x hx hx' ↦
        by_contra fun hxS ↦ hx' (Finset.mem_sdiff.mpr ⟨hA hx, hxS⟩)]
    rw [← e]
    exact probOn_mono hp0.le hp1.le fun A _ hA ↦ hA.anti hHG
  -- Step 2: the nonempty down-set `𝓕`
  set 𝓕 := (container G \ S).powerset.filter (fun T ↦ IsIndep G (S ∪ T)) with h𝓕
  have hdown : IsLowerSet (𝓕 : Set (Finset V)) := by
    intro A B hBA hA
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA ⊢
    have hBA' : B ⊆ A := hBA
    exact ⟨hBA'.trans hA.1, hA.2.mono (Finset.union_subset_union subset_rfl hBA')⟩
  have hne : 𝓕.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by rwa [Finset.union_empty]⟩⟩
  have hprob : probOn (container G \ S) p (· ∈ 𝓕) =
      probOn (container G \ S) p (fun T ↦ IsIndep G (S ∪ T)) :=
    probOn_congr fun A hA ↦ by
      rw [h𝓕, Finset.mem_filter, Finset.mem_powerset]
      exact and_iff_right hA
  -- Steps 3–5: `E[|C'_p| | C'_p ∈ 𝓕] ≥ (1 - δ)p|C'|`
  have hE : (1 - δ) * p * (container G \ S).card ≤
      condExp (container G \ S) p (fun A ↦ (A.card : ℝ)) (· ∈ 𝓕) := by
    rw [condExp_card]
    have hterm : ∀ v ∈ container G \ S,
        (1 - δ) * p ≤ condProb (container G \ S) p (v ∈ ·) (· ∈ 𝓕) := by
      intro v hv
      rw [condProb_congr_right (F' := fun T ↦ IsIndep G (S ∪ T)) fun A hA ↦ by
          rw [h𝓕, Finset.mem_filter, Finset.mem_powerset]
          exact and_iff_right hA,
        condProb_coupling hp0.le hp1 hS hv]
      exact hstop v hv
    have := Finset.card_nsmul_le_sum _ _ _ hterm
    rw [nsmul_eq_mul] at this
    linarith
  -- Step 6: Proposition 2.2
  have h22 := prop22_rpow hProp22 hp0 hp1 hdown (Finset.filter_subset _ _) hne
  have hexp : (container G \ S).card -
      condExp (container G \ S) p (fun A ↦ (A.card : ℝ)) (· ∈ 𝓕) / p ≤
        δ * (container G \ S).card := by
    have : (1 - δ) * (container G \ S).card ≤
        condExp (container G \ S) p (fun A ↦ (A.card : ℝ)) (· ∈ 𝓕) / p := by
      rw [le_div_iff₀ hp0]
      linarith
    linarith
  calc (1 - p) ^ (δ * ((container G \ S).card : ℝ))
      ≤ (1 - p) ^ ((container G \ S).card -
          condExp (container G \ S) p (fun A ↦ (A.card : ℝ)) (· ∈ 𝓕) / p) :=
        Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hp1) (by linarith) hexp
    _ ≤ probOn (container G \ S) p (· ∈ 𝓕) := h22
    _ = probOn (container G \ S) p (fun T ↦ IsIndep G (S ∪ T)) := hprob
    _ ≤ probOn (container G) p (fun A ↦ IsIndep H (S ∪ A)) := step1

/-- **Lemma 4.3.** For the output `(S, C)` of the algorithm on `I ∈ 𝓘(H)`:
`P(S ∪ C_p ∈ 𝓘(H)) ≥ (1 - p)^{δ|C \ S|}`. -/
theorem lemma43 (hProp22 : Prop22Statement.{u}) {H : Hypergraph V} {I : Finset V}
    (hp0 : 0 < p) (hp1 : p < 1) (hI : IsIndep H I) :
    (1 - p) ^ (δ * ((containerOf p δ H I \ fingerprint p δ H I).card : ℝ)) ≤
      probOn (containerOf p δ H I) p (fun A ↦ IsIndep H (fingerprint p δ H I ∪ A)) := by
  have hinv := lemma41_run (p := p) (δ := δ) hI
  have hstop := nextVertex_eq_none_iff.mp (run_stopped (p := p) (δ := δ) (I := I) H)
  refine lemma43_of hProp22 hp0 hp1 hinv.H_subset (hinv.indep.mono hinv.S_subset)
    hinv.indep_iff (hinv.S_subset.trans (subset_container hinv.indep)) fun v hv ↦ ?_
  obtain ⟨hvC, hvS⟩ := Finset.mem_sdiff.mp hv
  exact not_lt.mp fun hlt ↦ hstop v ⟨hvS, mem_container.mp hvC, hlt⟩

end Main

end CamposSamotij
