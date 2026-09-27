import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Finite p-random subsets (M3)

`weight`, `probOn`, `condProb`, `condExp` as explicit `Finset` sums;
conditioning on `v ∈ X_p`; product/splitting over `W = A ⊔ B`.
Downstream files use only the API lemmas proved here. See README §7.

## The model

For a finite set `X ⊆ V` and `p ∈ [0,1]`, the paper's `X_p` is the random subset
of `X` that keeps each element independently with probability `p`. Its law is
`P(X_p = A) = p^|A| (1-p)^|X \ A|` for `A ⊆ X`. We never build a measure. Every
probability is the finite sum of this weight over `X.powerset`.

## Definitions

* `weight p X A`: `P(X_p = A)`, i.e. `p^|A| (1-p)^|X \ A|`.
* `probOn X p E`: `P(E(X_p))`, for an event `E : Finset V → Prop`.
* `condProb X p E F`: `P(E(X_p) | F(X_p))`.
* `condExp X p f F`: `E[f(X_p) | F(X_p)]`, for `f : Finset V → ℝ`.

Events are predicates, not families, so that "`v ∈ X_p` and `X_p ∈ 𝓘(H)`" is
just `fun A ↦ v ∈ A ∧ IsIndep H A`. A family `𝓕` is the event `(· ∈ 𝓕)`.

⚠ UNSURE: division convention — `condProb` and `condExp` use Lean's `x / 0 = 0`,
so they are `0` when `P(F) = 0` — the paper only conditions on events of positive
probability, so every downstream use must carry `0 < probOn X p F`
(CLAUDE.md §7, "Conditional probability needs P_i > 0"), via `probOn_pos_of_empty`.
-/

namespace CamposSamotij

variable {V : Type*} [DecidableEq V]

/-! ### Definitions -/

/-- `P(X_p = A) = p^|A| (1-p)^|X \ A|`. Intended for `A ⊆ X`; outside `X.powerset`
it is never summed over. -/
def weight (p : ℝ) (X A : Finset V) : ℝ := p ^ A.card * (1 - p) ^ (X \ A).card

/-- `P(E(X_p))`: the total weight of the subsets `A ⊆ X` satisfying `E`. -/
def probOn (X : Finset V) (p : ℝ) (E : Finset V → Prop) [DecidablePred E] : ℝ :=
  ∑ A ∈ X.powerset with E A, weight p X A

/-- `P(E(X_p) | F(X_p)) = P(E ∧ F) / P(F)`. Equals `0` if `P(F) = 0`. -/
noncomputable def condProb (X : Finset V) (p : ℝ) (E F : Finset V → Prop)
    [DecidablePred E] [DecidablePred F] : ℝ :=
  probOn X p (fun A ↦ E A ∧ F A) / probOn X p F

/-- `E[f(X_p) | F(X_p)] = (∑_{A ⊆ X, F A} P(X_p = A) f(A)) / P(F)`.
Equals `0` if `P(F) = 0`. -/
noncomputable def condExp (X : Finset V) (p : ℝ) (f : Finset V → ℝ) (F : Finset V → Prop)
    [DecidablePred F] : ℝ :=
  (∑ A ∈ X.powerset with F A, weight p X A * f A) / probOn X p F

/-! ### Results

Each result lists where it is used downstream. -/

section Results

variable {X Y A B : Finset V} {p : ℝ} {v : V}

/-! #### 1. Basic bounds (used in Lemma 4.2 and Lemma 4.3 step 1) -/

theorem weight_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X A : Finset V) : 0 ≤ weight p X A :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem weight_pos (hp0 : 0 < p) (hp1 : p < 1) (X A : Finset V) : 0 < weight p X A :=
  mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)

theorem probOn_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset V) (E : Finset V → Prop)
    [DecidablePred E] : 0 ≤ probOn X p E :=
  Finset.sum_nonneg fun A _ ↦ weight_nonneg hp0 hp1 X A

/-- Events that agree on all subsets of `X` have the same probability. -/
theorem probOn_congr {E E' : Finset V → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ A ⊆ X, (E A ↔ E' A)) : probOn X p E = probOn X p E' := by
  simp only [probOn, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  simp only [h A (Finset.mem_powerset.mp hA)]

/-- `probOn` is monotone in the event. -/
theorem probOn_mono {E E' : Finset V → Prop} [DecidablePred E] [DecidablePred E']
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ∀ A ⊆ X, E A → E' A) :
    probOn X p E ≤ probOn X p E' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun A _ _ ↦ weight_nonneg hp0 hp1 X A
  intro A
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact fun ⟨hA, hE⟩ ↦ ⟨hA, h A hA hE⟩

/-! #### 2. Total mass -/

/-- The weights of all subsets of `X` sum to `1` (for every real `p`). -/
theorem sum_weight (p : ℝ) (X : Finset V) : ∑ A ∈ X.powerset, weight p X A = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) X
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [weight, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA)]

@[simp]
theorem probOn_true (p : ℝ) (X : Finset V) : probOn X p (fun _ ↦ True) = 1 := by
  simp [probOn, sum_weight]

theorem probOn_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset V) (E : Finset V → Prop)
    [DecidablePred E] : probOn X p E ≤ 1 :=
  (probOn_mono hp0 hp1 (E' := fun _ ↦ True) fun _ _ _ ↦ trivial).trans_eq (probOn_true p X)

/-! #### 3. Positivity from `∅` (gives `P_i > 0`, README §4.2) -/

theorem probOn_ge_of_empty {E : Finset V → Prop} [DecidablePred E]
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : E ∅) : (1 - p) ^ X.card ≤ probOn X p E := by
  have h0 : weight p X ∅ = (1 - p) ^ X.card := by simp [weight]
  rw [← h0]
  exact Finset.single_le_sum (f := weight p X) (fun A _ ↦ weight_nonneg hp0 hp1 X A)
    (Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset X, h⟩)

theorem probOn_pos_of_empty {E : Finset V → Prop} [DecidablePred E]
    (hp0 : 0 ≤ p) (hp1 : p < 1) (h : E ∅) : 0 < probOn X p E :=
  (pow_pos (sub_pos.mpr hp1) _).trans_le (probOn_ge_of_empty hp0 hp1.le h)

/-! #### 4. Conditioning on `v ∈ X_p` (used in Lemma 4.2, case `v_i ∈ I`) -/

theorem weight_insert_insert (hv : v ∉ Y) (hB : B ⊆ Y) :
    weight p (insert v Y) (insert v B) = p * weight p Y B := by
  have hvB : v ∉ B := fun h ↦ hv (hB h)
  have : insert v Y \ insert v B = Y \ B := by
    ext x; by_cases hx : x = v <;> simp [hx, hv]
  rw [weight, weight, this, Finset.card_insert_of_notMem hvB, pow_succ]
  ring

theorem weight_insert_of_notMem (hv : v ∉ Y) (hB : B ⊆ Y) :
    weight p (insert v Y) B = (1 - p) * weight p Y B := by
  have hvB : v ∉ B := fun h ↦ hv (hB h)
  have : insert v Y \ B = insert v (Y \ B) := by
    ext x; by_cases hx : x = v <;> simp [hx, hvB]
  rw [weight, weight, this, Finset.card_insert_of_notMem (by simp [hv]), pow_succ]
  ring

/-- Split an event according to whether `v ∈ X_p`. -/
theorem probOn_split (v : V) (X : Finset V) (E : Finset V → Prop) [DecidablePred E] :
    probOn X p E = probOn X p (fun A ↦ v ∈ A ∧ E A) + probOn X p (fun A ↦ v ∉ A ∧ E A) := by
  simp only [probOn, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  by_cases hv : v ∈ A <;> by_cases hE : E A <;> simp [hv, hE]

/-- `P(v ∈ X_p ∧ E(X_p)) = p · P(E(Y_p ∪ {v}))` for `X = Y ⊔ {v}`:
`Y_p ∪ {v}` has the law of `X_p` conditioned on `v ∈ X_p`. -/
theorem probOn_insert_mem {E : Finset V → Prop} [DecidablePred E] (hv : v ∉ Y) :
    probOn (insert v Y) p (fun A ↦ v ∈ A ∧ E A) = p * probOn Y p (fun B ↦ E (insert v B)) := by
  simp only [probOn, Finset.sum_filter]
  rw [Finset.sum_powerset_insert hv, Finset.mul_sum]
  have h1 : ∑ A ∈ Y.powerset, (if v ∈ A ∧ E A then weight p (insert v Y) A else 0) = 0 :=
    Finset.sum_eq_zero fun A hA ↦ ite_eq_right fun h ↦ hv (Finset.mem_powerset.mp hA h.1)
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun B hB ↦ ?_
  rw [weight_insert_insert hv (Finset.mem_powerset.mp hB)]
  split_ifs with h1 h2 h2 <;> simp_all

/-- `P(v ∉ X_p ∧ E(X_p)) = (1 - p) · P(E(Y_p))` for `X = Y ⊔ {v}`. -/
theorem probOn_insert_notMem {E : Finset V → Prop} [DecidablePred E] (hv : v ∉ Y) :
    probOn (insert v Y) p (fun A ↦ v ∉ A ∧ E A) = (1 - p) * probOn Y p E := by
  simp only [probOn, Finset.sum_filter]
  rw [Finset.sum_powerset_insert hv, Finset.mul_sum]
  have h2 : ∑ B ∈ Y.powerset,
      (if v ∉ insert v B ∧ E (insert v B) then weight p (insert v Y) (insert v B) else 0) = 0 :=
    Finset.sum_eq_zero fun B _ ↦ ite_eq_right fun h ↦ h.1 (Finset.mem_insert_self v B)
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  have hvA : v ∉ A := fun h ↦ hv (Finset.mem_powerset.mp hA h)
  rw [weight_insert_of_notMem hv (Finset.mem_powerset.mp hA)]
  split_ifs with h1 h2 h2 <;> simp_all

/-- `probOn_insert_mem` for `v ∈ X`, with `X \ {v}` written `X.erase v`. -/
theorem probOn_mem_and {E : Finset V → Prop} [DecidablePred E] (hv : v ∈ X) :
    probOn X p (fun A ↦ v ∈ A ∧ E A) = p * probOn (X.erase v) p (fun B ↦ E (insert v B)) := by
  conv_lhs => rw [← Finset.insert_erase hv]
  exact probOn_insert_mem (Finset.notMem_erase v X)

/-- `probOn_insert_notMem` for `v ∈ X`, with `X \ {v}` written `X.erase v`. -/
theorem probOn_notMem_and {E : Finset V → Prop} [DecidablePred E] (hv : v ∈ X) :
    probOn X p (fun A ↦ v ∉ A ∧ E A) = (1 - p) * probOn (X.erase v) p E := by
  conv_lhs => rw [← Finset.insert_erase hv]
  exact probOn_insert_notMem (Finset.notMem_erase v X)

/-! #### 5. Splitting over `X = A ⊔ B` (used in Lemma 4.3 step 3, coupling identity) -/

/-- **Product formula.** For disjoint `A`, `B`, the parts `X_p ∩ A` and `X_p ∩ B` of
`(A ∪ B)_p` are independent, with laws `A_p` and `B_p`:
`P(E_A((A ∪ B)_p ∩ A) ∧ E_B((A ∪ B)_p ∩ B)) = P(E_A(A_p)) · P(E_B(B_p))`. -/
theorem probOn_union_inter (hAB : Disjoint A B) (EA EB : Finset V → Prop)
    [hEA : DecidablePred EA] [DecidablePred EB] :
    probOn (A ∪ B) p (fun T ↦ EA (T ∩ A) ∧ EB (T ∩ B)) = probOn A p EA * probOn B p EB := by
  induction A using Finset.induction_on generalizing EA hEA with
  | empty =>
    have h0 : probOn (∅ : Finset V) p EA = if EA ∅ then 1 else 0 := by
      rw [probOn, Finset.powerset_empty, Finset.sum_filter, Finset.sum_singleton]
      simp [weight]
    rw [Finset.empty_union, h0]
    by_cases h : EA ∅
    · rw [ite_eq_left h, one_mul]
      exact probOn_congr fun T hT ↦ by simp [h, Finset.inter_eq_left.mpr hT]
    · rw [ite_eq_right h, zero_mul]
      simp [probOn, h]
  | insert a A ha ih =>
    obtain ⟨haB, hAB'⟩ := Finset.disjoint_insert_left.mp hAB
    have haX : a ∉ A ∪ B := by simp [ha, haB]
    have h1 : probOn (A ∪ B) p
        (fun T ↦ EA (insert a T ∩ insert a A) ∧ EB (insert a T ∩ B)) =
        probOn A p (fun S ↦ EA (insert a S)) * probOn B p EB := by
      rw [← ih hAB' (fun S ↦ EA (insert a S))]
      exact probOn_congr fun T _ ↦ by
        rw [← Finset.insert_inter_distrib, Finset.insert_inter_of_notMem haB]
    have h2 : probOn (A ∪ B) p (fun T ↦ EA (T ∩ insert a A) ∧ EB (T ∩ B)) =
        probOn A p EA * probOn B p EB := by
      rw [← ih hAB' EA]
      exact probOn_congr fun T hT ↦ by
        rw [Finset.inter_insert_of_notMem fun h ↦ haX (hT h)]
    rw [Finset.insert_union, probOn_split a, probOn_insert_mem haX, probOn_insert_notMem haX,
      h1, h2, probOn_split a (insert a A) EA, probOn_insert_mem ha, probOn_insert_notMem ha]
    ring

/-- If `E` only looks at `X_p ∩ B`, the rest of `A ∪ B` can be dropped. -/
theorem probOn_union_right (hAB : Disjoint A B) (E : Finset V → Prop) [DecidablePred E] :
    probOn (A ∪ B) p (fun T ↦ E (T ∩ B)) = probOn B p E := by
  have h := probOn_union_inter (p := p) hAB (fun _ ↦ True) E
  rw [probOn_true, one_mul] at h
  rw [← h]
  exact probOn_congr fun T _ ↦ by simp

/-! #### 6. Expected size as a sum of marginals (used in Lemma 4.3 step 5) -/

/-- `E[|X_p| | F] = ∑_{v ∈ X} P(v ∈ X_p | F)`. -/
theorem condExp_card (X : Finset V) (p : ℝ) (F : Finset V → Prop) [DecidablePred F] :
    condExp X p (fun A ↦ (A.card : ℝ)) F = ∑ v ∈ X, condProb X p (v ∈ ·) F := by
  simp only [condExp, condProb, ← Finset.sum_div]
  congr 1
  simp only [probOn, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  by_cases hF : F A
  · simp [hF, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hA),
      mul_comm]
  · simp [hF]

/-! #### 7. Down-sets (Prop 2.2 hypotheses, Lemma 4.3 step 2) -/

omit [DecidableEq V] in
/-- A nonempty down-set contains `∅`. -/
theorem empty_mem_of_isLowerSet {𝓕 : Finset (Finset V)}
    (h : IsLowerSet (𝓕 : Set (Finset V))) (hne : 𝓕.Nonempty) : ∅ ∈ 𝓕 := by
  obtain ⟨A, hA⟩ := hne
  exact h (Finset.empty_subset A) hA

/-- A nonempty down-set has positive probability. -/
theorem probOn_pos_of_isLowerSet {𝓕 : Finset (Finset V)} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (h : IsLowerSet (𝓕 : Set (Finset V))) (hne : 𝓕.Nonempty) : 0 < probOn X p (· ∈ 𝓕) :=
  probOn_pos_of_empty hp0 hp1 (empty_mem_of_isLowerSet h hne)

end Results

end CamposSamotij
