import CamposSamotij.Hypergraph.Updates
import CamposSamotij.Probability.RandomSubset

/-!
# The deterministic algorithm (M4)

`State`, `eligible`, `step`, `run` (fuel `|V|`), stopping, termination,
`container`. No probability *proofs* here. See README §4.2.
-/

-- note here a discrepancy with the definition of the algorithm in the paper
-- Give a set a hyprgraph H (our definition), let V be its vertex set, 0 < p ≤ δ < 1
-- assume some total ordering of these vertices1
-- container algorithm
-- input: an indepedet set I in H
-- output: a fingerprint S and a container C, both in V

-- Let V_p be the p-random subset of V

-- (1) Start: H_0 = H S_0 = ∅
-- (2)
-- (a) for i; if there is a vertex that is not a singleton in the edge set
-- and Pr(v ∈ V_p | V_p ∈ I(H_i)) < (1 - δ)p then let v_i be such vertex, otherwise J := i and stop
-- returning S_J and C_J
-- (b) if v_i belongs to I, S_i belongs to S_{i+1} and update the the hyprgraph
-- (c) if not, the fingerprint is the same and add {v} as an edge
-- (3)when over return S_J and C = {v : {v} ∉ H_J}

/-!
## The algorithm (paper, §4.1)

Input: a hypergraph `H` on `V`, parameters `p, δ`, and `I ∈ 𝓘(H)`.

1. `H₀ := H`, `S₀ := ∅`.
2. For `i = 0, 1, …`:
   (a) if some `v ∈ V \ Sᵢ` has `{v} ∉ Hᵢ` and `P(v ∈ V_p | V_p ∈ 𝓘(Hᵢ)) < (1 - δ)p`,
       let `vᵢ` be the **least** such vertex; otherwise set `J := i` and stop;
   (b) if `vᵢ ∈ I`: `Sᵢ₊₁ := Sᵢ ∪ {vᵢ}`, `Hᵢ₊₁ := Hᵢ ∪ ∂_{vᵢ} Hᵢ`;
   (c) if `vᵢ ∉ I`: `Sᵢ₊₁ := Sᵢ`, `Hᵢ₊₁ := Hᵢ ∪ {{vᵢ}}`.
3. Return `S := S_J` and `C := {v : {v} ∉ H_J}`.

## Deviations from the paper (`divergence.md` D3, D4)

* The paper says "let `vᵢ` be *some* such vertex". We take the least one in the linear
  order on `V` (README §7, **Decided**). All that matters is that `vᵢ` is a function of
  `(Hᵢ, Sᵢ)` (`nextVertex`); the input `I` is used only through the bit `[vᵢ ∈ I]`.
* The loop is `Nat.iterate step |V|`, with `step` the identity once stopped (README §7,
  **Decided**). `run_stopped` shows that `|V|` steps suffice.
* The in-code sketch above (step (a)) only asks `{v} ∉ Hᵢ`. The paper also asks
  `v ∉ Sᵢ`. We follow the paper (CLAUDE.md rule 6). Without `v ∉ Sᵢ` the potential
  argument for termination fails.
* Vertex types carry `[Fintype V] [LinearOrder V]` only. Decidable equality comes from the
  order, so there is a single `DecidableEq V` instance (no diamond). The files below this one
  (`Hypergraph/`, `Probability/`) take `[DecidableEq V]` and are instantiated from the order.

## Definitions

* `State V`: the pair `(Hᵢ, Sᵢ)`.
* `condProbIndep p H v`: `P(v ∈ V_p | V_p ∈ 𝓘(H))`.
* `Eligible p δ st v`: the condition in step (2a).
* `eligibleSet`, `nextVertex`: the eligible vertices and the chosen `vᵢ`.
* `update I st v`: steps (2b)/(2c). `step`, `run`: the loop.
* `container H`: `{v : {v} ∉ H}`. `fingerprint`, `containerOf`: the outputs `S` and `C`.

## Results

* `nextVertex_eq_none_iff`, `eligible_nextVertex`: characterization of the choice.
* `step_of_stopped`, `step_of_nextVertex`: unfolding `step`.
* `potential_step_lt`: each non-trivial step drops `#{v : v ∉ Sᵢ, {v} ∉ Hᵢ}` (termination).
* `run_stopped`: after `|V|` steps no vertex is eligible, i.e. `run` is the stage `J`.
-/

namespace CamposSamotij

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The state `(Hᵢ, Sᵢ)` of the algorithm at a stage `i`. -/
structure State (V : Type*) where
  /-- The current hypergraph `Hᵢ`. -/
  H : Hypergraph V
  /-- The current fingerprint `Sᵢ`. -/
  S : Finset V

/-- The initial state `(H₀, S₀) = (H, ∅)`. -/
def State.init (H : Hypergraph V) : State V := ⟨H, ∅⟩

/-- `P(v ∈ V_p | V_p ∈ 𝓘(H))`, with `V_p` the `p`-random subset of the whole vertex set. -/
noncomputable def condProbIndep (p : ℝ) (H : Hypergraph V) (v : V) : ℝ :=
  condProb Finset.univ p (v ∈ ·) (IsIndep H)

/-- Step (2a): `v` is *eligible* at state `(Hᵢ, Sᵢ)` if `v ∉ Sᵢ`, `{v} ∉ Hᵢ` and
`P(v ∈ V_p | V_p ∈ 𝓘(Hᵢ)) < (1 - δ)p`. -/
def Eligible (p δ : ℝ) (st : State V) (v : V) : Prop :=
  v ∉ st.S ∧ {v} ∉ st.H ∧ condProbIndep p st.H v < (1 - δ) * p

open Classical in
/-- The set of eligible vertices at state `st`. -/
noncomputable def eligibleSet (p δ : ℝ) (st : State V) : Finset V :=
  Finset.univ.filter (Eligible p δ st)

/-- The vertex `vᵢ` chosen in step (2a): the least eligible vertex, or `none` if there is
none (then the algorithm stops). It depends only on `(Hᵢ, Sᵢ)`, not on `I`. -/
noncomputable def nextVertex (p δ : ℝ) (st : State V) : Option V :=
  if h : (eligibleSet p δ st).Nonempty then some ((eligibleSet p δ st).min' h) else none

/-- Steps (2b)/(2c): process the chosen vertex `v` against the input `I`. -/
def update (I : Finset V) (st : State V) (v : V) : State V :=
  if v ∈ I then ⟨st.H ∪ link st.H v, insert v st.S⟩ else ⟨st.H ∪ {{v}}, st.S⟩

/-- One round of the loop (2). Once no vertex is eligible, it is the identity. -/
noncomputable def step (p δ : ℝ) (I : Finset V) (st : State V) : State V :=
  match nextVertex p δ st with
  | none => st
  | some v => update I st v

/-- The algorithm with input `I`: `|V|` rounds from `(H, ∅)`. By `run_stopped` this is the
final stage `(H_J, S_J)`. -/
noncomputable def run (p δ : ℝ) (H : Hypergraph V) (I : Finset V) : State V :=
  (step p δ I)^[Fintype.card V] (State.init H)

/-- The container `C = {v ∈ V : {v} ∉ H}` read off a hypergraph (step (3)). -/
def container (H : Hypergraph V) : Finset V :=
  Finset.univ.filter fun v ↦ {v} ∉ H

/-- The fingerprint `S = S_J` output on input `I`. -/
noncomputable def fingerprint (p δ : ℝ) (H : Hypergraph V) (I : Finset V) : Finset V :=
  (run p δ H I).S

/-- The container `C = {v : {v} ∉ H_J}` output on input `I`. -/
noncomputable def containerOf (p δ : ℝ) (H : Hypergraph V) (I : Finset V) : Finset V :=
  container (run p δ H I).H

/-- Termination potential: `#{v : v ∉ Sᵢ, {v} ∉ Hᵢ}`. -/
def potential (st : State V) : ℕ :=
  (Finset.univ.filter fun v ↦ v ∉ st.S ∧ {v} ∉ st.H).card

/-! ### Basic lemmas -/

section Lemmas

variable {p δ : ℝ} {I : Finset V} {st : State V} {v : V}

@[simp]
theorem mem_container {H : Hypergraph V} : v ∈ container H ↔ {v} ∉ H := by
  simp [container]

@[simp]
theorem mem_eligibleSet : v ∈ eligibleSet p δ st ↔ Eligible p δ st v := by
  classical
  simp [eligibleSet]

theorem nextVertex_eq_none_iff : nextVertex p δ st = none ↔ ∀ v, ¬ Eligible p δ st v := by
  unfold nextVertex
  split_ifs with h
  · obtain ⟨v, hv⟩ := h
    simp only [false_iff, not_forall, not_not]
    exact ⟨v, mem_eligibleSet.mp hv⟩
  · simp only [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem,
      mem_eligibleSet] at h
    simpa using h

/-- The chosen vertex is eligible. -/
theorem eligible_nextVertex (h : nextVertex p δ st = some v) : Eligible p δ st v := by
  unfold nextVertex at h
  split_ifs at h with hne
  cases h
  exact mem_eligibleSet.mp (Finset.min'_mem _ hne)

/-- The chosen vertex is the least eligible one. -/
theorem nextVertex_le (h : nextVertex p δ st = some v) {w : V} (hw : Eligible p δ st w) :
    v ≤ w := by
  unfold nextVertex at h
  split_ifs at h with hne
  cases h
  exact Finset.min'_le _ _ (mem_eligibleSet.mpr hw)

theorem step_of_stopped (h : nextVertex p δ st = none) : step p δ I st = st := by
  simp [step, h]

theorem step_of_nextVertex (h : nextVertex p δ st = some v) :
    step p δ I st = update I st v := by
  simp [step, h]

omit [Fintype V] in
theorem update_of_mem (hv : v ∈ I) :
    update I st v = ⟨st.H ∪ link st.H v, insert v st.S⟩ := by
  simp [update, hv]

omit [Fintype V] in
theorem update_of_notMem (hv : v ∉ I) : update I st v = ⟨st.H ∪ {{v}}, st.S⟩ := by
  simp [update, hv]

/-! ### Termination -/

/-- A non-trivial step strictly decreases the potential: `vᵢ` leaves the potential set
(it joins `S` or `{vᵢ}` becomes an edge), and the set only shrinks since `H`, `S` grow. -/
theorem potential_step_lt (h : nextVertex p δ st = some v) :
    potential (step p δ I st) < potential st := by
  obtain ⟨hvS, hvH, -⟩ := eligible_nextVertex h
  rw [step_of_nextVertex h]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨v, by simp [hvS, hvH], ?_⟩
    by_cases hvI : v ∈ I <;> simp [update, hvI]
  · intro w
    by_cases hvI : v ∈ I <;> simp +contextual [update, hvI]

/-- If the potential is at most `n`, then after `n` steps no vertex is eligible. -/
theorem nextVertex_iterate_eq_none :
    ∀ (n : ℕ) (st : State V), potential st ≤ n →
      nextVertex p δ ((step p δ I)^[n] st) = none
  | 0, st, h => by
    rw [Function.iterate_zero_apply, nextVertex_eq_none_iff]
    rintro v ⟨hvS, hvH, -⟩
    have : v ∈ Finset.univ.filter fun v ↦ v ∉ st.S ∧ {v} ∉ st.H := by simp [hvS, hvH]
    exact Finset.notMem_empty v (Finset.card_eq_zero.mp (Nat.le_zero.mp h) ▸ this)
  | n + 1, st, h => by
    rw [Function.iterate_succ_apply]
    cases hv : nextVertex p δ st with
    | none =>
      rw [step_of_stopped hv, Function.iterate_fixed (step_of_stopped hv)]
      exact hv
    | some v =>
      exact nextVertex_iterate_eq_none n _ (Nat.lt_succ_iff.mp ((potential_step_lt hv).trans_le h))

/-- **Termination** (paper, §4.2: `J ≤ |V|`): after `|V|` rounds no vertex is eligible,
so `run` is the final stage `(H_J, S_J)`. -/
theorem run_stopped (H : Hypergraph V) : nextVertex p δ (run p δ H I) = none :=
  nextVertex_iterate_eq_none _ _ (Finset.card_le_univ _)

end Lemmas

end CamposSamotij
