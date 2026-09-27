import CamposSamotij.Hypergraph.Updates

/-!
# Toy examples

`decide`-checkable examples on 3–4 vertices to sanity-check definitions
(`link`, `addSingleton`, …).
-/

namespace CamposSamotij.Examples

/-- `H = {{0,1}, {1,2}, {2}}` on `V = Fin 3`. -/
def H₀ : Hypergraph (Fin 3) := {{0, 1}, {1, 2}, {2}}

-- ∂₁ H₀ = {{0}, {2}}: edges through 1, with 1 removed.
example : link H₀ 1 = {{0}, {2}} := by decide
-- ∂₀ H₀ = {{1}}.
example : link H₀ 0 = {{1}} := by decide
-- 𝓘(H₀) = {∅, {0}, {1}}: every set containing 2 or {0,1} is dependent.
example : indepSets H₀ = {∅, {0}, {1}} := by decide
-- {2} ∈ H₀, so {2} is not independent.
example : ¬ IsIndep H₀ {2} := by decide
-- H₀ covers {{0,1,2}} but not {{0}}.
example : Covers H₀ {{0, 1, 2}} := by decide
example : ¬ Covers H₀ {{0}} := by decide

end CamposSamotij.Examples
