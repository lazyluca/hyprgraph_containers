import CamposSamotij.Algorithm.Defs
import CamposSamotij.Prop22.Statement

/-!
# Frozen statements (the contract)

Final statements of Lemmas 4.1–4.3 and Theorem B.
Changing anything here requires a human decision logged in README §8.

Statements are `Prop`-valued definitions (`TheoremBStatement`, …). The proofs live in
their milestone files (`theoremB : Prop22Statement → TheoremBStatement` in `TheoremB.lean`),
so a statement and its proof never share a name.
-/

-- Theorem B (paper, p. 3), verbatim:
-- Let H be a hypergraph with a finite vertex set V. For all reals δ and p satisfying
-- 0 < p ≤ δ < 1, there exists a family 𝒮 ⊆ 2^V and functions
--   g : 𝓘(H) → 𝒮   and   f : 𝒮 → 2^V
-- such that:
-- (a) For each I ∈ 𝓘(H), we have g(I) ⊆ I ⊆ f(g(I)).
-- (b) Each S ∈ 𝒮 has at most p|V|/δ elements.
-- (c) For every S ∈ 𝒮, letting C := f(S),  P(S ∪ C_p ∈ 𝓘(H)) ≥ (1 - p)^{δ|C \ S|}.

namespace CamposSamotij

universe u

/-! ### Theorem B (the "hard-core" container lemma)

Formalization choices (see `divergence.md` D8):

* `g` and `f` are total functions `Finset V → Finset V`. "`g : 𝓘(H) → 𝒮`" becomes
  `∀ I, IsIndep H I → g I ∈ 𝒮`, and only the values of `f` on `𝒮` are constrained. Restricting
  them gives the paper's functions. Conversely, any pair of paper functions extends to total
  functions.
* `P(S ∪ C_p ∈ 𝓘(H))` is `probOn C p (fun A ↦ IsIndep H (S ∪ A))`, and the exponent
  `δ|C \ S|` is a real number (`Real.rpow`).
* (b) and (c) quantify over `S ∈ 𝒮`, as in the paper (this resolves divergence D7).
-/

/-- **Theorem B** (Campos–Samotij), for vertex types in universe `u`.
**Frozen** (reviewed against the paper and approved, 2026-09-29). -/
def TheoremBStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [LinearOrder V] (H : Hypergraph V) (p δ : ℝ),
    0 < p → p ≤ δ → δ < 1 →
    ∃ (𝒮 : Finset (Finset V)) (g f : Finset V → Finset V),
      -- `g : 𝓘(H) → 𝒮`
      (∀ I, IsIndep H I → g I ∈ 𝒮) ∧
      -- (a) `g(I) ⊆ I ⊆ f(g(I))`
      (∀ I, IsIndep H I → g I ⊆ I ∧ I ⊆ f (g I)) ∧
      -- (b) `|S| ≤ p|V|/δ`
      (∀ S ∈ 𝒮, (S.card : ℝ) ≤ p * Fintype.card V / δ) ∧
      -- (c) `P(S ∪ C_p ∈ 𝓘(H)) ≥ (1 - p)^{δ|C \ S|}`, with `C = f(S)`
      (∀ S ∈ 𝒮, (1 - p) ^ (δ * ((f S \ S).card : ℝ)) ≤
        probOn (f S) p (fun A ↦ IsIndep H (S ∪ A)))

end CamposSamotij
