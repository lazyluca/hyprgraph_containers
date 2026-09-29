import CamposSamotij.Algorithm.Defs
import CamposSamotij.Prop22.Statement

/-!
# Frozen statements (the contract)

Final statements of Lemmas 4.1–4.3 and Theorem B, with `sorry` proofs.
Changing anything here requires a human decision logged in README §8.
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

end CamposSamotij
