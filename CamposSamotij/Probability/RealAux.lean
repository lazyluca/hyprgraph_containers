import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-analysis auxiliary lemma (M6)

For `0 < p ≤ δ < 1`: `(1-p)^n ≤ (1-δ)^m → δ m ≤ p n`. See README §4.4.

This is the last step of the paper's proof of Lemma 4.2 (p. 13): from
`(1 - p)^|V| ≤ (1 - δ)^|S|` (display (4)) it concludes `δ|S| ≤ p|V|`.

## Statements

* `one_sub_rpow_inv_antitoneOn`: the paper's auxiliary fact that
  `x ↦ (1 - x)^(1/x)` is decreasing on `(0, 1)`.
* `delta_mul_le_of_pow_le`: the lemma used in Lemma 4.2.

## Proof routes (not yet formalized)

* Paper route: if `δ m > p n`, then
  `(1-δ)^m < (1-δ)^(p n / δ) = ((1-δ)^(1/δ))^(p n) ≤ ((1-p)^(1/p))^(p n) = (1-p)^n`,
  using `one_sub_rpow_inv_antitoneOn` with `p ≤ δ`. This contradicts the hypothesis.
  For `n = 0` the hypothesis forces `m = 0`.
* README route: take logs. With `g(x) = -log(1-x)/x`, the hypothesis reads
  `n p g(p) ≥ m δ g(δ)`, and `g` is monotone on `(0,1)` because `-log(1-x)` is convex
  and vanishes at `0`. Mathlib has `ConvexOn.secant_mono_aux*` and `strictConcaveOn_log_Ioi`.
  Monotonicity of `g` is the same fact as `one_sub_rpow_inv_antitoneOn`, after taking logs.
-/

namespace CamposSamotij

/-- The map `x ↦ (1 - x)^(1/x)` is decreasing on `(0, 1)` (paper, proof of Lemma 4.2).
Equivalently, `x ↦ -log(1 - x)/x` is increasing on `(0, 1)`. -/
theorem one_sub_rpow_inv_antitoneOn :
    AntitoneOn (fun x : ℝ ↦ (1 - x) ^ (1 / x)) (Set.Ioo 0 1) := by
  sorry

/-- For `0 < p ≤ δ < 1` and `n m : ℕ`: if `(1-p)^n ≤ (1-δ)^m` then `δ m ≤ p n`.
Used with `n = |V|`, `m = |S|` to get Lemma 4.2, `δ|S| ≤ p|V|`. -/
theorem delta_mul_le_of_pow_le {p δ : ℝ} {n m : ℕ} (hp : 0 < p) (hpδ : p ≤ δ) (hδ : δ < 1)
    (h : (1 - p) ^ n ≤ (1 - δ) ^ m) : δ * m ≤ p * n := by
  sorry

end CamposSamotij
