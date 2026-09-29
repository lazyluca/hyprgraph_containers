import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Real-analysis auxiliary lemma (M6)

For `0 < p ≤ δ < 1`: `(1-p)^n ≤ (1-δ)^m → δ m ≤ p n`. See README §4.4.

This is the last step of the paper's proof of Lemma 4.2 (p. 13): from
`(1 - p)^|V| ≤ (1 - δ)^|S|` (display (4)) it concludes `δ|S| ≤ p|V|`.

## Statements

* `mul_log_one_sub_le`: `p log(1 - δ) ≤ δ log(1 - p)` for `0 < p ≤ δ < 1` (concavity of `log`).
  Both results below follow from it.
* `one_sub_rpow_inv_antitoneOn`: the paper's auxiliary fact that
  `x ↦ (1 - x)^(1/x)` is decreasing on `(0, 1)`.
* `delta_mul_le_of_pow_le`: the lemma used in Lemma 4.2.

## Proof routes (the README route is the one formalized)

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

/-- For `0 < p ≤ δ < 1`: `p log(1 - δ) ≤ δ log(1 - p)`. Write `1 - p` as the convex combination
`(1 - p/δ) · 1 + (p/δ) · (1 - δ)` and use concavity of `log` on `(0, ∞)`. -/
theorem mul_log_one_sub_le {p δ : ℝ} (hp : 0 < p) (hpδ : p ≤ δ) (hδ : δ < 1) :
    p * Real.log (1 - δ) ≤ δ * Real.log (1 - p) := by
  have hδ0 : 0 < δ := hp.trans_le hpδ
  set t := p / δ with ht
  have ht0 : 0 ≤ t := div_nonneg hp.le hδ0.le
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ((div_le_one hδ0).mpr hpδ)
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr (sub_pos.mpr hδ)) ht1 ht0 (by ring)
  have hcomb : (1 - t) • (1 : ℝ) + t • (1 - δ) = 1 - p := by
    simp only [smul_eq_mul, ht]; field_simp; ring
  rw [hcomb, smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
  have := mul_le_mul_of_nonneg_left hconc hδ0.le
  rwa [ht, ← mul_assoc, mul_div_cancel₀ _ hδ0.ne'] at this

/-- The map `x ↦ (1 - x)^(1/x)` is decreasing on `(0, 1)` (paper, proof of Lemma 4.2).
Equivalently, `x ↦ -log(1 - x)/x` is increasing on `(0, 1)`. -/
theorem one_sub_rpow_inv_antitoneOn :
    AntitoneOn (fun x : ℝ ↦ (1 - x) ^ (1 / x)) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  simp only
  rw [Real.rpow_def_of_pos (sub_pos.mpr hy.2), Real.rpow_def_of_pos (sub_pos.mpr hx.2),
    Real.exp_le_exp, mul_one_div, mul_one_div, div_le_div_iff₀ hy.1 hx.1]
  have := mul_log_one_sub_le hx.1 hxy hy.2
  linarith

/-- For `0 < p ≤ δ < 1` and `n m : ℕ`: if `(1-p)^n ≤ (1-δ)^m` then `δ m ≤ p n`.
Used with `n = |V|`, `m = |S|` to get Lemma 4.2, `δ|S| ≤ p|V|`. -/
theorem delta_mul_le_of_pow_le {p δ : ℝ} {n m : ℕ} (hp : 0 < p) (hpδ : p ≤ δ) (hδ : δ < 1)
    (h : (1 - p) ^ n ≤ (1 - δ) ^ m) : δ * m ≤ p * n := by
  have hp1 : 0 < 1 - p := by linarith
  have hδ1 : 0 < 1 - δ := by linarith
  -- `n log(1-p) ≤ m log(1-δ)`
  have hlog := Real.log_le_log (pow_pos hp1 n) h
  rw [Real.log_pow, Real.log_pow] at hlog
  have hL : Real.log (1 - p) < 0 := Real.log_neg hp1 (by linarith)
  have hc := mul_log_one_sub_le hp hpδ hδ
  -- `p n log(1-p) ≤ p m log(1-δ) ≤ δ m log(1-p)`, and `log(1-p) < 0`
  have h1 := mul_le_mul_of_nonneg_left hlog hp.le
  have h2 := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  by_contra hcon
  replace hcon := not_le.mp hcon
  nlinarith [mul_pos_of_neg_of_neg hL (sub_neg.mpr hcon)]

end CamposSamotij
