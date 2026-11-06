import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# The Euler-product lower bound at Backlund's center

This file proves the exact symbolic lower bound
`‖ζ(2σ)‖ / ‖ζ(σ)‖ ≤ ‖ζ(σ + it)‖` for `σ > 1`.
It introduces no numerical assumption about the ratio at `σ = 5/4`.

Rosser (1941), p. 224, prints the denominator `3.425`. The exact real
zeta ratio is slightly larger; the numerical audit in
`verification/backlund-center-rational.json` uses an independent rational
integral-test computation. That computation is not a Lean theorem.
-/

open Complex Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds

private theorem center_factor_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hz : ‖z‖ = a) :
    ‖(1 - (a : ℂ) ^ 2)⁻¹‖ ≤
      ‖(1 - (a : ℂ))⁻¹‖ * ‖(1 - z)⁻¹‖ := by
  have h1 : 0 < 1 - a := sub_pos.mpr ha1
  have h2 : 0 < 1 - a ^ 2 := by nlinarith
  have hz1 : 0 < ‖(1 : ℂ) - z‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    have : a = 1 := by simpa [he] using hz.symm
    linarith
  have htri : ‖(1 : ℂ) - z‖ ≤ 1 + a := by
    simpa only [norm_one, hz] using norm_sub_le (1 : ℂ) z
  have hreal1 : ‖(1 : ℂ) - (a : ℂ)‖ = 1 - a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg h1.le]
  have hreal2 : ‖(1 : ℂ) - (a : ℂ) ^ 2‖ = 1 - a ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_of_nonneg h2.le]
  rw [norm_inv, norm_inv, norm_inv, hreal1, hreal2, ← mul_inv]
  apply (inv_le_inv₀ h2 (mul_pos h1 hz1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left htri h1.le]

/-- A lower bound for zeta in the absolutely convergent half-plane.
The norms of the two real zeta values can equivalently be written as
their positive real values. -/
theorem zeta_norm_lower_euler_ratio {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ / ‖riemannZeta (s.re : ℂ)‖ ≤
      ‖riemannZeta s‖ := by
  have hσ : 1 < ((s.re : ℂ)).re := by simpa using hs
  have h2σ : 1 < (((2 * s.re : ℝ) : ℂ)).re := by simpa using (show 1 < 2 * s.re by linarith)
  have hprod := (riemannZeta_eulerProduct_hasProd hσ).norm.mul
    (riemannZeta_eulerProduct_hasProd hs).norm
  have hprod2 := (riemannZeta_eulerProduct_hasProd h2σ).norm
  have hfactor (p : Nat.Primes) :
      ‖(1 - (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)))⁻¹‖ ≤
        ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ *
          ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
    have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hp0 : 0 < (p : ℝ) := by linarith
    let a : ℝ := (p : ℝ) ^ (-s.re)
    have ha : 0 ≤ a := Real.rpow_nonneg hp0.le _
    have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    have hpow : (p : ℂ) ^ (-(s.re : ℂ)) = (a : ℂ) := by
      simpa only [a, Complex.ofReal_neg, Complex.ofReal_natCast] using
        (Complex.ofReal_cpow hp0.le (-s.re)).symm
    have hpow2 : (p : ℂ) ^ (-((2 * s.re : ℝ) : ℂ)) = (a : ℂ) ^ 2 := by
      rw [show -((2 * s.re : ℝ) : ℂ) = -(s.re : ℂ) * (2 : ℕ) by push_cast; ring,
        Complex.cpow_mul_nat, hpow]
    have hz : ‖(p : ℂ) ^ (-s)‖ = a := by
      simpa only [a, Complex.neg_re, Complex.ofReal_natCast] using
        Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
    rw [hpow, hpow2]
    exact center_factor_le ha ha1 hz
  have hlim : ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤
      ‖riemannZeta (s.re : ℂ)‖ * ‖riemannZeta s‖ := by
    apply le_of_tendsto_of_tendsto' hprod2 hprod
    intro S
    exact Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => hfactor p)
  have hζ : 0 < ‖riemannZeta (s.re : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hσ)
  exact (div_le_iff₀ hζ).mpr (by simpa only [mul_comm] using hlim)

/-- Exact symbolic lower bound at the center used by Rosser and Backlund. -/
theorem zeta_norm_lower_five_fourths_ratio (T : ℝ) :
    ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤
      ‖riemannZeta (((5 / 4 : ℝ) : ℂ) + T * Complex.I)‖ := by
  have h := zeta_norm_lower_euler_ratio
    (s := ((5 / 4 : ℝ) : ℂ) + T * Complex.I) (by simp; norm_num)
  norm_num at h ⊢
  exact h

end TernaryGoldbach.RSBounds
