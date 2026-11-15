/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import RSBounds.PolynomialPsi
import RSBounds.QuarticMellin
import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# The quartic smoothed prime sum is the fourth primitive of psi

This is the arithmetic bridge between the canonical truncated-power sum
`PolynomialPsi.Psi4` and the Mellin-transform formulation. Compact support
makes the prime sum finite. No zero-location or analytic prime estimate is
assumed.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.PolynomialPsiMellin

open TernaryGoldbach.Explicit PolynomialPsi QuarticMellin

/-- Compact support reduces the smoothed prime sum to its finite range. -/
theorem SsumG_quartic_eq_finite {x : ℝ} (hx : 0 < x) :
    SsumG (1 : DirichletCharacter ℂ 1) weight x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (Λ n : ℂ) * weight (n / x) := by
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  unfold SsumG
  simp only [hchar, mul_one]
  apply tsum_eq_sum
  intro n hn
  have hnf : ⌊x⌋₊ < n := by
    simp only [mem_Icc, Nat.zero_le, true_and] at hn
    omega
  have hxn : x < n := (Nat.floor_lt hx.le).1 hnf
  have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).2 (by simpa using hxn.le)
  rw [weight_eq_zero_of_one_le hratio, mul_zero]

/-- Scaling the quartic weight recovers the truncated-power primitive. -/
theorem scaled_weight_eq_quarticPrimitive {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x : ℂ) ^ 4 * weight (a / x) = (quarticPrimitive (x - a) : ℂ) := by
  have hmax : x * max (1 - a / x) 0 = max (x - a) 0 := by
    rw [mul_max_of_nonneg _ _ hx.le, mul_zero]
    congr 1
    field_simp [hx.ne'] <;> ring
  have hre : x ^ 4 * ((max (1 - a / x) 0) ^ 4 / 24) =
      quarticPrimitive (x - a) := by
    rw [quarticPrimitive, ← hmax, mul_pow]
    ring
  unfold weight
  exact_mod_cast hre

/-- The exact conversion from the Mellin smoothed prime sum to `Psi4`. -/
theorem pow_four_mul_SsumG_quartic_eq_Psi4 {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 4 * SsumG (1 : DirichletCharacter ℂ 1) weight x =
      (Psi4 x : ℂ) := by
  rw [SsumG_quartic_eq_finite hx, mul_sum]
  unfold Psi4 psi4Trunc
  push_cast
  apply sum_congr rfl
  intro n _
  calc
    (x : ℂ) ^ 4 * ((Λ n : ℂ) * weight (n / x)) =
        (Λ n : ℂ) * ((x : ℂ) ^ 4 * weight (n / x)) := by ring
    _ = (Λ n : ℂ) * (quarticPrimitive (x - n) : ℂ) := by
      rw [scaled_weight_eq_quarticPrimitive hx]

end TernaryGoldbach.RSBounds.PolynomialPsiMellin
