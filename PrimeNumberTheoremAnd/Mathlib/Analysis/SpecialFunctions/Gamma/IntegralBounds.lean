/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gamma bounds from the Euler integral

Pointwise bounds for `Real.Gamma` and `Complex.Gamma` used in finite-order estimates for
completed zeta functions. These follow from the Euler integral representation and convexity on
`[1, 2]`, without Binet's kernel.

## Main results

* `Real.Gamma.le_one_of_mem_Icc` : `Γ(x) ≤ 1` for `x ∈ [1, 2]`
* `Complex.Gamma.norm_le_Gamma_re` : `‖Γ z‖ ≤ Γ (re z)` for `0 < re z`
* `Complex.Gamma.norm_le_one` : `‖Γ z‖ ≤ 1` for `1 ≤ re z ≤ 2`

## References

* [DLMF], §5.2.1 for the Euler integral representation
-/

open Real Complex Set MeasureTheory

@[expose] public section

noncomputable section

namespace Real
namespace Gamma

/-- For `x ∈ [1, 2]`, `Γ(x) ≤ 1` since `Γ(1) = Γ(2) = 1` and the function is convex. -/
theorem le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) : Gamma x ≤ 1 := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Gamma 1 = 1 := Gamma_one
  have h2 : Gamma 2 = 1 := Gamma_two
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc
    Gamma x = Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Gamma 1 + (1 - t) * Gamma 2 := this
    _ = 1 := by rw [h1, h2]; ring

end Gamma
end Real

namespace Complex
namespace Gamma

/-- The Euler integral gives `‖Γ z‖ ≤ Γ (re z)` for `0 < re z`; compare [DLMF], §5.2.1. -/
theorem norm_le_Gamma_re {z : ℂ} (hz : 0 < z.re) : ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  have h_norm_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ = Real.exp (-t) * t ^ (z.re - 1) := by
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := by
      simpa using norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [norm_exp, hcpow]
  calc
    ‖GammaIntegral z‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ := by
          unfold GammaIntegral
          exact norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
          exact setIntegral_congr_fun measurableSet_Ioi h_norm_eq

/-- For `1 ≤ re z ≤ 2`, `‖Γ z‖ ≤ 1`. -/
theorem norm_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) : ‖Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc
    ‖Gamma z‖ ≤ Real.Gamma z.re := norm_le_Gamma_re hz_pos
    _ ≤ 1 := Real.Gamma.le_one_of_mem_Icc hlo hhi

/-- Squared form of `Complex.Gamma.norm_le_Gamma_re`. -/
theorem norm_sq_le_Gamma_re_sq {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ^ 2 ≤ (Real.Gamma z.re) ^ 2 := by
  have h := norm_le_Gamma_re hz
  have hΓ : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
  simpa [pow_two] using mul_le_mul h h (norm_nonneg _) hΓ

/-- Squared comparison against the real-axis value at `re z`. -/
theorem norm_sq_le_norm_sq_Gamma_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖Gamma z‖ ^ 2 ≤ ‖Gamma z.re‖ ^ 2 := by
  have hz_pos : 0 < z.re := by linarith
  have h := norm_sq_le_Gamma_re_sq hz_pos
  have habs : ‖Gamma (z.re : ℂ)‖ = Real.Gamma z.re := by
    rw [Gamma_ofReal z.re, norm_real]
    exact abs_of_pos (Real.Gamma_pos_of_pos hz_pos)
  rw [habs]
  exact h

end Gamma
end Complex

end
