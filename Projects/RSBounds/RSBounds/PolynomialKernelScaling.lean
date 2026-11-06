import RSBounds.PolynomialAveragedFormula

/-! Exact dilation identities for the fourfold additive zero coefficient. -/

open Complex

namespace TernaryGoldbach.RSBounds.PolynomialKernelScaling

open PolynomialZeroKernel PolynomialAveraged

theorem antiderivative_four_mul {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (ρ : ℂ) :
    antiderivative ρ 4 (x * y) =
      (x : ℂ) ^ (ρ + 4) * antiderivative ρ 4 y := by
  simp only [antiderivative, Nat.cast_ofNat, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le hy]
  ring

theorem forwardDiff_four_dilate (f : ℝ → ℂ) (x y δ : ℝ) :
    forwardDiff (δ * x) 4 f (x * y) =
      forwardDiff δ 4 (fun t => f (x * t)) y := by
  rw [forwardDiff_four, forwardDiff_four]
  rw [show x * y + 4 * (δ * x) = x * (y + 4 * δ) by ring,
    show x * y + 3 * (δ * x) = x * (y + 3 * δ) by ring,
    show x * y + 2 * (δ * x) = x * (y + 2 * δ) by ring,
    show x * y + δ * x = x * (y + δ) by ring]

/-- Dilation is exact before any zero-location estimate is used. -/
theorem zeroCoefficient_dilate {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    zeroCoefficient (x * y) (δ * x) ρ =
      (x : ℂ) ^ ρ *
        (forwardDiff δ 4 (antiderivative ρ 4) y / (δ : ℂ) ^ 4) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  rw [zeroCoefficient, forwardDiff_four_dilate, forwardDiff_four, forwardDiff_four]
  rw [antiderivative_four_mul hx (by linarith),
    antiderivative_four_mul hx (by linarith),
    antiderivative_four_mul hx (by linarith),
    antiderivative_four_mul hx (by linarith), antiderivative_four_mul hx hy.le]
  rw [Complex.cpow_add _ _ hxc, Complex.cpow_ofNat]
  push_cast
  field_simp [hxc, hδc]
  <;> ring

theorem zeroCoefficient_upper {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (ρ : ℂ) :
    zeroCoefficient x (δ * x) ρ = (x : ℂ) ^ ρ * upperKernel δ ρ := by
  simpa only [mul_one, upperKernel_eq_normalized_difference] using
    zeroCoefficient_dilate hx (by norm_num : (0 : ℝ) < 1) hδ ρ

theorem zeroCoefficient_lower {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ4 : 4 * δ < 1) (ρ : ℂ) :
    zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ =
      (x : ℂ) ^ ρ *
        (forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ) / (δ : ℂ) ^ 4) := by
  rw [show x - 4 * (δ * x) = x * (1 - 4 * δ) by ring]
  exact zeroCoefficient_dilate hx (by linarith) hδ ρ

theorem norm_zeroCoefficient_dilate {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    ‖zeroCoefficient (x * y) (δ * x) ρ‖ =
      x ^ ρ.re * ‖forwardDiff δ 4 (antiderivative ρ 4) y / (δ : ℂ) ^ 4‖ := by
  rw [zeroCoefficient_dilate hx hy hδ, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]

end TernaryGoldbach.RSBounds.PolynomialKernelScaling
