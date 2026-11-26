import RSBounds.PolynomialAveragedFormula
import RSBounds.PolynomialRemainderBound

/-!
# From the actual finite averaged zero sums to a bound for psi

The upper and lower quartic formulas use the same good-height sequence.
A uniform eventual bound for their finite zero sums passes to their limits.
The already proved remainder bound and polynomial sandwich then give the
unsmoothed error. The only outstanding analytic estimate in the final
theorem is the explicitly stated bound on those actual finite sums.
-/

open Complex Finset Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.PolynomialPsiFromZeroSums

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialAveraged
open PolynomialPsi PolynomialRemainderBound

theorem norm_log_two_pi : ‖Complex.log (2 * Real.pi)‖ = Real.log (2 * Real.pi) := by
  have hcast : Complex.log (2 * Real.pi) = (Real.log (2 * Real.pi) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (Complex.ofReal_log (show 0 ≤ 2 * Real.pi by positivity)).symm
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))

/-- Recover the real smoothing error from the limit of its complex zero sum. -/
theorem smoothing_error_of_norm_bound {m s B C : ℝ} {r : ℂ}
    (hzero : ‖(m : ℂ) - (s : ℂ) - r - Complex.log (2 * Real.pi)‖ ≤ B)
    (hr : ‖r‖ ≤ C) : |s - m| ≤ B + C + Real.log (2 * Real.pi) := by
  let z : ℂ := (m : ℂ) - (s : ℂ) - r - Complex.log (2 * Real.pi)
  have hz : ‖z‖ ≤ B := hzero
  have he : ((s - m : ℝ) : ℂ) = -(z + r + Complex.log (2 * Real.pi)) := by
    dsimp [z]
    push_cast
    ring
  calc
    |s - m| = ‖((s - m : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖z + r + Complex.log (2 * Real.pi)‖ := by rw [he, norm_neg]
    _ ≤ ‖z‖ + ‖r‖ + ‖Complex.log (2 * Real.pi)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B + C + Real.log (2 * Real.pi) := by
      rw [norm_log_two_pi]
      exact add_le_add (add_le_add hz hr) le_rfl

/-- The upper smoothed error from an eventual bound on its actual finite zero sums. -/
theorem upper_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h B C : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N)
    (hzero : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ‖ ≤ B)
    (hr : ‖leftRemainder x h‖ ≤ C) :
    |psiUpper N x h - (x + 2 * h)| ≤ B + C + Real.log (2 * Real.pi) := by
  have hlim := explicit_formula_upper_at_heights hT hx hh hN
  exact smoothing_error_of_norm_bound (le_of_tendsto hlim.norm hzero) hr

/-- The lower smoothed error from an eventual bound on its actual finite zero sums. -/
theorem lower_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h B C : ℝ} (hx : 4 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N)
    (hzero : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 4 * h) h ρ‖ ≤ B)
    (hr : ‖leftRemainder (x - 4 * h) h‖ ≤ C) :
    |psiLower N x h - (x - 2 * h)| ≤ B + C + Real.log (2 * Real.pi) := by
  have hlim := explicit_formula_lower_at_heights hT hx hh hN
  exact smoothing_error_of_norm_bound (le_of_tendsto hlim.norm hzero) hr

/-- The historical degree-four smoothing parameters, with only an explicit
eventual finite-zero-sum budget left to supply. The sums have the actual
contour multiplicities and the actual normalized quartic kernel. -/
theorem psi_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x zeroBudget : ℝ} (hx : Real.exp 23 ≤ x)
    (hupper : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) *
          zeroCoefficient x (0.0000211 * x) ρ‖ ≤ x * zeroBudget)
    (hlower : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) *
          zeroCoefficient (x - 4 * (0.0000211 * x)) (0.0000211 * x) ρ‖ ≤
            x * zeroBudget) :
    |Chebyshev.psi x - x| / x ≤
      2 * (0.0000211 : ℝ) + (Real.log (2 * Real.pi) + 0.1) / x + zeroBudget := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hh : 0 < (0.0000211 : ℝ) * x := by positivity
  have hshift : 4 * ((0.0000211 : ℝ) * x) < x := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 4 * ((0.0000211 : ℝ) * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hup := upper_error_of_eventually_bounded_zero_sums hT hx0 hh hN hupper
    (norm_upper_leftRemainder_lt hx).le
  have hlo := lower_error_of_eventually_bounded_zero_sums hT hshift hh hNx hlower
    (norm_lower_leftRemainder_lt hx).le
  have hpsi := psi_error_of_polynomial_errors hx0.le hh hN hup hlo
  calc
    _ ≤ (x * zeroBudget + 0.1 + Real.log (2 * Real.pi) + 2 * (0.0000211 * x)) / x :=
      div_le_div_of_nonneg_right hpsi hx0.le
    _ = _ := by
      field_simp [hx0.ne']
      ring

end TernaryGoldbach.RSBounds.PolynomialPsiFromZeroSums
