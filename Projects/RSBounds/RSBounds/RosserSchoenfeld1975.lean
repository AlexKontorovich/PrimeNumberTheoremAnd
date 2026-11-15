import RSBounds.PolynomialZeroPairing
import RSBounds.PolynomialZeroMajorants
import RSBounds.QuarticFirst29BudgetBridges
import RSBounds.RosserWeightedBounds
import RSBounds.QuarticLowZeroBounds
import RSBounds.QuarticFirst29BudgetApplication
import RSBounds.PolynomialPsiFromZeroSums

/-!
# The actual high-zero contribution to the quartic budget

Reflection and conjugation give the factor `x + 1`. The fifth-power
ordinate sum is bounded by the proved unconditional Rosser estimate.
There is no RH premise for this high-zero bound.
-/

open Complex Finset

namespace TernaryGoldbach.RSBounds.QuarticHighZeroBounds

open TernaryGoldbach.Explicit BacklundCountIdentity QuarticFirst29BudgetNumerics

theorem C_nonneg : 0 ≤ (C : ℝ) := QuarticFirst29BudgetBridges.C_nonneg

theorem kernel_constant_eq :
    PolynomialZeroKernel.R4 PolynomialZeroMajorants.delta /
      PolynomialZeroMajorants.delta ^ 4 = (C : ℝ) := by
  simpa only [QuarticFirst29BudgetBridges.delta_cast_eq, PolynomialZeroMajorants.delta] using
    QuarticFirst29BudgetBridges.C_cast_eq_R4.symm

/-- Both actual high-zero sums satisfy the same unconditional bound. -/
theorem norm_high_sum_le (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hAT : (A : ℝ) < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => (A : ℝ) < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      (x + 1) * highWeight := by
  have hA : (0 : ℝ) < (A : ℝ) := by norm_num [A]
  have hT : 0 < T := hA.trans hAT
  have hk :
      ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => (A : ℝ) < |ρ.im|),
        (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
        (C : ℝ) * (x + 1) * WeightedZetaZeros.weightedSum (A : ℝ) T (fun t => 1 / t ^ 5) := by
    rw [← kernel_constant_eq]
    cases lower with
    | false =>
        simpa [PolynomialZeroMajorants.coefficient] using
          PolynomialZeroPairing.norm_high_sum_upper_le hT hg hx
            PolynomialZeroMajorants.delta_pos (A : ℝ)
    | true =>
        simpa [PolynomialZeroMajorants.coefficient] using
          PolynomialZeroPairing.norm_high_sum_lower_le hT hg hx
            PolynomialZeroMajorants.delta_pos PolynomialZeroMajorants.four_mul_delta_lt_one (A : ℝ)
  have ht := RosserWeightedBounds.fifth_sum_le
    (show (7 : ℝ) ≤ (A : ℝ) by norm_num [A]) hAT.le
  calc
    _ ≤ (C : ℝ) * (x + 1) *
        (RosserTailIntegrals.J (A : ℝ) + 2 * rosserR 1.588 (A : ℝ) / (A : ℝ) ^ 5) :=
      hk.trans (mul_le_mul_of_nonneg_left ht (mul_nonneg C_nonneg (by linarith)))
    _ = (x + 1) * highWeight := by
      rw [QuarticFirst29BudgetBridges.highWeight_eq]
      ring

end TernaryGoldbach.RSBounds.QuarticHighZeroBounds

/-!
# The complete finite averaged zero sum

The rectangle is split at the finite-RH height. Conjugation doubles the
certified positive low contribution; reflection has already bounded the
high contribution by `(x + 1) * highWeight`. The resulting bound applies
to the actual complex zero sums in the averaged explicit formula.
-/

open Complex Finset

namespace TernaryGoldbach.RSBounds.QuarticZeroSumBound

open TernaryGoldbach.Explicit BacklundCountIdentity QuarticFirst29BudgetNumerics

theorem norm_low_sum_le (lower : Bool) {x T : ℝ} (hx : 0 < x)
    (hRH : Goals.FiniteRH 1894439) (hAT : (A : ℝ) < T) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ (A : ℝ)),
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      Real.sqrt x * sqrtCoefficient := by
  have hA : (0 : ℝ) < (A : ℝ) := by norm_num [A]
  have hh := PolynomialZeroPairing.norm_low_sum_le_two_closed hA hAT
    (PolynomialZeroMajorants.coefficient lower x)
    (fun ρ _ => PolynomialZeroMajorants.norm_coefficient_conj lower hx ρ)
  have hp := QuarticLowZeroBounds.positive_low_sum_le lower hx hRH
  calc
    _ ≤ 2 * (Real.sqrt x * (lineWeight - ((a : ℝ) - 0.931) * bandMass)) :=
      hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ = Real.sqrt x * sqrtCoefficient := by unfold sqrtCoefficient; ring

/-- The actual finite complex sum, with every analytic multiplicity retained. -/
theorem norm_sum_le (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hRH : Goals.FiniteRH 1894439) (hAT : (A : ℝ) < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      Real.sqrt x * sqrtCoefficient + (x + 1) * highWeight := by
  classical
  have hlo := norm_low_sum_le lower (by linarith : 0 < x) hRH hAT
  have hhi := QuarticHighZeroBounds.norm_high_sum_le lower hx hAT hg
  rw [← Finset.sum_filter_add_sum_filter_not (zerosRectD zetaF T)
    (fun ρ => |ρ.im| ≤ (A : ℝ))]
  simp only [not_le]
  exact (norm_add_le _ _).trans (add_le_add hlo hhi)

/-- The normalized budget used by the psi reduction. -/
theorem norm_sum_le_budget (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hRH : Goals.FiniteRH 1894439) (hAT : (A : ℝ) < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
      x * (highWeight + sqrtCoefficient / Real.sqrt x + highWeight / x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  have hdiv : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hs0).mpr
    nlinarith [Real.sq_sqrt hx0.le]
  calc
    _ ≤ Real.sqrt x * sqrtCoefficient + (x + 1) * highWeight :=
      norm_sum_le lower hx hRH hAT hg
    _ = x * highWeight + (x / Real.sqrt x) * sqrtCoefficient + highWeight := by
      rw [hdiv]
      ring
    _ = _ := by
      field_simp [hx0.ne', hs0]

end TernaryGoldbach.RSBounds.QuarticZeroSumBound

/-!
# The b = 23 moderate-error psi table entry

The only premise is finite RH through height 1894439 for the actual zeta
function. The proof uses degree-four polynomial smoothing with the
historical delta, the certified first 29 zeros, the unconditional Rosser
count bound, and the checked scalar budget. No quantitative zero-free
region or stronger finite-RH height is assumed.
-/

open Complex Finset Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.PsiTable1975

open TernaryGoldbach.Explicit PolynomialExplicit QuarticFirst29BudgetNumerics

/-- The moderate-error estimate at its original threshold. -/
theorem psi_error_lt (hRH : Goals.FiniteRH 1894439) {x : ℝ} (hx : Real.exp 23 ≤ x) :
    |Chebyshev.psi x - x| < 0.00020211 * x := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hx1 : 1 ≤ x := by nlinarith [QuarticFirst29BudgetApplication.x_lower hx]
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  have hlarge : ∀ᶠ k : ℕ in atTop, (A : ℝ) < T k := by
    filter_upwards [eventually_ge_atTop (1894439 : ℕ)] with k hk
    have hkR : (1894439 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have ht := (hT.mem k).1
    norm_num only [A, Rat.cast_ofNat] at ⊢
    linarith
  let zeroBudget : ℝ := highWeight + sqrtCoefficient / Real.sqrt x + highWeight / x
  have hnorm (lower : Bool) : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
          x * zeroBudget := by
    filter_upwards [hlarge] with k hk
    exact QuarticZeroSumBound.norm_sum_le_budget lower hx1 hRH hk
      (PolynomialZeroCountBridge.zetaGoodHeight_of_goodHeights hT k)
  have hpsi := PolynomialPsiFromZeroSums.psi_error_of_eventually_bounded_zero_sums
    hT hx
    (by simpa [PolynomialZeroMajorants.coefficient, PolynomialZeroMajorants.delta] using hnorm false)
    (by simpa [PolynomialZeroMajorants.coefficient, PolynomialZeroMajorants.delta] using hnorm true)
  have hrelative : |Chebyshev.psi x - x| / x < 0.00020211 := by
    calc
      _ ≤ 2 * (0.0000211 : ℝ) + (Real.log (2 * Real.pi) + 0.1) / x + zeroBudget := hpsi
      _ = 2 * (delta : ℝ) + highWeight + sqrtCoefficient / Real.sqrt x +
          (highWeight + Real.log (2 * Real.pi) + 0.1) / x := by
        rw [QuarticFirst29BudgetBridges.delta_cast_eq]
        dsimp only [zeroBudget]
        ring
      _ < 0.00020211 := QuarticFirst29BudgetApplication.relativeBudget_lt hx
  exact (div_lt_iff₀ hx0).mp hrelative

/-- The original target proposition, now discharged under finite RH alone. -/
theorem proved : Goals.PsiTable1975 := by
  intro hRH x hx
  exact psi_error_lt hRH hx

end TernaryGoldbach.RSBounds.PsiTable1975

/-!
# Public interface for the b = 23 psi estimate

Finite RH through 1894439 is the sole premise. Every other analytic,
finite-zero, smoothing, and scalar input is proved in the imported chain.
-/

namespace TernaryGoldbach.RSBounds.RosserSchoenfeld1975

theorem psi_error_b23 (hRH : Goals.FiniteRH 1894439) (x : ℝ)
    (hx : Real.exp 23 ≤ x) : |Chebyshev.psi x - x| < 0.00020211 * x :=
  PsiTable1975.psi_error_lt hRH hx

end TernaryGoldbach.RSBounds.RosserSchoenfeld1975
