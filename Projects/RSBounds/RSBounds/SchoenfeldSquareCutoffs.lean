import RSBounds.SchoenfeldReciprocalSquare
import RSBounds.PolynomialZeroPairing

/-!
# Public finite-cutoff forms of Schoenfeld's reciprocal-square bound

Conjugation and actual analytic multiplicities are preserved. No height is
assumed to avoid zero ordinates, and no RH hypothesis is present.
-/

open Complex Finset
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.SchoenfeldReciprocalSquare

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge

/-- The all-ordinate contour sum is uniformly bounded, at any positive height. -/
theorem rectangle_reciprocal_square_sum_lt {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2) < 0.0463 := by
  have h := finite_zeta_reciprocal_square_sum_lt (zerosRectD zetaF T)
    (fun ρ hρ => ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1)
  convert h using 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [multRectD_zetaF_eq_analyticOrder hT hρ]

/-- The inclusive positive-ordinate sum is less than half the all-ordinate bound. -/
theorem positive_reciprocal_square_sum_lt {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ closedPositiveZeros T,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im ^ 2) < 0.02315 := by
  classical
  let U := T + 1
  have hU : 0 < U := by dsimp [U]; linarith
  have hTU : T < U := by dsimp [U]; linarith
  let S := (zerosRectD zetaF U).filter (fun ρ => |ρ.im| ≤ T)
  have hs : (∑ ρ ∈ S, (multRectD zetaF U ρ : ℝ) / ρ.im ^ 2) < 0.0463 := by
    have h := finite_zeta_reciprocal_square_sum_lt S
      (fun ρ hρ => ((mem_zerosRectD_zetaF_iff_xi hU).mp (Finset.mem_filter.mp hρ).1).1)
    convert h using 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [multRectD_zetaF_eq_analyticOrder hU (Finset.mem_filter.mp hρ).1]
  have hp := PolynomialZeroPairing.sum_norm_low_eq_two_closed hT hTU
    (fun ρ : ℂ => ((1 / ρ.im ^ 2 : ℝ) : ℂ)) (by
      intro ρ _
      simp only [Complex.conj_im, neg_sq])
  have hnorm (ρ : ℂ) : ‖((1 / ρ.im ^ 2 : ℝ) : ℂ)‖ = 1 / ρ.im ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [hnorm, mul_one_div] at hp
  change (∑ ρ ∈ S, (multRectD zetaF U ρ : ℝ) / ρ.im ^ 2) =
    2 * ∑ ρ ∈ closedPositiveZeros T,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im ^ 2 at hp
  linarith

/-- The public weighted-zero interface includes the upper endpoint. -/
theorem weighted_reciprocal_square_sum_lt {T : ℝ} (hT : 0 < T) :
    WeightedZetaZeros.weightedSum 0 T (fun t => 1 / t ^ 2) < 0.02315 := by
  have he : WeightedZetaZeros.weightedSum 0 T (fun t => 1 / t ^ 2) =
      ∑ ρ ∈ closedPositiveZeros T,
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im ^ 2 := by
    unfold WeightedZetaZeros.weightedSum
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hi := ((mem_closedPositiveZeros_iff hT).mp hρ).2.1
    simp only [hi, if_true, mul_one_div]
  rw [he]
  exact positive_reciprocal_square_sum_lt hT

end TernaryGoldbach.RSBounds.SchoenfeldReciprocalSquare
