import RSBounds.ZeroWindowFiniteSum
import RSBounds.PolynomialZeroMajorants
import RSBounds.QuarticFirst29BudgetBridges
import RSBounds.RosserWeightedSplit
import RSBounds.ZetaZeroHeadBound
import RSBounds.Targets

/-!
# The positive-ordinate low-zero contribution for the quartic b=23 bound

The only conditional input is RH through 1894439. The short head uses the
proved first-29 zero table; the remaining weights use the proved Rosser count.
The signed correction at Y and the eight cancellation subbands are retained.
-/

open Complex
open scoped BigOperators
namespace TernaryGoldbach.RSBounds.QuarticLowZeroBounds
open BacklundCountIdentity WeightedZetaZeros
open QuarticFirst29BudgetNumerics QuarticFirst29BudgetBridges

private theorem majorant_delta_eq : PolynomialZeroMajorants.delta = (delta : ℝ) := by
  norm_num [PolynomialZeroMajorants.delta, delta]

/-- Finite RH is used only to locate the actual low zeros on the critical line. -/
theorem low_zero_re {ρ : ℂ} (hRH : Goals.FiniteRH 1894439)
    (hρ : ρ ∈ closedPositiveZeros (A : ℝ)) : ρ.re = 1 / 2 := by
  have hp : 0 < (A : ℝ) := by norm_num [A]
  obtain ⟨hz, him, hiA⟩ := (mem_closedPositiveZeros_iff hp).mp hρ
  obtain ⟨hr0, hr1⟩ := zeta_zero_re_strip hz him.ne'
  apply hRH ρ hz hr0 hr1
  simpa only [abs_of_pos him, A_cast_eq] using hiA

/-- The eight explicit subbands supply a lower bound for the actual reciprocal
zero sum in the full cancellation band. -/
theorem bandMass_le_reciprocal :
    bandMass ≤ weightedSum (cutoff 0 : ℝ) (cutoff 8 : ℝ) (fun t => 1 / t) := by
  rw [bandMass_eq]
  exact RosserWeightedSplit.reciprocal_bands_lower 8
    (fun j => (cutoff j : ℝ)) cutoff_monotone
    (by have h := hundred_le_cutoff_zero; linarith)

/-- The exact first-29 head and the joined reciprocal/fifth-power estimate
produce the common line weight. -/
theorem head_and_tail_le_lineWeight :
    (a : ℝ) * (∑ ρ ∈ closedPositiveZeros 100,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) +
      (a : ℝ) * weightedSum 100 (Y : ℝ) (fun t => 1 / t) +
      (C : ℝ) * weightedSum (Y : ℝ) (A : ℝ) (fun t => 1 / t ^ 5) ≤ lineWeight := by
  have hh := mul_le_mul_of_nonneg_left ZetaZeroHeadBound.weighted_head_le a_nonneg
  have ht := RosserWeightedSplit.reciprocal_fifth_split_le
    (D := 100) (Y := (Y : ℝ)) (T := (A : ℝ)) (k := (a : ℝ)) (C := (C : ℝ))
    (by norm_num) hundred_le_Y Y_le_A a_nonneg C_nonneg split_coefficient_le
  rw [ZetaZeroTable.positiveZeroCount_hundred] at ht
  rw [lineWeight_eq]
  nlinarith only [hh, ht]

/-- Actual low-zero contribution, counting multiplicity and valid for either
of the two quartic smoothings. -/
theorem positive_low_sum_le (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hRH : Goals.FiniteRH 1894439) :
    (∑ ρ ∈ closedPositiveZeros (A : ℝ),
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
        ‖PolynomialZeroMajorants.coefficient lower x ρ‖) ≤
      Real.sqrt x * (lineWeight - ((a : ℝ) - 0.931) * bandMass) := by
  have hgeneric := ZeroWindowFiniteSum.sum_le_windows
    (D := 100) (L := (cutoff 0 : ℝ)) (U := (cutoff 8 : ℝ))
    (Y := (Y : ℝ)) (A := (A : ℝ)) (s := Real.sqrt x)
    (k := (a : ℝ)) (C := (C : ℝ)) (r := 0.931)
    (by norm_num) hundred_le_cutoff_zero (cutoff_monotone (by norm_num : 0 ≤ 8))
    cutoff_eight_le_Y Y_le_A (Real.sqrt_nonneg _) a_nonneg
    (fun ρ => ‖PolynomialZeroMajorants.coefficient lower x ρ‖)
    (by
      intro ρ hρ
      have h := PolynomialZeroMajorants.norm_coefficient_le_low lower hx (low_zero_re hRH hρ)
      rw [majorant_delta_eq, ← a_cast_eq] at h
      exact h)
    (by
      intro ρ hρ _
      have him := ((mem_closedPositiveZeros_iff (by norm_num [A])).mp hρ).2.1
      have h := PolynomialZeroMajorants.norm_coefficient_le_high_line lower hx
        (low_zero_re hRH hρ) him.ne'
      rw [abs_of_pos him, majorant_delta_eq, ← C_cast_eq_R4] at h
      exact h)
    (by
      intro ρ hρ hlo hhi
      apply PolynomialZeroMajorants.norm_coefficient_le_band_pos lower hx (low_zero_re hRH hρ)
      · rw [majorant_delta_eq, ← cutoff_zero_eq]
        exact hlo.le
      · rwa [majorant_delta_eq, ← cutoff_eight_eq])
  change (∑ ρ ∈ closedPositiveZeros (A : ℝ),
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) *
      ‖PolynomialZeroMajorants.coefficient lower x ρ‖) ≤ _ at hgeneric
  apply hgeneric.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hb := mul_le_mul_of_nonneg_left bandMass_le_reciprocal saving_nonneg
  have hh := head_and_tail_le_lineWeight
  change (a : ℝ) * (∑ ρ ∈ closedPositiveZeros 100,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) +
      (a : ℝ) * weightedSum 100 (Y : ℝ) (fun t => 1 / t) +
      (C : ℝ) * weightedSum (Y : ℝ) (A : ℝ) (fun t => 1 / t ^ 5) -
      ((a : ℝ) - 0.931) * weightedSum (cutoff 0 : ℝ) (cutoff 8 : ℝ) (fun t => 1 / t) ≤ _
  linarith

end TernaryGoldbach.RSBounds.QuarticLowZeroBounds
