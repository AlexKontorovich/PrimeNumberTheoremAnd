import RSBounds.QuarticFirst29BudgetNumerics
import RSBounds.RosserWeightedBounds
import RSBounds.PolynomialZeroKernel

/-!
# Parameter and scalar-function bridges for the first-29 quartic budget

These are rational arithmetic, order, and algebraic identities. No numerical
source is regenerated, and no additional analytic estimate is assumed.
-/

namespace TernaryGoldbach.RSBounds.QuarticFirst29BudgetBridges
open QuarticFirst29BudgetNumerics

theorem delta_cast_eq : (delta : ℝ) = 0.0000211 := by norm_num [delta]

theorem delta_cast_pos : (0 : ℝ) < (delta : ℝ) := by norm_num [delta]

theorem a_cast_eq : (a : ℝ) = 1 + 2 * (delta : ℝ) := by
  unfold a
  push_cast
  rfl

theorem C_cast_eq_R4 :
    (C : ℝ) = PolynomialZeroKernel.R4 (delta : ℝ) / (delta : ℝ) ^ 4 := by
  unfold C PolynomialZeroKernel.R4
  push_cast
  rfl

theorem Y_cast_eq : (Y : ℝ) = 2 / (delta : ℝ) := by
  unfold Y
  push_cast
  rfl

theorem A_cast_eq : (A : ℝ) = 1894439 := by norm_num [A]

theorem a_nonneg : (0 : ℝ) ≤ (a : ℝ) := by
  rw [a_cast_eq]
  have h := delta_cast_pos
  positivity

theorem C_nonneg : (0 : ℝ) ≤ (C : ℝ) := by
  rw [C_cast_eq_R4]
  unfold PolynomialZeroKernel.R4
  positivity

theorem saving_nonneg : (0 : ℝ) ≤ (a : ℝ) - 0.931 := by
  norm_num [a, delta]

theorem hundred_le_Y : (100 : ℝ) ≤ (Y : ℝ) := by norm_num [Y, delta]

theorem Y_le_A : (Y : ℝ) ≤ (A : ℝ) := by norm_num [Y, delta, A]

theorem cutoff_zero_eq : (cutoff 0 : ℝ) = 4 / (3 * (delta : ℝ)) := by
  norm_num [cutoff, Y, delta]

theorem cutoff_eight_eq_Y_sub : (cutoff 8 : ℝ) = (Y : ℝ) - 8 := by
  norm_num [cutoff, Y, delta]

theorem cutoff_eight_eq :
    (cutoff 8 : ℝ) = 2 * (1 - 4 * (delta : ℝ)) / (delta : ℝ) := by
  norm_num [cutoff, Y, delta]

theorem cutoff_monotone_rat : Monotone cutoff := by
  intro m n hmn
  have hspan : (0 : ℚ) ≤ (Y - 8) - 4 / (3 * delta) := by decide +kernel
  have hmnQ : (m : ℚ) ≤ (n : ℚ) := by exact_mod_cast hmn
  unfold cutoff
  exact add_le_add le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmnQ hspan)
      (by norm_num : (0 : ℚ) ≤ 8))

theorem cutoff_monotone : Monotone (fun j : ℕ => (cutoff j : ℝ)) := by
  intro m n hmn
  exact (Rat.cast_le (K := ℝ)).mpr (cutoff_monotone_rat hmn)

theorem hundred_le_cutoff_zero : (100 : ℝ) ≤ (cutoff 0 : ℝ) := by
  norm_num [cutoff, Y, delta]

theorem cutoff_eight_le_Y : (cutoff 8 : ℝ) ≤ (Y : ℝ) := by
  rw [cutoff_eight_eq_Y_sub]
  linarith

theorem hundred_le_cutoff (j : ℕ) : (100 : ℝ) ≤ (cutoff j : ℝ) :=
  hundred_le_cutoff_zero.trans (cutoff_monotone (Nat.zero_le j))

theorem cutoff_le_Y {j : ℕ} (hj : j ≤ 8) : (cutoff j : ℝ) ≤ (Y : ℝ) :=
  (cutoff_monotone hj).trans cutoff_eight_le_Y

theorem cutoff_le_A {j : ℕ} (hj : j ≤ 8) : (cutoff j : ℝ) ≤ (A : ℝ) :=
  (cutoff_le_Y hj).trans Y_le_A

theorem cutoff_range :
    (100 : ℝ) ≤ (cutoff 0 : ℝ) ∧ (cutoff 0 : ℝ) ≤ (cutoff 8 : ℝ) ∧
      (cutoff 8 : ℝ) ≤ (Y : ℝ) :=
  ⟨hundred_le_cutoff_zero, cutoff_monotone (by decide), cutoff_eight_le_Y⟩

/-- The signed split correction has the direction used in the analytic bound. -/
theorem split_coefficient_le : (a : ℝ) / (Y : ℝ) ≤ (C : ℝ) / (Y : ℝ) ^ 5 := by
  have hq : a / Y ≤ C / Y ^ 5 := by decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  exact hr

theorem F_eq_rosserF (t : ℝ) : F t = rosserF t := by
  unfold F rosserF
  ring

theorem R_eq_rosserR (t : ℝ) : R t = rosserR 1.588 t := rfl

theorem fifthTail_eq_J (t : ℝ) : fifthTail t = RosserTailIntegrals.J t := rfl

theorem lowIntegral_eq_I : lowIntegral = RosserWeightedBounds.I 100 (Y : ℝ) := by
  unfold lowIntegral RosserWeightedBounds.I
  ring

theorem lineWeight_eq :
    lineWeight =
      (a : ℝ) * (0.592316 + RosserWeightedBounds.I 100 (Y : ℝ) +
        (RosserWeightedBounds.G 100 - 29) / 100) +
      (C : ℝ) * RosserTailIntegrals.J (Y : ℝ) +
      2 * rosserR 1.588 (Y : ℝ) * ((C : ℝ) / (Y : ℝ) ^ 5 - (a : ℝ) / (Y : ℝ)) := by
  simp only [lineWeight, F_eq_rosserF, R_eq_rosserR, fifthTail_eq_J,
    lowIntegral_eq_I, RosserWeightedBounds.G]

theorem highWeight_eq :
    highWeight = (C : ℝ) * (RosserTailIntegrals.J (A : ℝ) +
      2 * rosserR 1.588 (A : ℝ) / (A : ℝ) ^ 5) := by
  simp only [highWeight, fifthTail_eq_J, R_eq_rosserR]

theorem bandMass_eq :
    bandMass = ∑ j ∈ Finset.range 8,
      (rosserF (cutoff (j + 1) : ℝ) - rosserR 1.588 (cutoff (j + 1) : ℝ) -
        rosserF (cutoff j : ℝ) - rosserR 1.588 (cutoff j : ℝ)) /
          (cutoff (j + 1) : ℝ) := by
  simp only [bandMass, F_eq_rosserF, R_eq_rosserR]

end TernaryGoldbach.RSBounds.QuarticFirst29BudgetBridges
