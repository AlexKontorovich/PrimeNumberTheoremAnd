import RSBounds.BacklundFunctionalStrip
import RSBounds.BacklundZetaBoundary
import RSBounds.BacklundGammaModulusAbsorption

/-!
# Backlund's left-strip bound (77)

The Gamma factor is bounded by a slightly looser explicit multiplier
than the one printed in Backlund, but the saving in (54) absorbs it.
The resulting zeta estimate has exactly the classical constant and range.
-/

open Complex Real

namespace TernaryGoldbach.RSBounds.BacklundLeftZetaBoundary

/-- Backlund (1918), (77), unconditionally for `-1/2 ≤ σ ≤ 0`, `t ≥ 50`. -/
theorem norm_zeta_left_strip_lt {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 0) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ <
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hζ : ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ ≤ Real.log t - 6 / 125 := by
    have h := BacklundZetaBoundary.zeta_norm_le_log_sub
      (s := (((1 - σ : ℝ) : ℂ) + t * I))
      (by simp; linarith) (by simpa using ht)
    convert h using 1
    norm_num
  have hP : 0 < (t / (2 * Real.pi)) ^ (1 / 2 - σ) :=
    Real.rpow_pos_of_pos (by positivity) _
  calc
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ :=
      BacklundFunctionalMultiplier.norm_zeta_reflected_strip_le hσ (by linarith) ht
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        (Real.log t - 6 / 125) :=
      mul_le_mul_of_nonneg_left hζ (by positivity)
    _ = (t / (2 * Real.pi)) ^ (1 / 2 - σ) *
        (Real.exp (5 / (2 * t ^ 2)) * (Real.log t - 6 / 125)) := by ring
    _ < _ := mul_lt_mul_of_pos_left
      (BacklundGammaModulus.exp_mul_log_saving_lt ht) hP

end TernaryGoldbach.RSBounds.BacklundLeftZetaBoundary
