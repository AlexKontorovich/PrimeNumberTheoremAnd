import RSBounds.BacklundLowScalarBase
import RSBounds.Targets
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The finite-height handoff for the RS75 zero-free region

The boundary is strictly to the right of one half for every height at least
21. Finite RH therefore supplies the closed height interval through 1894439.
The separate high-height theorem remains an explicit input to the final
assembly lemma in this file.
-/

namespace TernaryGoldbach.RSBounds.RS75FiniteHandoff

open BacklundLowScalar

theorem log_twentyone_seventeen_gt :
    (0.21 : ℝ) < Real.log (21 / 17 : ℝ) := by
  let c : LogCert := ⟨0, 17, 4⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (21 / 100 : ℚ) < c.lower := by
    change (21 / 100 : ℚ) < (LogCert.mk 0 17 4).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  norm_num at h ⊢
  exact h

theorem boundary_gt_half {t : ℝ} (ht : 21 ≤ t) :
    (1 / 2 : ℝ) < 1 - 1 / (9.645908801 * Real.log (t / 17)) := by
  have hm : Real.log (21 / 17 : ℝ) ≤ Real.log (t / 17) :=
    Real.log_le_log (by norm_num) (div_le_div_of_nonneg_right ht (by norm_num))
  have hl : (0.21 : ℝ) < Real.log (t / 17) :=
    log_twentyone_seventeen_gt.trans_le hm
  have hd : (2 : ℝ) < 9.645908801 * Real.log (t / 17) := by linarith
  have hpos : (0 : ℝ) < 9.645908801 * Real.log (t / 17) := by linarith
  have hdiv : 1 / (9.645908801 * Real.log (t / 17)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ hpos).mpr
    linarith
  linarith

/-- Finite RH is needed only for this bounded-height part of the target. -/
theorem zero_free_low (hRH : Goals.FiniteRH 1894439) {s : ℂ}
    (ht : 21 ≤ |s.im|) (hA : |s.im| ≤ 1894439)
    (hσ : 1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hhalf : (1 / 2 : ℝ) < s.re := (boundary_gt_half ht).trans_le hσ
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hr := hRH s hz hs0 hs1 hA
  linarith

/-- An implication, not a proof of the missing high-height estimate. -/
theorem of_high
    (high : ∀ s : ℂ, 1894439 ≤ |s.im| →
      1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re →
      riemannZeta s ≠ 0) : Goals.ZeroFreeRegion1975 := by
  intro hRH s ht hσ
  by_cases hA : |s.im| ≤ 1894439
  · exact zero_free_low hRH ht hA hσ
  · exact high s (le_of_not_ge hA) hσ

end TernaryGoldbach.RSBounds.RS75FiniteHandoff
