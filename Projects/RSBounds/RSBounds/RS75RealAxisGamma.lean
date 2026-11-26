import RSBounds.IEANTNDigammaDifference
import RSBounds.RS75RealAxisNumerics
import Mathlib.Tactic

/-!
# The real-axis Gamma increment with its first term cancelled

The `n = 0` term of the IEANTN Gauss difference cancels `1/s - 1`
exactly. The remaining terms are bounded by the certified sum of the
reciprocal squares of the odd integers at least three.
-/

open Complex

namespace TernaryGoldbach.RSBounds.RS75RealAxisGamma

noncomputable def gammaAxis (s : ℝ) : ℝ :=
  1 / s + (1 / 2 : ℝ) * (Complex.digamma ((s : ℂ) / 2)).re

noncomputable def gammaTerm (s : ℝ) (n : ℕ) : ℝ :=
  (s - 1) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + s))

theorem hasSum_gammaTerm {s : ℝ} (hs : 1 ≤ s) :
    HasSum (gammaTerm s)
      ((1 / 2 : ℝ) * ((Complex.digamma ((s : ℂ) / 2)).re -
        (Complex.digamma (1 / 2 : ℂ)).re)) := by
  have hs0 : 0 < s / 2 := by linarith
  have ha := IEANTNDigamma.summable_gauss_series
    (s := ((s / 2 : ℝ) : ℂ)) (by simpa using hs0)
  have hb := IEANTNDigamma.summable_gauss_series
    (s := (1 / 2 : ℂ)) (by norm_num)
  change Summable (GammaSolution.gaussTerm ((s / 2 : ℝ) : ℂ)) at ha
  change Summable (GammaSolution.gaussTerm (1 / 2 : ℂ)) at hb
  have hdiff :
      Complex.digamma ((s / 2 : ℝ) : ℂ) - Complex.digamma (1 / 2 : ℂ) =
        (∑' n, GammaSolution.gaussTerm ((s / 2 : ℝ) : ℂ) n) -
          ∑' n, GammaSolution.gaussTerm (1 / 2 : ℂ) n := by
    rw [GammaSolution.digamma_eq_gaussSum (by simpa using hs0),
      GammaSolution.digamma_eq_gaussSum (by norm_num)]
    unfold GammaSolution.gaussSum
    ring
  have hh := (Complex.hasSum_re (ha.hasSum.sub hb.hasSum)).mul_left (1 / 2 : ℝ)
  rw [← hdiff, Complex.sub_re] at hh
  have hterm (n : ℕ) :
      (1 / 2 : ℝ) * (GammaSolution.gaussTerm ((s / 2 : ℝ) : ℂ) n -
        GammaSolution.gaussTerm (1 / 2 : ℂ) n).re = gammaTerm s n := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      GammaSolution.gaussTerm_sub hs0 (by norm_num) n]
    have he :
        (((s / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ)) /
          (((n : ℂ) + ((s / 2 : ℝ) : ℂ)) * ((n : ℂ) + ((1 / 2 : ℝ) : ℂ))) =
        (((s / 2 - 1 / 2) / (((n : ℝ) + s / 2) * ((n : ℝ) + 1 / 2)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he, Complex.ofReal_re]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₁ : (n : ℝ) + s / 2 ≠ 0 := by linarith
    have h₂ : (n : ℝ) + 1 / 2 ≠ 0 := by linarith
    have h₃ : 2 * (n : ℝ) + 1 ≠ 0 := by linarith
    have h₄ : 2 * (n : ℝ) + s ≠ 0 := by linarith
    unfold gammaTerm
    field_simp [h₁, h₂, h₃, h₄]
    <;> ring
  have hh' := hh.congr_fun (fun n => (hterm n).symm)
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hh'

theorem gammaTerm_succ_le {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    gammaTerm s (n + 1) ≤ (s - 1) * RS75RealAxisNumerics.oddSquareTerm n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < 2 * (n : ℝ) + 3 := by positivity
  have hden : (2 * (n : ℝ) + 3) ^ 2 ≤
      (2 * ((n + 1 : ℕ) : ℝ) + 1) * (2 * ((n + 1 : ℕ) : ℝ) + s) := by
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ 2 * (n : ℝ) + 3 by positivity) (sub_nonneg.mpr hs)]
  unfold gammaTerm RS75RealAxisNumerics.oddSquareTerm
  calc
    _ ≤ (s - 1) / (2 * (n : ℝ) + 3) ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) (pow_pos hp 2) hden
    _ = _ := by ring

/-- The real-axis Gamma contribution after exact cancellation of its first term. -/
theorem gammaAxis_increment_le {s : ℝ} (hs : 1 ≤ s) :
    gammaAxis s - gammaAxis 1 ≤ 0.23391 * (s - 1) := by
  have hsum := hasSum_gammaTerm hs
  have htail : Summable (fun n : ℕ => gammaTerm s (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum.summable
  have hle := Summable.tsum_le_tsum (gammaTerm_succ_le hs) htail
    (RS75RealAxisNumerics.summable_oddSquareTerm.mul_left (s - 1))
  rw [tsum_mul_left] at hle
  have hnumeric := mul_le_mul_of_nonneg_left RS75RealAxisNumerics.tsum_oddSquareTerm_le
    (by linarith : 0 ≤ s - 1)
  have he := hsum.tsum_eq
  rw [hsum.summable.tsum_eq_zero_add] at he
  have hzero : gammaTerm s 0 = (s - 1) / s := by simp [gammaTerm]
  rw [hzero] at he
  have hs0 : s ≠ 0 := by linarith
  have hcancel : 1 / s - 1 + (s - 1) / s = 0 := by field_simp [hs0] <;> ring
  unfold gammaAxis
  norm_num only [one_div_one, Complex.ofReal_one] at ⊢
  linarith

end TernaryGoldbach.RSBounds.RS75RealAxisGamma
