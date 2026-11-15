import RSBounds.MertensIntervalSum
import RSBounds.MertensIntervalKernel
import RSBounds.PolynomialPrimeSum
import RSBounds.QuadraticContourLimit

/-!
# The finite signed psi integral on the Mellin line

The arithmetic identity is unconditional. The Mellin-line identity takes an
explicit inverse-square kernel estimate; the concrete estimate is discharged
separately by `MertensIntervalDecay`.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensIntervalMellin

open TernaryGoldbach.Explicit MertensIntervalKernel PolynomialExplicit
  QuadraticContourLimit

/-- The actual von Mangoldt Mellin sum is precisely the finite psi integral. -/
theorem SsumG_eq_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    SsumG (1 : DirichletCharacter ℂ 1) (weight a b) 1 =
      ((∫ t in a..b, Chebyshev.psi t / t ^ 2 : ℝ) : ℂ) := by
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  unfold SsumG
  simp only [hchar, mul_one, div_one]
  rw [← MertensIntervalSum.tsum_mangoldt_mul_intervalWeight ha hab,
    Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [weight, intervalWeight, MertensIntervalSum.ramp]

/-- Centering the prime sum requires no limiting or Euler-constant premise. -/
theorem SsumG_sub_log_eq_signed_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    SsumG (1 : DirichletCharacter ℂ 1) (weight a b) 1 -
      ((Real.log b - Real.log a : ℝ) : ℂ) =
      ((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) := by
  rw [SsumG_eq_integral ha hab, integral_psi_error_div_sq ha hab]
  push_cast
  rfl

/-- Mellin inversion on the right line, with only the decay estimate exposed. -/
theorem prime_sum_eq_right_line {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hM : DecayTwo (kernel a b) K) :
    SsumG (1 : DirichletCharacter ℂ 1) (weight a b) 1 =
      -(1 / (2 * π) : ℂ) *
        ∫ t : ℝ, contourIntegrand riemannZeta (kernel a b) 1
          (((3 / 2 : ℝ) : ℂ) + t * I) := by
  have hline : (fun t : ℝ => mellin (weight a b) (((3 / 2 : ℝ) : ℂ) + t * I)) =
      fun t : ℝ => kernel a b (((3 / 2 : ℝ) : ℂ) + t * I) := by
    funext t
    exact mellin_weight ha hb (by simp; norm_num)
  have hc : Continuous (fun t : ℝ =>
      mellin (weight a b) (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact hM.continuous_line _ (Or.inr rfl)
  have hi : Integrable (fun t : ℝ =>
      mellin (weight a b) (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact hM.integrable_line (Or.inr rfl)
  have hS := PolynomialPrimeSum.SsumG_eq_line (1 : DirichletCharacter ℂ 1)
    (fun _ hu => continuousAt_weight a b hu)
    (mellinConvergent_weight ha hb (by norm_num)) hc hi (by norm_num : (0 : ℝ) < 1)
  have hF (t : ℝ) : Fline (1 : DirichletCharacter ℂ 1) (weight a b) 1
      (((3 / 2 : ℝ) : ℂ) + t * I) =
      -contourIntegrand riemannZeta (kernel a b) 1
        (((3 / 2 : ℝ) : ℂ) + t * I) := by
    rw [Fline, contourIntegrand, LFunction_one_mod_one, logDeriv_apply,
      mellin_weight ha hb (by simp; norm_num)]
    ring
  simpa only [hF, integral_neg, mul_neg, neg_mul] using hS

end TernaryGoldbach.RSBounds.MertensIntervalMellin
