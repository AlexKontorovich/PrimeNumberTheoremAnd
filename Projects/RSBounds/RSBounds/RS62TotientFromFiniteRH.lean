import RSBounds.RS62FiniteHandoff
import RSBounds.TotientAnalyticReduction
import RSBounds.SmallTotientProduct
import RSBounds.MertensProductBridge
import RSBounds.RS62ProductBudget
import RSBounds.PsiThetaElementary
import RSBounds.ModeratePsi
import RSBounds.RosserSchoenfeld1975
import RSBounds.WeakPsiTail
import RSBounds.MertensLargeBudget

/-! The unrestricted RS62 totient inequality with the finite-height
critical-line premise displayed. The finite prime-product range ends at
100000; there is no upper restriction on the integer in the final theorem.

Source preparation: dependencies and this assembly are checked separately.
-/

open Real

namespace TernaryGoldbach.RSBounds.RS62TotientFromFiniteRH

noncomputable def fixedJ (x : ℝ) : ℝ :=
  0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
    Real.log (2 * Real.pi) / x

theorem log_ge_six {x : ℝ} (hx : 100000 ≤ x) : 6 ≤ Real.log x := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < x)).mpr
  calc
    Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2.7182818286 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    _ ≤ 100000 := by norm_num
    _ ≤ x := hx

theorem primeTheta_eq (n : ℕ) : Totient.primeTheta n = Chebyshev.theta n := by
  unfold Totient.primeTheta Chebyshev.theta
  simp only [Nat.floor_natCast]
  congr 1

theorem theta_lower_of_errors {x e : ℝ} (hx : 100000 ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ e * x)
    (hbudget : e + 6.5 / Real.sqrt x ≤ 1 / (2 * Real.log x)) :
    x * (1 - 1 / (2 * Real.log x)) ≤ Chebyshev.theta x := by
  have hx0 : 0 < x := by linarith
  have hs0 := Real.sqrt_pos.mpr hx0
  have heq : (e + 6.5 / Real.sqrt x) * x = e * x + 6.5 * Real.sqrt x := by
    field_simp [hs0.ne']
    nlinarith only [Real.sq_sqrt hx0.le]
  have hm := mul_le_mul_of_nonneg_right hbudget hx0.le
  rw [heq] at hm
  have ht := PsiThetaElementary.psi_sub_theta_le hx
  have hp := (abs_le.mp hpsi).1
  nlinarith only [hm, ht, hp]

theorem theta_lower (hRH : Goals.FiniteRH 1894439) {x : ℝ} (hx : 100000 ≤ x) :
    x * (1 - 1 / (2 * Real.log x)) ≤ Chebyshev.theta x := by
  have hx0 : 0 < x := by linarith
  by_cases h23 : Real.log x ≤ 23
  · apply theta_lower_of_errors hx (e := 0.0023 + 6 / Real.sqrt x)
    · rw [MertensModerateBudget.error_mul_eq hx0]
      exact ModeratePsi.psi_error_le hRH hx
    · convert PsiThetaElementary.moderate_theta_budget hx h23 using 1 <;> ring
  · have hExp23 : Real.exp 23 ≤ x :=
      (Real.le_log_iff_exp_le hx0).mp (le_of_lt (lt_of_not_ge h23))
    by_cases h2400 : Real.log x ≤ 2400
    · exact theta_lower_of_errors hx
        (RosserSchoenfeld1975.psi_error_b23 hRH x hExp23).le
        (PsiThetaElementary.b23_theta_budget hExp23 h2400)
    · have hExp2400 : Real.exp 2400 ≤ x :=
        (Real.le_log_iff_exp_le hx0).mp (le_of_lt (lt_of_not_ge h2400))
      apply theta_lower_of_errors hx (e := 0.1 / Real.log x)
      · convert WeakPsiTail.psi_error_le hRH hExp2400 using 1 <;> ring
      · exact PsiThetaElementary.large_theta_budget hExp2400

theorem primeProduct_log_upper (hRH : Goals.FiniteRH 1894439)
    {n : ℕ} (hn : 100000 ≤ n) :
    Totient.primeProduct n < Real.exp Real.eulerMascheroniConstant *
      (Real.log n + 1 / (2 * Real.log n)) := by
  have hx : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hJ : ∀ u : ℝ, (n : ℝ) ≤ u → |MertensSecondSigned.J u| ≤ fixedJ n := by
    intro u hu
    exact (MertensPotentialBound.abs_J_A_lt_uniform hRH (by linarith) hu).le
  by_cases h23 : Real.log (n : ℝ) ≤ 23
  · apply MertensProductBridge.primeProduct_lt_of_errors hn
      (e := 0.0023 + 6 / Real.sqrt n) (j := fixedJ n)
    · rw [MertensModerateBudget.error_mul_eq hx0]
      exact ModeratePsi.psi_error_le hRH hx
    · exact hJ
    · exact RS62ProductBudget.moderate_log_budget hx h23 le_rfl le_rfl
  · have hExp23 : Real.exp 23 ≤ n :=
      (Real.le_log_iff_exp_le hx0).mp (le_of_lt (lt_of_not_ge h23))
    by_cases h2400 : Real.log (n : ℝ) ≤ 2400
    · exact MertensProductBridge.primeProduct_lt_of_errors hn
        (RosserSchoenfeld1975.psi_error_b23 hRH n hExp23).le hJ
        (RS62ProductBudget.b23_log_budget hExp23 h2400 le_rfl le_rfl)
    · have hL : 2400 ≤ Real.log (n : ℝ) := le_of_lt (lt_of_not_ge h2400)
      have hExp2400 : Real.exp 2400 ≤ n := (Real.le_log_iff_exp_le hx0).mp hL
      apply MertensProductBridge.primeProduct_lt_of_errors hn
        (e := 0.1 / Real.log n) (j := 1 / (Real.log n) ^ 2)
      · convert WeakPsiTail.psi_error_le hRH hExp2400 using 1 <;> ring
      · intro u hu
        exact (MertensLargeBudget.abs_J_lt (by linarith) hL hu hRH).le
      · exact RS62ProductBudget.large_log_budget hExp2400 le_rfl le_rfl

theorem prime_product_rs62 (hRH : Goals.FiniteRH 1894439)
    {n : ℕ} (hn : 100000 ≤ n) :
    Totient.primeProduct n < Real.exp Real.eulerMascheroniConstant *
      Real.log (Totient.primeTheta n) + 2.50637 / Real.log (Totient.primeTheta n) := by
  have hx : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  apply rs62_primeProduct_bound_of_inputs
    (by linarith [Totient.exp_gamma_ge]) SmallTotientProduct.exp_gamma_le
    (by linarith : (0 : ℝ) < n) (log_ge_six hx)
  · rw [primeTheta_eq]
    exact theta_lower hRH hx
  · exact primeProduct_log_upper hRH hn

/-- The original all-integer RS62 target, conditional only on finite RH
through the displayed height. No upper bound on n occurs. -/
theorem totient_bound_of_finiteRH (hRH : Goals.FiniteRH 1894439) : Goals.TotientBound := by
  intro n hn
  exact RS62FiniteHandoff.totient_ratio_lt_of_tail (X := 100000) (by norm_num)
    (fun p _ hp => prime_product_rs62 hRH hp) hn

end TernaryGoldbach.RSBounds.RS62TotientFromFiniteRH
