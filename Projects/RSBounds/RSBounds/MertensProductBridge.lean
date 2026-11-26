import RSBounds.MertensProductCorrection
import RSBounds.MertensSecondSigned

/-! Binding the signed second-Mertens error and the finite prime-power
correction to the actual Euler product. Numerical budgets remain explicit
inputs in this reusable bridge. -/

open Finset Real

namespace TernaryGoldbach.RSBounds.MertensProductBridge

open TernaryGoldbach.PNTMertens MertensSecondSigned

theorem primeProduct_pos (n : ℕ) : 0 < Totient.primeProduct n := by
  unfold Totient.primeProduct
  apply prod_pos
  intro p hp
  have hprime : p.Prime := (mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (by linarith) (by linarith)

theorem log_primeProduct_le {n : ℕ} (hn : 100000 ≤ n) {e j : ℝ}
    (hpsi : |Chebyshev.psi n - n| ≤ e * n)
    (hJ : ∀ u : ℝ, (n : ℝ) ≤ u → |J u| ≤ j) :
    Real.log (Totient.primeProduct n) ≤ Real.eulerMascheroniConstant +
      Real.log (Real.log n) + e / Real.log n +
      2 * j * (1 / Real.log n + 1 / (Real.log n) ^ 2) +
      5.6 / (Real.sqrt n * Real.log n) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have he := second_error_abs_le hn2 hpsi hJ
  have hc := (MertensProductCorrection.primeProduct_correction_bounds hn).2
  have hE : E₂Λ n = (∑ d ∈ Ioc 0 n, (ArithmeticFunction.vonMangoldt d : ℝ) /
      (d * Real.log d)) - Real.log (Real.log n) - Real.eulerMascheroniConstant := by
    simp only [E₂Λ, Nat.floor_natCast, γ.eq_eulerMascheroni]
  rw [hE] at he
  unfold MertensLogKernel.logMass at he
  have hh := (abs_le.mp he).2
  linarith

theorem primeProduct_lt_of_errors {n : ℕ} (hn : 100000 ≤ n) {e j : ℝ}
    (hpsi : |Chebyshev.psi n - n| ≤ e * n)
    (hJ : ∀ u : ℝ, (n : ℝ) ≤ u → |J u| ≤ j)
    (hbudget : e / Real.log n + 2 * j * (1 / Real.log n + 1 / (Real.log n) ^ 2) +
      5.6 / (Real.sqrt n * Real.log n) < Real.log (1 + 1 / (2 * (Real.log n) ^ 2))) :
    Totient.primeProduct n < Real.exp Real.eulerMascheroniConstant *
      (Real.log n + 1 / (2 * Real.log n)) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos hn1
  have hc : 0 < 1 + 1 / (2 * (Real.log n) ^ 2) := by positivity
  have hl := log_primeProduct_le hn hpsi hJ
  have hh : Real.log (Totient.primeProduct n) < Real.eulerMascheroniConstant +
      Real.log (Real.log n) + Real.log (1 + 1 / (2 * (Real.log n) ^ 2)) := by
    linarith
  have he := Real.exp_lt_exp.mpr hh
  rw [Real.exp_log (primeProduct_pos n), Real.exp_add, Real.exp_add,
    Real.exp_log hL, Real.exp_log hc] at he
  convert he using 1
  field_simp [hL.ne'] <;> ring

end TernaryGoldbach.RSBounds.MertensProductBridge
