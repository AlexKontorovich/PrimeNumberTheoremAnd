import RSBounds.MertensFinite100000
import RSBounds.ModeratePsi
import RSBounds.RosserSchoenfeld1975
import RSBounds.WeakPsiTail
import RSBounds.MertensLargeBudget

/-! The full real-range RS62 weighted Mertens lower bound.

The sole explicit premise is the critical-line statement through height
1894439. The finite range, actual zero count, zero-free region, contour
formula, Euler normalization and numerical budgets are proved dependencies.
This conditional theorem does not assert the unconditional target without
its displayed finite-height hypothesis.
-/

namespace TernaryGoldbach.RSBounds.RS62MertensFromFiniteRH

theorem mertens_lower_of_finiteRH (hRH : Goals.FiniteRH 1894439) : Goals.MertensLower := by
  apply MertensFiniteWalk.mertensLower_of_tail
  intro x hx
  have hx0 : 0 < x := by linarith
  by_cases h23 : Real.log x ≤ 23
  · exact MertensPotentialBound.mertens_lower_of_moderate_psi hRH hx h23
      (ModeratePsi.psi_error_le hRH hx)
  · have hExp23 : Real.exp 23 ≤ x :=
      (Real.le_log_iff_exp_le hx0).mp (le_of_lt (lt_of_not_ge h23))
    by_cases h2400 : Real.log x ≤ 2400
    · have hxlarge : (1000000000 : ℝ) ≤ x := by
        have hh := QuarticFirst29BudgetApplication.x_lower hExp23
        norm_num at hh
        linarith
      exact MertensPotentialBound.mertens_lower_of_b23_psi hRH hxlarge h2400
        (RosserSchoenfeld1975.psi_error_b23 hRH x hExp23).le
    · have hL : 2400 ≤ Real.log x := le_of_lt (lt_of_not_ge h2400)
      have hExp2400 : Real.exp 2400 ≤ x := (Real.le_log_iff_exp_le hx0).mp hL
      exact MertensLargeBudget.mertens_lower_of_weak_psi (by linarith) hL hRH
        (WeakPsiTail.psi_error_le hRH hExp2400)

end TernaryGoldbach.RSBounds.RS62MertensFromFiniteRH
