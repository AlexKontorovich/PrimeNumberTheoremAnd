import Mathlib.Tactic

/-
This file stores the numerical data for `RosserSchoenfeldPrime.lean`, as well as any purely numerical computations about that data.  This file should not import any other files from the PNT+ project, other than further numerical data files.  This is to avoid these computation-intensive files from having to be repeatedly compiled.

In general, data should be moved here once we require significant numerical calculations to be performed using that data.
-/


namespace RS_prime

/- This is the optimal constant in the inequality $\psi(x) \leq c_0 x$. -/

def c₀ : ℝ := 1.03883

end RS_prime
