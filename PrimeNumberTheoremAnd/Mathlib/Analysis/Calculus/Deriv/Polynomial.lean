module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Polynomial derivatives and logarithmic derivatives

Auxiliary derivative identities for exponential polynomials, used in the polynomial factor
appearing in Hadamard products.
-/

@[expose] public section

namespace Polynomial

/-- The logarithmic derivative of the exponential of a complex polynomial is the polynomial
derivative. -/
theorem logDeriv_exp_eval (P : ℂ[X]) (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
      Polynomial.eval z P.derivative := by
  have hderiv :
      deriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
        Complex.exp (Polynomial.eval z P) * Polynomial.eval z P.derivative := by
    simpa [Function.comp_def, mul_comm] using
      ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).deriv
  rw [logDeriv_apply, hderiv]
  field_simp [Complex.exp_ne_zero (Polynomial.eval z P)]

/-- The derivative of a degree-one complex polynomial is constant. -/
theorem degree_derivative_le_zero_of_degree_le_one {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) :
    P.derivative.degree ≤ 0 := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [Polynomial.coeff_derivative]
  have hmpos : 0 < m := by exact_mod_cast hm
  have hlt : (1 : WithBot ℕ) < (m + 1 : ℕ) := by
    norm_cast
    exact Nat.succ_lt_succ hmpos
  have hcoeff := (Polynomial.degree_le_iff_coeff_zero P 1).mp hP (m + 1) hlt
  simp [hcoeff]

/-- The derivative of a degree-one complex polynomial is independent of the evaluation point. -/
theorem eval_derivative_eq_eval_derivative_zero_of_degree_le_one {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) (z : ℂ) :
    Polynomial.eval z P.derivative = Polynomial.eval 0 P.derivative := by
  have hder :
      P.derivative.degree ≤ 0 :=
    degree_derivative_le_zero_of_degree_le_one hP
  rw [Polynomial.eq_C_of_degree_le_zero hder]
  simp

end Polynomial
