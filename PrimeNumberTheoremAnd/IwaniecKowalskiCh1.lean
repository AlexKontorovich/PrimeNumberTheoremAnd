import Architect
import Mathlib

open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

open scoped LSeries.notation

namespace ArithmeticFunction

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

blueprint_comment /--
Here we collect facts from Chapter 1 that are not already in Mathlib.
We will try to upstream as much as possible.
-/

/-- `τ` (tau) is the divisor count function, equal to `σ 0`. -/
abbrev tau : ArithmeticFunction ℕ := σ 0

@[inherit_doc tau]
scoped notation "τ" => tau

variable {R : Type*}

/--
An arithmetic function `IsAdditive` if it satisfies the property that for any two coprime natural numbers `m` and `n`, the function evaluated at their product equals the sum of the function evaluated at each number individually.
-/
@[blueprint
  "IsAdditive"
  (statement := /-- Additive function. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, IsRelPrime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (statement := /-- Completely additive function. -/)]
def IsCompletelyAdditive [MulZeroOneClass R] :=
  MonoidWithZeroHom ℕ R

/-- If `g` is a multiplicative arithmetic function, then for any `n ≠ 0`,
    `∑ d | n, μ(d) * g(d) = ∏ p ∈ n.primeFactors, (1 - g(p))`. -/
@[blueprint
  "sum_moebius_pmul_eq_prod_one_sub"
  (statement := /-- If `g` is a multiplicative arithmetic function, then for any `n ≠ 0`,
    `∑ d | n, μ(d) * g(d) = ∏ p ∈ n.primeFactors, (1 - g(p))`. -/)
  (proof := /--
  Multiply out and collect terms.
  -/)]
theorem sum_moebius_pmul_eq_prod_one_sub {R : Type*} [CommRing R]
    {g : ArithmeticFunction R} (hg : g.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (moebius d : R) * g d = ∏ p ∈ n.primeFactors, (1 - g p) := by
  sorry



/-- The Dirichlet convolution of `ζ` with itself is `τ` (the divisor count function). -/
@[blueprint
  "zeta_mul_zeta"
  (statement := /-- The Dirichlet convolution of `ζ` with itself is `τ` (the divisor count function). -/)
  (proof := /--
  By definition of `ζ`, we have `ζ(n) = 1` for all `n ≥ 1`. Thus, the Dirichlet convolution
  `(ζ * ζ)(n)` counts the number of ways to write `n` as a product of two positive integers,
  which is exactly the number of divisors of `n`, i.e., `τ(n)`.
  -/)]
theorem zeta_mul_zeta : (ζ : ArithmeticFunction ℕ) * ζ = τ := by
  sorry

/-- The L-series of `τ` equals the square of the Riemann zeta function for `Re(s) > 1`. -/
@[blueprint
  "LSeries_tau_eq_riemannZeta_sq"
  (statement := /-- The L-series of `τ` equals the square of the Riemann zeta function for `Re(s) > 1`. -/)
  (proof := /--
  From the previous theorem, we have that the Dirichlet convolution of `ζ` with itself is `τ`.
  Taking L-series on both sides, we get `LSeries(τ, s) = LSeries(ζ, s) * LSeries(ζ, s)`.
  Since `LSeries(ζ, s)` is the Riemann zeta function `ζ(s)`, we conclude that
  `LSeries(τ, s) = ζ(s) ^ 2` for `Re(s) > 1`.
  -/)]
theorem LSeries_tau_eq_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗τ) s = riemannZeta s ^ 2 := by
  sorry



end ArithmeticFunction
