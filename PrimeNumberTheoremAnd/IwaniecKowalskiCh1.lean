import Architect
import Mathlib

open ArithmeticFunction hiding log
open Finset Nat Real

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

blueprint_comment /--
Here we collect facts from Chapter 1 that are not already in Mathlib.
We will try to upstream as much as possible.
-/


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
