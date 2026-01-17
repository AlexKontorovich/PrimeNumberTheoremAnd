import Architect
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Hadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ZetaFiniteOrder

blueprint_comment /--

In this file, we prove the Hadamard Factorization theorem for functions of finite order,
and prove that the zeta function is such.

-/

noncomputable section

open scoped Real

namespace PrimeNumberTheoremAnd

/-!
We provide blueprint-facing entry points for the intrinsic Hadamard factorization theorem.

The **general** theorem is `Complex.Hadamard.hadamard_factorization_of_growth`, which factors an
entire function assuming only a polynomial-type growth bound on `log(1+‖f z‖)`.

The **zeta** corollary is `Riemann.completedRiemannZeta₀_hadamard_factorization_intrinsic`,
obtained by combining the general theorem with the growth estimate proved in
`Mathlib/Analysis/Complex/ZetaFiniteOrder.lean`.
-/

@[blueprint
  "hadamard_factorization_of_growth"
  (title := "Hadamard factorization (intrinsic, from growth)")
  (statement := /--
    Let `f : ℂ → ℂ` be entire and not identically zero. If `log (1 + ‖f z‖)` is bounded above by
    `C * (1 + ‖z‖)^ρ`, then `f` admits a Hadamard factorization in terms of an exponential of a
    polynomial and the canonical product indexed by the divisor of `f`.
  --/)
  (latexEnv := "theorem")]
theorem hadamard_factorization_of_growth {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            Complex.Hadamard.divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_growth (f := f) (ρ := ρ) hρ hentire hnot hgrowth)

@[blueprint
  "completedRiemannZeta0_hadamard_factorization_intrinsic"
  (title := "Hadamard factorization for the completed Riemann zeta function")
  (statement := /--
    The entire completed Riemann zeta function `completedRiemannZeta₀` admits an intrinsic Hadamard
    factorization with genus `1` and an exponential factor of degree at most `1`.
  --/)
  (latexEnv := "theorem")]
theorem completedRiemannZeta₀_hadamard_factorization_intrinsic :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ 1 ∧
      ∀ z : ℂ,
        completedRiemannZeta₀ z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
            Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  simpa using Riemann.completedRiemannZeta₀_hadamard_factorization_intrinsic

end PrimeNumberTheoremAnd
