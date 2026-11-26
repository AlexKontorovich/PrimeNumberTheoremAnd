import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Specifications, not proofs. No declaration in this file asserts that a goal
holds. Finite RH is an explicit proposition concerning the actual zeta function.
-/

namespace TernaryGoldbach.RSBounds.Goals

def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

/-- RS75, Theorem 1, with the finite RH verification kept as an explicit
premise. This is a target proposition, not a proof or an axiom. -/
def ZeroFreeRegion1975 : Prop :=
  FiniteRH 1894439 → ∀ s : ℂ, 21 ≤ |s.im| →
    1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re →
    riemannZeta s ≠ 0

def PsiTable1975 : Prop :=
  FiniteRH 1894439 → ∀ x : ℝ, Real.exp 23 ≤ x →
    |Chebyshev.psi x - x| < 0.00020211 * x

def PsiTable1976 : Prop :=
  FiniteRH 1894439 → ∀ x : ℝ, Real.exp 23 ≤ x →
    |Chebyshev.psi x - x| < 0.00020171 * x

def ThetaLogBound (c x₀ : ℝ) : Prop :=
  FiniteRH 1894439 → ∀ x : ℝ, x₀ ≤ x →
    |Chebyshev.theta x - x| ≤ c * x / Real.log x

noncomputable def mertensE : ℝ :=
  -Real.eulerMascheroniConstant -
    ∑' p : ℕ, if p.Prime then Real.log p / ((p : ℝ) * (p - 1)) else 0

def MertensLower : Prop :=
  ∀ x : ℝ, 1 < x → Real.log x + mertensE - 1 / (2 * Real.log x) <
    ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p

def TotientBound : Prop :=
  ∀ q : ℕ, 3 ≤ q → (q : ℝ) / Nat.totient q <
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log q) +
      2.50637 / Real.log (Real.log q)

end TernaryGoldbach.RSBounds.Goals
