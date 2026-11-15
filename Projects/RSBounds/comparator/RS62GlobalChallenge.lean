import Mathlib

/- Independent targets. This file imports no project proof. The deliberate
theorem holes belong only to the challenge and are forbidden in the solution. -/

namespace TernaryGoldbach.RSBounds.Goals

def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

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

namespace TernaryGoldbach.RSBounds.RS62MertensFromFiniteRH

theorem mertens_lower_of_finiteRH (hRH : Goals.FiniteRH 1894439) :
    Goals.MertensLower := by sorry

end TernaryGoldbach.RSBounds.RS62MertensFromFiniteRH

namespace TernaryGoldbach.RSBounds.RS62TotientFromFiniteRH

theorem totient_bound_of_finiteRH (hRH : Goals.FiniteRH 1894439) :
    Goals.TotientBound := by sorry

end TernaryGoldbach.RSBounds.RS62TotientFromFiniteRH
