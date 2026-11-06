import Mathlib

/- Independent Mathlib-only statements. Deliberate theorem holes occur only
in this challenge; neither the solution nor its audit imports this module. -/

namespace TernaryGoldbach.RSBounds.Goals

def FiniteRH (A : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
    |ρ.im| ≤ A → ρ.re = 1 / 2

end TernaryGoldbach.RSBounds.Goals

namespace TernaryGoldbach.RSBounds.RS75ZeroFree1975

theorem zero_free_high {s : ℂ} (ht : 1894439 ≤ |s.im|)
    (hσ : 1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re) :
    riemannZeta s ≠ 0 := by sorry

theorem zero_free (hRH : Goals.FiniteRH 1894439) {s : ℂ}
    (ht : 21 ≤ |s.im|)
    (hσ : 1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re) :
    riemannZeta s ≠ 0 := by sorry

end TernaryGoldbach.RSBounds.RS75ZeroFree1975
