import TernaryGoldbach.Explicit.XiPartial

/-!
# Concrete functions in Backlund's zero-count identity

The count is a finite sum of multiplicities of the actual entire xi function.
The anchor is `5/4`, as required by Rosser's circle geometry. The theta
function is the continuous gamma phase, defined by integrating digamma.
-/

open Complex MeasureTheory Set
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

noncomputable def riemannSiegelTheta (T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..(T / 2), (Complex.digamma (1 / 4 + t * I)).re) -
    T / 2 * Real.log Real.pi

noncomputable def arcVariation (f : ℂ → ℂ) (a T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, (logDeriv f ((a : ℂ) + t * I)).re) -
    ∫ σ in (1 / 2 : ℝ)..a, (logDeriv f ((σ : ℂ) + T * I)).im

noncomputable def zetaArgVar (T : ℝ) : ℝ := arcVariation riemannZeta (5 / 4) T
noncomputable def xiArcVar (T : ℝ) : ℝ := arcVariation xiF (5 / 4) T

def zetaGoodHeight (T : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T

noncomputable def positiveZeros (T : ℝ) : Finset ℂ :=
  (zerosIn xiF 2 (RT T) (RT T / 2)).filter (fun ρ => 0 < ρ.im ∧ ρ.im < T)

noncomputable def N (T : ℝ) : ℕ :=
  ∑ ρ ∈ positiveZeros T, multRectD xiF T ρ

end TernaryGoldbach.RSBounds.BacklundCountIdentity
