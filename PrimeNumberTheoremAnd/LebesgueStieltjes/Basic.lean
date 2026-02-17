/--
  Lebesgue–Stieltjes integration (work in progress)
  ===============================================

  This folder hosts a Lean formalization of Lebesgue–Stieltjes integration,
  with a focus on an integration-by-parts theorem for functions of bounded variation (BV).

  The present file provides small convenience wrappers around mathlib's `StieltjesFunction`
  and its associated measure.
-/

import Mathlib.MeasureTheory.Measure.Stieltjes

noncomputable section

open Set MeasureTheory Function
open ENNReal (ofReal)

namespace PrimeNumberTheoremAnd
namespace LebesgueStieltjes

/-- The Stieltjes measure associated to a monotone function `g : ℝ → ℝ`.

This is the Borel measure attached by mathlib to the right-continuous modification `rightLim g`.
-/
noncomputable def stieltjesMeasure (g : ℝ → ℝ) (hg : Monotone g) : Measure ℝ :=
  (hg.stieltjesFunction).measure

@[simp]
lemma stieltjesMeasure_Ioc (g : ℝ → ℝ) (hg : Monotone g) (a b : ℝ) :
    stieltjesMeasure g hg (Ioc a b) = ofReal (Function.rightLim g b - Function.rightLim g a) := by
  simp [stieltjesMeasure, Monotone.stieltjesFunction_eq]

lemma stieltjesMeasure_rightLim (g : ℝ → ℝ) (hg : Monotone g) :
    stieltjesMeasure (Function.rightLim g) (hg.rightLim) = stieltjesMeasure g hg := by
  ext s hs
  have hrc : ∀ x, ContinuousWithinAt (Function.rightLim g) (Ici x) x :=
    (hg.stieltjesFunction).right_continuous'
  have hrl : Function.rightLim (Function.rightLim g) = Function.rightLim g := by
    funext x
    exact (hrc x).rightLim_eq
  have hsf : (hg.rightLim).stieltjesFunction = hg.stieltjesFunction := by
    ext x
    simp [Monotone.stieltjesFunction_eq, hrl]
  simpa [stieltjesMeasure, hsf]

end LebesgueStieltjes
end PrimeNumberTheoremAnd
