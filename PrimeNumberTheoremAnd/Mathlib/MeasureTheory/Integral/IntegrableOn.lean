module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Domination for `IntegrableOn`

A small `IntegrableOn` wrapper for a.e. norm domination on a restricted measure.
-/

@[expose] public section

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}

/-- If `‖f x‖ ≤ g x` a.e. on `s` and `g` is integrable on `s`, then so is `f`. -/
lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ)
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (h : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ g x) : IntegrableOn f s μ := by
  exact Integrable.mono' hg hf h

end MeasureTheory
