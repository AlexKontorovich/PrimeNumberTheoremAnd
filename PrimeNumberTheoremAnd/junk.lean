import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory

example : MeasurableSet {x : ℝ | 0 < x} := by
  apply (isOpen_lt' 0).measurableSet
  exac

example (s : Set ℝ) (hs : MeasurableSet s) (P : ℝ → Prop) (hP : ∀ x ∈ s, P x) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict s), P x := by

  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  exact hP
