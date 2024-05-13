import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory

example (s : Set ℝ) (P : ℝ → Prop) (hP : ∀ x ∈ s, P x) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict s), P x := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict sorry]
  exact hP
