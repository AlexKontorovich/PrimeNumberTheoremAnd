import Mathlib

open MeasureTheory

example {α : Type} [MeasurableSpace α] {μ : Measure α} {f : α → ENNReal} {a : ENNReal}
    (h : (∫⁻ x, f x ∂μ) ≤ a) (ha : a ≠ ⊤) : (∫⁻ x, f x ∂μ) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ha h
