import Mathlib.Topology.EMetricSpace.BoundedVariation

open Set

example (ψ : ℝ → ℂ) (hvar : BoundedVariationOn ψ (Set.univ : Set ℝ)) :
    eVariationOn ψ (Set.univ : Set ℝ) ≠ ⊤ := hvar
