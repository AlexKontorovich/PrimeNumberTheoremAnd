import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.NhdsWithin

open Filter Topology

example (g : ℝ → ℝ) (h_g_eq : ∀ᶠ x in 𝓝[≠] (0 : ℝ), g x = 0) (hg0 : g 0 = 0) : Tendsto g (𝓝 0) (𝓝 0) := by
  nth_rw 1 [← nhdsNE_sup_pure 0]
  rw [tendsto_sup]
  constructor
  · rw [tendsto_congr' h_g_eq]
    exact tendsto_const_nhds
  · rw [tendsto_pure_left, hg0]
    exact tendsto_const_nhds
