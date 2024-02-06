import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace Real

open Real Filter

open scoped Topology

@[mono]
theorem arctan_strictMono : StrictMono arctan := tanOrderIso.symm.strictMono

theorem arctan_injective : arctan.Injective := arctan_strictMono.injective

theorem arctan_ne_zero {x : ℝ} (hx : x ≠ 0) : arctan x ≠ 0 :=
  fun h ↦ hx <| arctan_injective (h.trans arctan_zero.symm)

theorem arctan_atTop : Tendsto arctan atTop (𝓝[<] (π / 2)) :=
  tendsto_Ioo_atTop.mp tanOrderIso.symm.tendsto_atTop

theorem arctan_atBot : Tendsto arctan atBot (𝓝[>] (-(π / 2))) :=
  tendsto_Ioo_atBot.mp tanOrderIso.symm.tendsto_atBot
