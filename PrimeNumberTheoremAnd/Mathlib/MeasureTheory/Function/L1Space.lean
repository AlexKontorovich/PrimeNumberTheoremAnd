import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.L1Space

noncomputable section

open scoped Classical
open Topology BigOperators ENNReal MeasureTheory NNReal

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory

variable {α β γ δ : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
variable [NormedAddCommGroup β]
variable [NormedAddCommGroup γ]

section ContinuousLinearMap

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

theorem ContinuousLinearEquiv.integrable_comp_iff {φ : α → H} (L : H ≃L[𝕜] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ⟨fun h ↦ by simpa using ContinuousLinearMap.integrable_comp (L.symm : E →L[𝕜] H) h,
  fun h ↦ ContinuousLinearMap.integrable_comp (L : H →L[𝕜] E) h⟩

theorem LinearIsometryEquiv.integrable_comp_iff {φ : α → H} (L : H ≃ₗᵢ[𝕜] E) :
    Integrable (fun a : α ↦ L (φ a)) μ ↔ Integrable φ μ :=
  ContinuousLinearEquiv.integrable_comp_iff (L : H ≃L[𝕜] E)

end ContinuousLinearMap
