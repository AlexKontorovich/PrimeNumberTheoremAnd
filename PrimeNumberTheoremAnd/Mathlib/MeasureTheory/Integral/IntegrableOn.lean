import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory

variable {α β E F : Type*} [MeasurableSpace α]
variable [TopologicalSpace β] {l l' : Filter α} {f g : α → β} {μ ν : Measure α}

-- @[simp]
-- theorem IntegrableAtFilter.top : IntegrableAtFilter f ⊤ μ ↔ Integrable f μ := by
--   refine ⟨fun h ↦ ?_, fun h ↦ h.integrableAtFilter ⊤⟩
--   obtain ⟨s, hsf, hs⟩ := h
--   exact (integrableOn_iff_integrable_of_support_subset fun _ _ ↦ hsf _).mp hs
