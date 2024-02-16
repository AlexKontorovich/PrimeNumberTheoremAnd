import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Order.Compact
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal BigOperators

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [NormedAddCommGroup E]
  {f : X → E} {μ : Measure X}

theorem integrable_iff_integrableAtFilter_atBot_atTop [LinearOrder X] [CompactIccSpace X] :
    Integrable f μ ↔
    (IntegrableAtFilter f atBot μ ∧ IntegrableAtFilter f atTop μ) ∧ LocallyIntegrable f μ := by
  use fun hf ↦ ⟨⟨hf.integrableAtFilter _, hf.integrableAtFilter _⟩, hf.locallyIntegrable⟩
  refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
  exact (IntegrableAtFilter.sup_iff.mpr h.1).filter_mono cocompact_le_atBot_atTop

theorem integrable_iff_integrableAtFilter_atBot [LinearOrder X] [OrderTop X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrable f μ := by
  use fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
  exact h.1.filter_mono cocompact_le_atBot

theorem integrable_iff_integrableAtFilter_atTop [LinearOrder X] [OrderBot X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrable f μ := by
  use fun hf ↦ ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  refine fun h ↦ integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
  exact h.1.filter_mono cocompact_le_atTop

variable {a : X}

theorem integrableOn_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrableOn f (Iic a) μ := by
  refine ⟨fun h ↦ ⟨⟨Iic a, Iic_mem_atBot a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ ↦ ?_⟩
  haveI : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atBot_sets.mp hsl
  refine (integrableOn_union.mpr ⟨hs.mono ha' le_rfl, ?_⟩).mono Iic_subset_Iic_union_Icc le_rfl
  exact h.integrableOn_compact_subset Icc_subset_Iic_self isCompact_Icc

theorem integrableOn_Ici_iff_integrableAtFilter_atTop [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Ici a) μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrableOn f (Ici a) μ := by
  refine ⟨fun h ↦ ⟨⟨Ici a, Ici_mem_atTop a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ ↦ ?_⟩
  haveI : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atTop_sets.mp hsl
  refine (integrableOn_union.mpr ⟨?_, hs.mono ha' le_rfl⟩).mono Ici_subset_Icc_union_Ici le_rfl
  exact h.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
