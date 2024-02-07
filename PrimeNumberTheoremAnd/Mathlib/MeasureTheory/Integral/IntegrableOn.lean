import Mathlib.MeasureTheory.Integral.IntegrableOn

open Filter MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
  {l l' : Filter α} {f g : α → β} {μ : Measure α}

protected theorem IntegrableAtFilter.norm (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖) l μ :=
  Exists.casesOn hf fun s hs ↦ ⟨s, hs.1, hs.2.norm⟩

@[simp]
theorem integrableAtFilter_top : IntegrableAtFilter f ⊤ μ ↔ Integrable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.integrableAtFilter ⊤⟩
  obtain ⟨s, hsf, hs⟩ := h
  exact (integrableOn_iff_integrable_of_support_subset fun _ _ ↦ hsf _).mp hs

theorem IntegrableAtFilter.sup_iff {l l' : Filter α} :
    IntegrableAtFilter f (l ⊔ l') μ ↔ IntegrableAtFilter f l μ ∧ IntegrableAtFilter f l' μ := by
  use fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ ↦ ⟨s ∪ t, union_mem_sup hsl htl, hs.union ht⟩
