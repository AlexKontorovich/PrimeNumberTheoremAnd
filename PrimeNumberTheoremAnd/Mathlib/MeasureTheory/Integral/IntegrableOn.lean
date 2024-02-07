import Mathlib.MeasureTheory.Integral.IntegrableOn

open Filter MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
  {l l' : Filter α} {f g : α → β} {μ : Measure α}

theorem IntegrableAtFilter.sup_iff {l l' : Filter α} :
    IntegrableAtFilter f (l ⊔ l') μ ↔ IntegrableAtFilter f l μ ∧ IntegrableAtFilter f l' μ := by
  use fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ ↦ ⟨s ∪ t, union_mem_sup hsl htl, hs.union ht⟩
