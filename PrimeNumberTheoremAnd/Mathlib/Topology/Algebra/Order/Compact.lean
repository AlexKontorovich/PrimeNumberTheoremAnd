import Mathlib.Topology.Algebra.Order.Compact

open Filter Set

variable {α : Type*} [LinearOrder α] [TopologicalSpace α]

theorem _root_.cocompact_le_atBot_atTop [LinearOrder α] [CompactIccSpace α] :
    cocompact α ≤ atBot ⊔ atTop := by
  refine fun s hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs.1
    obtain ⟨u, hu⟩ := mem_atTop_sets.mp hs.2
    refine ⟨Icc t u, isCompact_Icc, fun x hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ ht x (le_of_not_le h)) fun h ↦ hu x (le_of_not_le h)

theorem _root_.cocompact_le_atBot [LinearOrder α] [OrderTop α] [CompactIccSpace α] :
    cocompact α ≤ atBot := by
  refine fun _ hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
    refine ⟨Icc t ⊤, isCompact_Icc, fun _ hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ ht _ (le_of_not_le h)) (fun h ↦ (h le_top).elim)

theorem _root_.cocompact_le_atTop [LinearOrder α] [OrderBot α] [CompactIccSpace α] :
    cocompact α ≤ atTop := by
  refine fun _ hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atTop_sets.mp hs
    refine ⟨Icc ⊥ t, isCompact_Icc, fun _ hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ (h bot_le).elim) (fun h ↦ ht _ (le_of_not_le h))

private theorem _root_.le_cocompact_aux {l : Filter α}
    (h_aux : (s t : Set α) → t.Nonempty → Nonempty α → IsCompact t → tᶜ ⊆ s → s ∈ l) :
    l ≤ cocompact α := by
  refine fun s hs ↦ ?_
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
  refine (Set.eq_empty_or_nonempty t).casesOn (fun h_empty ↦ ?_) (fun h_nonempty ↦ ?_)
  · rewrite [compl_univ_iff.mpr h_empty, univ_subset_iff] at hts
    convert univ_mem
  · exact h_aux s t h_nonempty h_nonempty.nonempty ht hts

theorem _root_.atBot_le_cocompact [LinearOrder α] [NoMinOrder α] [ClosedIicTopology α] :
    atBot ≤ cocompact α := by
  refine le_cocompact_aux fun s t h_nonempty _ ht hts ↦ Filter.mem_atBot_sets.mpr ?_
  obtain ⟨a, ha⟩ := ht.exists_isLeast h_nonempty
  obtain ⟨b, hb⟩ := exists_lt a
  exact ⟨b, fun b' hb' ↦ hts <| Classical.byContradiction fun hc ↦
    LT.lt.false <| hb'.trans_lt <| hb.trans_le <| ha.2 (not_not_mem.mp hc)⟩

theorem _root_.atTop_le_cocompact [LinearOrder α] [NoMaxOrder α] [ClosedIciTopology α] :
    atTop ≤ cocompact α := by
  refine le_cocompact_aux fun s t h_nonempty _ ht hts ↦ Filter.mem_atTop_sets.mpr ?_
  obtain ⟨a, ha⟩ := ht.exists_isGreatest h_nonempty
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨b, fun b' hb' ↦ hts <| Classical.byContradiction fun hc ↦
    ha.2 (not_not_mem.mp hc) |>.trans_lt hb |>.trans_le hb' |>.false⟩

theorem _root_.atBot_atTop_le_cocompact [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
    [OrderClosedTopology α] : atBot ⊔ atTop ≤ cocompact α :=
  sup_le atBot_le_cocompact atTop_le_cocompact

theorem _root_.cocompact_eq_atBot_atTop [LinearOrder α] [NoMaxOrder α] [NoMinOrder α]
    [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atTop :=
  cocompact_le_atBot_atTop.antisymm atBot_atTop_le_cocompact

theorem _root_.cocompact_eq_atBot [LinearOrder α] [NoMinOrder α] [OrderTop α]
    [ClosedIicTopology α] [CompactIccSpace α] : cocompact α = atBot :=
  cocompact_le_atBot.antisymm atBot_le_cocompact

theorem _root_.cocompact_eq_atTop [LinearOrder α] [NoMaxOrder α] [OrderBot α]
    [ClosedIciTopology α] [CompactIccSpace α] : cocompact α = atTop :=
  cocompact_le_atTop.antisymm atTop_le_cocompact
