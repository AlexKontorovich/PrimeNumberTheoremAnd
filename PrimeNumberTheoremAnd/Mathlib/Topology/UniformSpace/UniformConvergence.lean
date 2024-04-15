import Mathlib.Topology.UniformSpace.UniformConvergence

open Topology Filter Uniformity Uniform

variable {ι α β : Type*} [UniformSpace β] {l : Filter ι} [NeBot l] {p : Filter α} {b : β}
  {F : ι → α → β} {f : α → β} {L : ι → β} {ℓ : β}

theorem TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformlyOnFilter F f l p) (h2 : ∀ᶠ i in l, Tendsto (F i) p (𝓝 (L i)))
    (h3 : Tendsto L l (𝓝 ℓ)) : Tendsto f p (𝓝 ℓ) := by
  rw [tendsto_nhds_left] ; intro s hs ; change ∀ᶠ x in p, (f x, ℓ) ∈ s
  obtain ⟨t, ht, hts⟩ := comp3_mem_uniformity hs
  have l1 : ∀ᶠ i in l, (L i, ℓ) ∈ t := tendsto_nhds_left.mp h3 ht
  have l2 : ∀ᶠ i in l, ∀ᶠ x in p, (F i x, L i) ∈ t := by
    filter_upwards [h2] with i h2 using tendsto_nhds_left.mp h2 ht
  have l3 : ∀ᶠ i in l, ∀ᶠ x in p, (f x, F i x) ∈ t := (h1 t ht).curry
  obtain ⟨i, l4, l5, l6⟩ := (l1.and (l2.and l3)).exists
  filter_upwards [l5, l6] with x l5 l6 using hts ⟨F i x, l6, L i, l5, l4⟩

theorem TendstoUniformly.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformly F f l) (h2 : ∀ᶠ i in l, Tendsto (F i) p (𝓝 (L i)))
    (h3 : Tendsto L l (𝓝 ℓ)) : Tendsto f p (𝓝 ℓ) :=
  (h1.tendstoUniformlyOnFilter.mono_right le_top).tendsto_of_eventually_tendsto h2 h3
