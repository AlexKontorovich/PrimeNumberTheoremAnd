/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/

import Mathlib.MeasureTheory.Integral.SetIntegral
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Theta

/-!
# Uniform Asymptotics

For a family of functions `f : ι × α → E` and `g : α → E`, we can think of
`f =O[𝓟 s ×ˢ l] fun (i, x) ↦ g x` as expressing that `f i` is O(g) uniformly on `s`.

This file provides methods for constructing `=O[𝓟 s ×ˢ l]` relations (similarly `Θ`)
and deriving their consequences.
-/

open Filter

open Topology

namespace Asymptotics

variable {α ι E F : Type*} {s : Set ι}

section Basic

variable [Norm E] [Norm F] {f : ι × α → E} {g : α → F} {l : Filter α}

/-- If f = O(g) uniformly on `s`, then f_i = O(g) for any i.` -/
theorem isBigO_of_isBigOUniformly (h : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) {i : ι} (hi : i ∈ s) :
    (fun x ↦ f (i, x)) =O[l] g := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, Filter.eventually_iff_exists_mem.mpr ⟨v, hv, ?_⟩⟩
  exact fun y hy ↦ ht _ <| huv ⟨hu hi, hy⟩

/-- If f = Ω(g) uniformly on `s`, then f_i = Ω(g) for any i.` -/
theorem isBigO_rev_of_isBigOUniformly_rev (h : (g ∘ Prod.snd) =O[𝓟 s ×ˢ l] f) {i : ι} (hi : i ∈ s) :
    g =O[l] fun x ↦ f (i, x) := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, Filter.eventually_iff_exists_mem.mpr ⟨v, hv, ?_⟩⟩
  exact fun y hy ↦ ht (i, y) <| huv ⟨hu hi, hy⟩

/-- If f = Θ(g) uniformly on `s`, then f_i = Θ(g) for any i.` -/
theorem isTheta_of_isThetaUniformly (h : f =Θ[𝓟 s ×ˢ l] (g ∘ Prod.snd)) {i : ι} (hi : i ∈ s) :
    (fun x ↦ f (i, x)) =Θ[l] g :=
  ⟨isBigO_of_isBigOUniformly h.1 hi, isBigO_rev_of_isBigOUniformly_rev h.2 hi⟩

end Basic

section Order

variable [NormedAddCommGroup α] [LinearOrder α] [ProperSpace α] [NormedAddCommGroup F]

theorem isLittleO_const_fst_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (ly : Filter E) :
    (fun (_ : α × E) ↦ c) =o[atBot ×ˢ ly] Prod.fst := by
  refine ly.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  show ((fun _ ↦ c) ∘ Prod.fst) =o[atBot ×ˢ ly] (id ∘ Prod.fst)
  rewrite [← isLittleO_map, map_fst_prod]
  exact isLittleO_const_id_atBot2 c

theorem isLittleO_const_snd_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atBot] Prod.snd := by
  refine lx.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  show ((fun _ ↦ c) ∘ Prod.snd) =o[lx ×ˢ atBot] (id ∘ Prod.snd)
  rewrite [← isLittleO_map, map_snd_prod]
  exact isLittleO_const_id_atBot2 c

theorem isLittleO_const_fst_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (ly : Filter E) :
    (fun (_ : α × E) ↦ c) =o[atTop ×ˢ ly] Prod.fst := by
  refine ly.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  show ((fun _ ↦ c) ∘ Prod.fst) =o[atTop ×ˢ ly] (id ∘ Prod.fst)
  rewrite [← isLittleO_map, map_fst_prod]
  exact isLittleO_const_id_atTop2 c

theorem isLittleO_const_snd_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atTop] Prod.snd := by
  refine lx.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  show ((fun _ ↦ c) ∘ Prod.snd) =o[lx ×ˢ atTop] (id ∘ Prod.snd)
  rewrite [← isLittleO_map, map_snd_prod]
  exact isLittleO_const_id_atTop2 c

end Order

section ContinuousOn

variable [TopologicalSpace ι] {C : ι → E} {c : F}

section IsBigO

variable [SeminormedAddGroup E] [Norm F]

/-- A family of constant functions `f (i, x) = C i` is uniformly bounded w.r.t. `s` by
`⨆ i ∈ s, ‖C i‖`, if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOWithUniformlyOn_isCompact
    (hf : ContinuousOn C s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (l : Filter α) :
    IsBigOWith (sSup (norm '' (C '' s)) / ‖c‖) (𝓟 s ×ˢ l)
    (fun (i, _x) ↦ C i) fun _ => c := by
  refine isBigOWith_iff.mpr <| eventually_of_mem ?_ (fun x hx ↦ ?_) (U := s ×ˢ Set.univ)
  · exact prod_mem_prod (mem_principal_self s) univ_mem
  · rw [div_mul_cancel₀ _ hc]
    replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
    have h_sSup := hs.isLUB_sSup <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x.1, hx.1⟩
    exact h_sSup.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx.1

/-- A family of constant functions `f (i, x) = C i` is uniformly O(1) w.r.t. `s`,
if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOUniformlyOn_isCompact
    (hf : ContinuousOn C s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (l : Filter α) :
    (fun (i, _x) ↦ C i) =O[𝓟 s ×ˢ l] fun _ => c :=
  (hf.const_isBigOWithUniformlyOn_isCompact hs hc l).isBigO

end IsBigO

section IsTheta

variable [NormedAddGroup E] [SeminormedAddGroup F]

/-- A family of constant functions `f (i, x) = C i` is uniformly bounded below w.r.t. `s` by
`⊓ i ∈ s, ‖C i‖`, if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOWithUniformlyOn_isCompact_rev
    (hf : ContinuousOn C s) (hs : IsCompact s) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / sInf (norm '' (C '' s))) (𝓟 s ×ˢ l)
    (fun _ => c) fun (i, _x) ↦ C i := by
  refine isBigOWith_iff.mpr <| eventually_of_mem ?_ (fun x hx ↦ ?_) (U := s ×ˢ Set.univ)
  · exact prod_mem_prod (mem_principal_self s) univ_mem
  · rewrite [mul_comm_div]
    replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
    have h_sInf := hs.isGLB_sInf <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x.1, hx.1⟩
    refine le_mul_of_one_le_right (norm_nonneg c) <| (one_le_div ?_).mpr <|
      h_sInf.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx.1
    obtain ⟨_, ⟨x, hx, hCx⟩, hnormCx⟩ := hs.sInf_mem h_sInf.nonempty
    rewrite [← hnormCx, ← hCx]
    exact (norm_ne_zero_iff.mpr (hC x hx)).symm.lt_of_le (norm_nonneg _)

/-- A family of constant functions `f (i, x) = C i` is uniformly Ω(1) w.r.t. `s`,
if `s` is compact and `C` is continuous with no zeros on `s`. -/
theorem _root_.ContinuousOn.const_isBigOUniformlyOn_isCompact_rev
    (hf : ContinuousOn C s) (hs : IsCompact s) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    (fun _ => c) =O[𝓟 s ×ˢ l] (fun (i, _x) ↦ C i) :=
  (hf.const_isBigOWithUniformlyOn_isCompact_rev hs hC l).isBigO

/-- A family of constant functions `f (i, x) = C i` is uniformly Θ(1) w.r.t. `s`,
if `s` is compact and `C` is continuous with no zeros on `s`. -/
theorem _root_.ContinuousOn.const_isThetaUniformlyOn_isCompact (hf : ContinuousOn C s)
    (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    (fun (i, _x) ↦ C i) =Θ[𝓟 s ×ˢ l] fun _ => c :=
  ⟨hf.const_isBigOUniformlyOn_isCompact hs hc l, hf.const_isBigOUniformlyOn_isCompact_rev hs hC l⟩

end IsTheta

end ContinuousOn

section Integral -- TODO: move to Integral/Asymptotics.lean

open MeasureTheory

variable [MeasurableSpace ι] [NormedAddCommGroup E] {f : ι × α → E} {g : α → F}
  {μ : Measure ι} {l : Filter α}

/-- Let `f : X x Y → Z`. If as y → l, f(x, y) = O(g(y)) uniformly on `s : Set X` of finite measure,
then f is eventually (as y → l) integrable along `s`. -/
theorem IsBigO.eventually_integrableOn [Norm F]
    (hf : f =O[𝓟 s ×ˢ l] fun (_i, x) ↦ g x)
    (hfm : ∀ᶠ x in l, AEStronglyMeasurable (fun i ↦ f (i, x)) (μ.restrict s))
    (hs : MeasurableSet s) (hμ : μ s < ⊤) :
    ∀ᶠ x in l, IntegrableOn (fun i ↦ f (i, x)) s μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  obtain ⟨w, hwl, hw⟩ := hfm.exists_mem
  refine eventually_iff_exists_mem.mpr ⟨w ∩ v, inter_mem hwl hv, fun x hx ↦ ?_⟩
  haveI : IsFiniteMeasure (μ.restrict s) :=
    ⟨by convert hμ using 1; exact Measure.restrict_apply_univ s⟩
  refine Integrable.mono' (integrable_const (C * ‖g x‖)) (hw x hx.1) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  intro y hy
  exact ht (y, x) <| huv ⟨hu hy, hx.2⟩

variable [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let `f : X x Y → Z`. If as y → l, f(x, y) = O(g(y)) uniformly on `s : Set X` of finite measure,
then the integral of f along s is O(g(y)). -/
theorem IsBigO.set_integral_isBigO
    (hf : f =O[𝓟 s ×ˢ l] fun (_i, x) ↦ g x) (hs : MeasurableSet s) (hμ : μ s < ⊤)  :
    (fun x ↦ ∫ i in s, f (i, x) ∂μ) =O[l] g := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C * (μ s).toReal, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx ↦ ?_⟩⟩
  rewrite [mul_assoc, ← smul_eq_mul (a' := ‖g x‖), ← MeasureTheory.Measure.restrict_apply_univ,
    ← integral_const, mul_comm, ← smul_eq_mul, ← integral_smul_const]
  refine (norm_integral_le_integral_norm _).trans <|
    integral_mono_of_nonneg (univ_mem' fun _ ↦ norm_nonneg _) ?_ ?_
  · haveI : IsFiniteMeasure (μ.restrict s) :=
      ⟨by convert hμ using 1; exact Measure.restrict_apply_univ s⟩
    exact integrable_const _
  · filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
    intro y hy
    rewrite [smul_eq_mul, mul_comm]
    exact ht (y, x) <| huv ⟨hu hy, hx⟩

end Integral
