/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Uniformly
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Function.LocallyIntegrable
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `Asymptotics.IsBigO.integrableAtFilter`: If `f = O[l] g` on measurably generated `l`,
  `f` is strongly measurable at `l`, and `g` is integrable at `l`, then `f` is integrable at `l`.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`: If `f` is locally integrable,
  and `f =O[cocompact] g` for some `g` integrable at `cocompact`, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop`: If `f` is locally integrable,
  and `f =O[atBot] g`, `f =O[atTop] g'` for some `g`, `g'` integrable `atBot` and `atTop`
  respectively, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_eq_norm_neg`:
  If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g` for some
  `g` integrable `atTop`, then `f` is integrable.
-/

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : α → E} {g : α → F} {a b : α} {μ : Measure α} {l : Filter α}

variable [TopologicalSpace α] [SecondCountableTopology α]

namespace MeasureTheory

section LinearOrderedAddCommGroup

/-- If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g`, for some
`g` integrable at `atTop`, then `f` is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_eq_norm_neg
    [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [CompactIccSpace α] [IsMeasurablyGenerated (atTop (α := α))]
    [MeasurableNeg α] [μ.IsNegInvariant] (hf : LocallyIntegrable f μ)
    (hsymm : norm ∘ f =ᵐ[μ] norm ∘ f ∘ Neg.neg) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  refine (isEmpty_or_nonempty α).casesOn (fun _ ↦ Integrable.of_finite) (fun _ ↦ ?_)
  let a := -|Classical.arbitrary α|
  have h_int : IntegrableOn f (Ici a) μ :=
    LocallyIntegrableOn.integrableOn_of_isBigO_atTop (hf.locallyIntegrableOn _) ho hg
  have h_map_neg : (μ.restrict (Ici a)).map Neg.neg = μ.restrict (Iic (-a)) := by
    rw [show Ici a = Neg.neg ⁻¹' Iic (-a) by simp, ← measurableEmbedding_neg.restrict_map,
      Measure.map_neg_eq_self]
  have h_int_neg : IntegrableOn (f ∘ Neg.neg) (Ici a) μ := by
    refine h_int.congr' ?_ hsymm.restrict
    refine AEStronglyMeasurable.comp_aemeasurable ?_ measurable_neg.aemeasurable
    convert hf.aestronglyMeasurable.restrict
  replace h_int_neg := measurableEmbedding_neg.integrable_map_iff.mpr h_int_neg
  rewrite [h_map_neg] at h_int_neg
  refine integrableOn_univ.mp ?_
  convert integrableOn_union.mpr ⟨h_int_neg, h_int⟩
  exact (Set.Iic_union_Ici_of_le (by simp [a])).symm

end LinearOrderedAddCommGroup

end MeasureTheory
