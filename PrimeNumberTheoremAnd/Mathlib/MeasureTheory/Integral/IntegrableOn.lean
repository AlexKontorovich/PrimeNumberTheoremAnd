module

public import Architect
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Domination for `IntegrableOn`

A small `IntegrableOn` wrapper for a.e. norm domination on a restricted measure.
-/

@[expose] public section

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}

/-- If `‖f x‖ ≤ g x` a.e. on `s` and `g` is integrable on `s`, then so is `f`. -/
lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ)
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (h : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ g x) : IntegrableOn f s μ := by
  exact Integrable.mono' hg hf h

end MeasureTheory

open Set MeasureTheory

/-- Fubini's theorem for integrals restricted to two sets. -/
@[blueprint "setIntegral_integral_swap"
  (title := "Fubini on a product of sets")
  (statement := /-- If $f$ is integrable on $s\times t$ for a product of sigma-finite
    measures, then its two iterated set integrals are equal. -/)
  (proof := /-- Apply Fubini to the restricted product measure. -/)]
theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert hf.integrable
  exact Measure.prod_restrict s t


/-- Localize a set integral to any measurable set containing the support. -/
@[blueprint "integral_eq_integral_inter_of_support_subset"
  (title := "Localize an integral to the support")
  (statement := /-- If the support of $f$ is contained in a measurable set $t$,
    then $\int_s f=\int_{s\cap t} f$. -/)
  (proof := /-- Insert the indicator of $t$. -/)]
lemma SetIntegral.integral_eq_integral_inter_of_support_subset {α : Type*}
    [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set α} {f : α → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [← setIntegral_indicator ht, indicator_eq_self.2 h]

/-- Localize an integral to a closed interval containing the support. -/
@[blueprint "integral_eq_integral_inter_of_support_subset_Icc"
  (title := "Localize an integral to a closed interval")
  (statement := /-- If the support of $f$ is contained in $[a,b]\subseteq s$,
    then $\int_s f=\int_{[a,b]} f$. -/)
  (proof := /-- Intersect with the supporting interval. -/)
  (proofUses := ["integral_eq_integral_inter_of_support_subset"])]
lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]
