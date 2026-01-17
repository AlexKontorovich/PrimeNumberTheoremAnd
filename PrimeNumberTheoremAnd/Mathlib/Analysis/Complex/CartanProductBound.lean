import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Order
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor

/-!
## Reusable lemmas for Cartan/minimum-modulus bounds (products → exp(sum))

This file collects small, reusable “algebra + infinite product” lemmas that repeatedly occur in
Hadamard/Cartan arguments:

- bounding finite products by exponentials of finite sums;
- turning a uniform bound on finite partial products into a bound on the `HasProd` limit.

These lemmas are intentionally agnostic of Hadamard factorization and can be upstreamed.
-/

noncomputable section

namespace Complex.Hadamard

open scoped BigOperators
open Filter Finset Real Topology

/-!
### Finite products bounded by `exp(sum)`
-/

lemma Finset.prod_le_exp_sum {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm

/-!
### Infinite products: pass a bound on all partial products to the limit
-/

lemma hasProd_le_of_prod_le_exp {α : Type} {f : α → ℝ} {a : ℝ}
    (hf : HasProd f a (SummationFilter.unconditional α))
    {B : ℝ} (hB : ∀ s : Finset α, (∏ x ∈ s, f x) ≤ Real.exp B) :
    a ≤ Real.exp B :=
  hasProd_le_of_prod_le (L := (SummationFilter.unconditional α)) hf hB

lemma hasProd_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α) := by
  -- Avoid `HasProd.inv` here: `HasProd.inv` is for *topological groups* (global continuity of `inv`),
  -- while for `ℂ` we only have continuity of `inv` away from `0`, i.e. `inv₀`.
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, (fac x)⁻¹)
      (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
  have hprod :
      Tendsto (fun s : Finset α => ∏ x ∈ s, fac x)
        (SummationFilter.unconditional α).filter (𝓝 F) := by
    simpa [HasProd] using hfac
  have hinv :
      Tendsto (fun s : Finset α => (∏ x ∈ s, fac x)⁻¹)
        (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
    hprod.inv₀ hF
  refine hinv.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [Finset.prod_inv_distrib]

lemma hasProd_norm_inv_unconditional {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) := by
  simpa using (hasProd_inv_unconditional hfac hF).norm

lemma hasProd_norm_inv_le_exp_of_pointwise_le_exp {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α))
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ x, ‖(fac x)⁻¹‖ ≤ Real.exp (b x))
    (hsum : ∀ s : Finset α, (∑ x ∈ s, b x) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  by_cases hF : F = 0
  · subst hF
    simp; exact exp_nonneg B
  have hnorm :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    hasProd_norm_inv_unconditional hfac hF
  -- bound all partial products by `exp(∑ b)` then by `exp B`
  have hprod : ∀ s : Finset α, (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp B := by
    intro s
    have h0 : ∀ x ∈ s, 0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s, b x) := by
      refine (Finset.prod_le_exp_sum s (a := fun x => ‖(fac x)⁻¹‖) (b := b) h0 ?_)
      intro x hx
      simpa using hterm x
    have h2 : Real.exp (∑ x ∈ s, b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (hsum s)
    exact h1.trans h2
  exact hasProd_le_of_prod_le_exp hnorm hprod

end Complex.Hadamard
