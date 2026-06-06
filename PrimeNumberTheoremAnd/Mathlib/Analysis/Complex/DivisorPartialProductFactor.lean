/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorComplement
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Uniqueness


/-!
# Local factorization of finite divisor-indexed products

This file packages the finite-order computation for partial products of Weierstrass factors indexed
by `divisorZeroIndex₀`, and deduces a local factorization at a point `z₀` once the finset contains
the full fiber over `z₀`.
-/

@[expose] public section

noncomputable section

open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Finite product multiplicity at a point

For a finite product of elementary factors indexed by divisor-indices, the analytic order at `z₀`
equals the number of indices whose value is exactly `z₀`.
-/

theorem analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card : ℕ∞) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : divisorZeroIndex₀_val p = z₀
    · have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀_val q)) z₀ := by
        simpa [divisorPartialProduct] using analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card + 1 := by
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (analyticOrderAt_weierstrassFactor_div_self (m := m) (a := divisorZeroIndex₀_val p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter
          (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
            (z / divisorZeroIndex₀_val q)) z₀ = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hcard, Nat.add_comm]
    · have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        exact (differentiable_weierstrassFactor_divisorZeroIndex₀ m p).analyticAt z₀
      have hfac0 : analyticOrderAt (fun z : ℂ => weierstrassFactor m
          (z / divisorZeroIndex₀_val p)) z₀ = 0 := by
        have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
        have hval : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
          have : (z₀ / divisorZeroIndex₀_val p) ≠ 1 := by
            intro h1
            have : z₀ = divisorZeroIndex₀_val p := by
              have : z₀ = (z₀ / divisorZeroIndex₀_val p) * (divisorZeroIndex₀_val p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          exact (weierstrassFactor_ne_zero_iff m (z₀ / divisorZeroIndex₀_val p)).2 this
        simpa using (han_fac.analyticOrderAt_eq_zero).2 (by simpa using hval)
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m
          (z / divisorZeroIndex₀_val q)) z₀ := by
        simpa [divisorPartialProduct] using analyticAt_divisorPartialProduct m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m
        (z / divisorZeroIndex₀_val q)) z₀
            = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have hfac0' : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using hfac0
                      simp [hfac0']
        _ = ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm

theorem analyticOrderNatAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderNatAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ =
      (s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card := by
  simpa [analyticOrderNatAt] using
    (congrArg ENat.toNat
      (analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀ (m := m) (f := f) (s := s)
      (z₀ := z₀)))

theorem analyticOrderAt_partialProduct_eq_fiberCard_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀ = ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : divisorZeroIndex₀_val p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv
    · intro hp_fiber
      have hpv : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h

theorem exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    simpa [F, divisorPartialProduct] using analyticAt_divisorPartialProduct m f s z₀
  have hOrder :
      analyticOrderAt F z₀ =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    simpa [F] using
      (analyticOrderAt_partialProduct_eq_fiberCard_of_subset (m := m)
      (f := f) (z₀ := z₀) (s := s) hs)
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (divisorZeroIndex₀_fiberFinset
    (f := f) z₀).card)).1 ?_
  simp [hOrder]

end Complex.Hadamard
