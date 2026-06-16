/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CanonicalProduct
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorSupport

/-!
# Indexing zeros via the divisor

This file defines index types that enumerate zeros of a meromorphic function (with multiplicity)
using `MeromorphicOn.divisor`.

The main use is in Hadamard/Weierstrass factorization, where these indices are used to build
canonical products.

## Main definitions

* `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types for zeros
  with multiplicity.
* `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.
-/

@[expose] public section


open Set

namespace Complex.Hadamard

/-!
## Index types
-/

/-- Index type enumerating zeros (with multiplicity) via the divisor. -/
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))

/-- The nonzero part of `divisorZeroIndex`. -/
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}

/-- The underlying point of a (nonzero) divisor index. -/
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1

@[simp]
lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2

/-- A (nonzero) divisor index has nonzero multiplicity at its underlying point. -/
@[simp]
lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
    simp [hdiv]
  exact hn this

lemma divisorZeroIndex₀_val_mem_divisor_support' {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f U).support := by
  simp [Function.mem_support]

lemma exists_ball_inter_divisor_support_eq_singleton_of_index
    {f : ℂ → ℂ} (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ ε > 0,
      Metric.ball (divisorZeroIndex₀_val p) ε ∩
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support =
        {divisorZeroIndex₀_val p} := by
  simpa using
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (hs := MeromorphicOn.divisor_support_discrete (f := f) (U := (Set.univ : Set ℂ)))
      (divisorZeroIndex₀_val_mem_divisor_support' (p := p))

/-- The canonical product attached to the (nonzero) divisor of `f` on `U`. -/
noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)

/-- Reindex the divisor canonical product along an equivalence. -/
theorem divisorCanonicalProduct_eq_tprod_of_equiv
    {ι : Type*} (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ)
    (e : ι ≃ divisorZeroIndex₀ f U) (z : ℂ) :
    divisorCanonicalProduct m f U z =
      ∏' i : ι, weierstrassFactor m (z / divisorZeroIndex₀_val (e i)) := by
  simpa [divisorCanonicalProduct] using
    (e.tprod_eq (fun p : divisorZeroIndex₀ f U =>
      weierstrassFactor m (z / divisorZeroIndex₀_val p))).symm

/-- If a sequence enumerates the nonzero divisor indices, the divisor-indexed product is the
corresponding canonical product. -/
theorem divisorCanonicalProduct_eq_canonicalProduct_of_equiv
    (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (e : ℕ ≃ divisorZeroIndex₀ f U) (z : ℂ) :
    divisorCanonicalProduct m f U z =
      Complex.canonicalProduct m (fun n : ℕ => divisorZeroIndex₀_val (e n)) z := by
  simpa [Complex.canonicalProduct_def] using
    divisorCanonicalProduct_eq_tprod_of_equiv (m := m) (f := f) (U := U) e z

@[simp]
lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  simp [divisorCanonicalProduct]

lemma divisorCanonicalProduct_ne_zero_at_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 ≠ 0 := by
  simp [divisorCanonicalProduct_zero]

end Complex.Hadamard
