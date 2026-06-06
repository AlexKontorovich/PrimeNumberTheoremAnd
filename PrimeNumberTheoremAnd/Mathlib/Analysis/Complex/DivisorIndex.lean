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
* `Complex.Hadamard.centeredDivisorZeroIndex`,
  `Complex.Hadamard.centeredDivisorCanonicalProduct`: translated versions for products centered at
  an arbitrary point `c`.
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

/-! ## Centered products -/

/-- Nonzero divisor indices for `f`, translated so that the center `c` is treated as the origin.

An index `p : centeredDivisorZeroIndex c f` corresponds to a zero of `f` at
`c + divisorZeroIndex₀_val p`, and the coordinate `divisorZeroIndex₀_val p` is nonzero.  This is
the centered analogue of Tao's convention of extracting the zero at the origin separately. -/
abbrev centeredDivisorZeroIndex (c : ℂ) (f : ℂ → ℂ) : Type :=
  divisorZeroIndex₀ (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ)

/-- The underlying centered coordinate of an index. -/
abbrev centeredDivisorZeroIndex_coord {c : ℂ} {f : ℂ → ℂ}
    (p : centeredDivisorZeroIndex c f) : ℂ :=
  divisorZeroIndex₀_val p

/-- The actual zero location corresponding to a centered divisor index. -/
abbrev centeredDivisorZeroIndex_val {c : ℂ} {f : ℂ → ℂ}
    (p : centeredDivisorZeroIndex c f) : ℂ :=
  c + centeredDivisorZeroIndex_coord p

@[simp]
lemma centeredDivisorZeroIndex_val_sub_center {c : ℂ} {f : ℂ → ℂ}
    (p : centeredDivisorZeroIndex c f) :
    centeredDivisorZeroIndex_val p - c = centeredDivisorZeroIndex_coord p := by
  simp [centeredDivisorZeroIndex_val, centeredDivisorZeroIndex_coord]

@[simp]
lemma centeredDivisorZeroIndex_coord_ne_zero {c : ℂ} {f : ℂ → ℂ}
    (p : centeredDivisorZeroIndex c f) :
    centeredDivisorZeroIndex_coord p ≠ 0 :=
  divisorZeroIndex₀_val_ne_zero p

@[simp]
lemma centeredDivisorZeroIndex_val_sub_center_ne_zero {c : ℂ} {f : ℂ → ℂ}
    (p : centeredDivisorZeroIndex c f) :
    centeredDivisorZeroIndex_val p - c ≠ 0 := by
  simp

@[simp]
lemma centeredDivisorZeroIndex_val_ne_center {c : ℂ} {f : ℂ → ℂ}
    (p : centeredDivisorZeroIndex c f) :
    centeredDivisorZeroIndex_val p ≠ c := by
  intro h
  exact centeredDivisorZeroIndex_val_sub_center_ne_zero p (by simp [h])

/-- Canonical product centered at `c`: the zero at `c` is omitted from the product and is handled
by the monomial `(z - c) ^ analyticOrderNatAt f c` in centered Hadamard factorization. -/
noncomputable def centeredDivisorCanonicalProduct (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏' p : centeredDivisorZeroIndex c f,
    weierstrassFactor m ((z - c) / centeredDivisorZeroIndex_coord p)

/-- The centered product is the origin-centered product of the translated function, evaluated at
the centered coordinate. -/
theorem centeredDivisorCanonicalProduct_eq_divisorCanonicalProduct
    (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    centeredDivisorCanonicalProduct m c f z =
      divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c) := by
  rfl

/-- Reindex the centered divisor canonical product along an equivalence. -/
theorem centeredDivisorCanonicalProduct_eq_tprod_of_equiv
    {ι : Type*} (m : ℕ) (c : ℂ) (f : ℂ → ℂ)
    (e : ι ≃ centeredDivisorZeroIndex c f) (z : ℂ) :
    centeredDivisorCanonicalProduct m c f z =
      ∏' i : ι, weierstrassFactor m ((z - c) / centeredDivisorZeroIndex_coord (e i)) := by
  simpa [centeredDivisorCanonicalProduct] using
    (e.tprod_eq (fun p : centeredDivisorZeroIndex c f =>
      weierstrassFactor m ((z - c) / centeredDivisorZeroIndex_coord p))).symm

/-- If a sequence enumerates the centered nonzero divisor indices, the centered divisor-indexed
product is the corresponding canonical product in the centered coordinate. -/
theorem centeredDivisorCanonicalProduct_eq_canonicalProduct_of_equiv
    (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (e : ℕ ≃ centeredDivisorZeroIndex c f) (z : ℂ) :
    centeredDivisorCanonicalProduct m c f z =
      Complex.canonicalProduct m (fun n : ℕ => centeredDivisorZeroIndex_coord (e n)) (z - c) := by
  simpa [Complex.canonicalProduct_def] using
    centeredDivisorCanonicalProduct_eq_tprod_of_equiv (m := m) (c := c) (f := f) e z

@[simp]
lemma centeredDivisorCanonicalProduct_center (m : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    centeredDivisorCanonicalProduct m c f c = 1 := by
  classical
  simp [centeredDivisorCanonicalProduct]

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
  classical
  simp [divisorCanonicalProduct]

lemma divisorCanonicalProduct_ne_zero_at_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 ≠ 0 := by
  simp [divisorCanonicalProduct_zero]

end Complex.Hadamard
