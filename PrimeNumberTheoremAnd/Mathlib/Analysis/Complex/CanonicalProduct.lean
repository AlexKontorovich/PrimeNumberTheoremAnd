/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ`:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

The convergence results specialize the locally uniform product API for scaled Weierstrass factors
developed in `Mathlib.Analysis.Complex.WeierstrassFactor`.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Complex

/-- The canonical product `∏' n, E_m(z / a_n)` for a sequence `a`. -/
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)

@[simp] theorem canonicalProduct_def (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl

/-- The canonical product converges locally uniformly on `ℂ` under the standard summability
hypothesis. -/
theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero

/-- The canonical product is locally uniformly multipliable on `ℂ` under the standard
summability hypothesis. -/
theorem multipliableLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliableLocallyUniformlyOn

/-- The canonical product converges uniformly on compact sets under the standard summability
hypothesis. -/
theorem hasProdUniformlyOn_canonicalProduct_compact {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n)) (canonicalProduct m a) K := by
  have hloc :
      HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
        (canonicalProduct m a) K :=
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).mono (by simp : K ⊆ Set.univ)
  exact hloc.hasProdUniformlyOn_of_isCompact hK

/-- Uniform convergence on compact sets for the canonical product. -/
theorem canonicalProduct_converges_uniformOn_compact {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (canonicalProduct m a) Filter.atTop K := by
  intro K hK
  exact (hasProdUniformlyOn_iff_tendstoUniformlyOn.1
    (hasProdUniformlyOn_canonicalProduct_compact h_sum h_nonzero hK))

/-- The canonical product is holomorphic on `ℂ` under the standard summability hypothesis. -/
theorem differentiable_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    Differentiable ℂ (canonicalProduct m a) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero)
  have hfactor : ∀ i : ℕ, Differentiable ℂ (fun z ↦ weierstrassFactor m (z / a i)) := by
    intro i
    simpa using (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i))
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ (fun z ↦ ∏ n ∈ Finset.range N, weierstrassFactor m (z / a n))
          Set.univ := by
    filter_upwards with N
    simpa [differentiableOn_univ] using
      (Differentiable.fun_finsetProd (u := Finset.range N) fun i hi ↦ hfactor i)
  exact differentiableOn_univ.mp <| hloc.differentiableOn hpartial isOpen_univ

/-- The canonical product is analytic on `ℂ` under the standard summability hypothesis. -/
theorem analyticOnNhd_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    AnalyticOnNhd ℂ (canonicalProduct m a) Set.univ := by
  exact DifferentiableOn.analyticOnNhd
    (differentiableOn_univ.mpr (differentiable_canonicalProduct h_sum h_nonzero)) isOpen_univ

/-- Genus-one Weierstrass factors contribute the usual `1 / (z - a) + 1 / a` term to
the logarithmic derivative. -/
theorem logDeriv_weierstrassFactor_one_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => weierstrassFactor 1 (w / a)) z =
      1 / (z - a) + 1 / a := by
  have hE :
      (fun w : ℂ => weierstrassFactor 1 (w / a)) =
        fun w : ℂ => (1 - w / a) * exp (w / a) := by
    ext w
    simp [weierstrassFactor_def, partialLogSum_eq_sum]
  have hf : (1 - z / a) ≠ 0 := by
    intro hzero
    have hdiv : z / a = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    exact hz ((div_eq_one_iff_eq ha).1 hdiv)
  rw [hE, logDeriv_mul z hf (exp_ne_zero (z / a)) (by fun_prop) (by fun_prop)]
  have hleft : logDeriv (fun w : ℂ => 1 - w / a) z = 1 / (z - a) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => 1 - w / a) z = -(1 / a) := by
      simp [one_div]
    rw [hderiv]
    have haz : -z + a ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (Ne.symm hz)
    field_simp [ha, sub_ne_zero.mpr hz, haz]
    have haz' : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hza : z - a = -(a - z) := by ring
    rw [hza]
    field_simp [haz']
  have hright : logDeriv (fun w : ℂ => exp (w / a)) z = 1 / a := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => exp (w / a)) z =
        exp (z / a) * (1 / a) := by
      simp [one_div]
    rw [hderiv]
    field_simp [exp_ne_zero (z / a)]
  rw [hleft, hright]

/-- The canonical product vanishes at each prescribed zero `a n`. -/
@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    canonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) Filter.atTop
        (𝓝 (canonicalProduct m a (a n))) := by
    simpa [f, canonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[Filter.atTop] fun _ ↦ (0 : ℂ) := by
    refine Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero

/-- The canonical product vanishes at every point in `Set.range a`. -/
theorem canonicalProduct_eq_zero_of_mem_range {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∈ Set.range a) :
    canonicalProduct m a z = 0 := by
  rcases hz with ⟨n, rfl⟩
  exact canonicalProduct_apply_eq_zero h_sum h_nonzero n

/-- Away from the prescribed zero set `Set.range a`, the canonical product is nonzero. -/
theorem canonicalProduct_ne_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a) :
    canonicalProduct m a z ≠ 0 := by
  let f : ℕ → ℂ := fun n ↦ weierstrassFactor m (z / a n) - 1
  have hfn : ∀ n, 1 + f n ≠ 0 := by
    intro n
    have hza : z ≠ a n := by
      intro hza
      exact hz ⟨n, hza.symm⟩
    simpa [f] using (weierstrassFactor_div_ne_zero_iff (m := m) (a := a n) (z := z)
      (h_nonzero n)).2 hza
  have hnormsumm :
      Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) :=
    summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero z
  simpa [canonicalProduct, f] using
    (tprod_one_add_ne_zero_of_summable (f := f) hfn hnormsumm)

theorem differentiableOn_canonicalPartialProduct (m : ℕ) (a : ℕ → ℂ) (N : ℕ) :
    DifferentiableOn ℂ (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) Set.univ := by
  simpa [differentiableOn_univ] using
    (Differentiable.fun_finsetProd (u := Finset.range N) fun i _ =>
      (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i)))

private theorem tendsto_deriv_canonicalPartialProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    Tendsto (fun N ↦ deriv (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) (a n))
      Filter.atTop
      (𝓝 (deriv (canonicalProduct m a) (a n))) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
        (m := m) (a := a) h_sum h_nonzero)
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ
          (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) Set.univ := by
    filter_upwards with N
    exact differentiableOn_canonicalPartialProduct m a N
  simpa [canonicalProduct] using
    (hloc.deriv hpartial isOpen_univ).tendsto_at (by simp)

/-- The zero set of the canonical product is exactly `Set.range a`. -/
theorem canonicalProduct_eq_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z = 0 ↔ z ∈ Set.range a := by
  constructor
  · intro hz0
    by_contra hzrange
    exact (canonicalProduct_ne_zero h_sum h_nonzero hzrange) hz0
  · exact canonicalProduct_eq_zero_of_mem_range h_sum h_nonzero

/-- Away from `Set.range a`, the canonical product is nonzero, expressed as an iff. -/
theorem canonicalProduct_ne_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z ≠ 0 ↔ z ∉ Set.range a := by
  rw [not_iff_not]
  exact canonicalProduct_eq_zero_iff h_sum h_nonzero

/-- The logarithmic derivative of a genus-one sequence-indexed canonical product is the expected
sum of the logarithmic derivatives of the Weierstrass factors, away from the prescribed zero set. -/
theorem logDeriv_canonicalProduct_one_eq_tsum {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (2 : ℕ))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a)
    (hm : Summable (fun n : ℕ => 1 / (z - a n) + 1 / a n)) :
    logDeriv (canonicalProduct 1 a) z =
      ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
  let Φ : ℕ → ℂ → ℂ := fun n w => weierstrassFactor 1 (w / a n)
  have hf : ∀ n, Φ n z ≠ 0 := by
    intro n
    refine weierstrassFactor_ne_zero_of_ne_one 1 ?_
    intro h
    have hza : z = a n := (div_eq_one_iff_eq (h_nonzero n)).1 h
    exact hz ⟨n, hza.symm⟩
  have hd : ∀ n, DifferentiableOn ℂ (Φ n) (Set.univ : Set ℂ) := by
    intro n
    exact ((differentiable_weierstrassFactor 1).comp
      (differentiable_id.div_const (a n))).differentiableOn
  have hm' : Summable fun n => logDeriv (Φ n) z := by
    refine hm.congr ?_
    intro n
    have hza : z ≠ a n := by
      intro h
      exact hz ⟨n, h.symm⟩
    simpa [Φ] using
      (logDeriv_weierstrassFactor_one_div (a := a n) (z := z) (h_nonzero n) hza).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    simpa [Φ] using multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero
  have hnez : (∏' n, Φ n z) ≠ 0 := by
    simpa [Φ, canonicalProduct] using canonicalProduct_ne_zero h_sum h_nonzero hz
  have hlog :
      logDeriv (∏' n, Φ n ·) z = ∑' n, logDeriv (Φ n) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (canonicalProduct 1 a) z = ∑' n, logDeriv (Φ n) z := by
      simpa [Φ, canonicalProduct] using hlog
    _ = ∑' n : ℕ, (1 / (z - a n) + 1 / a n) := by
      refine tsum_congr fun n => ?_
      have hza : z ≠ a n := by
        intro h
        exact hz ⟨n, h.symm⟩
      simpa [Φ] using logDeriv_weierstrassFactor_one_div (a := a n) (z := z) (h_nonzero n) hza

end Complex
