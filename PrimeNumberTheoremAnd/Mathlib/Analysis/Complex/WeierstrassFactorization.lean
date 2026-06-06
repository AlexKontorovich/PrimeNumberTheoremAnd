/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CanonicalProduct
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weierstrass factorization with prescribed zeros

This file expresses the variable-genus Weierstrass product into prescribed-zero existence theorems.
The first endpoint treats nonzero sequences escaping to infinity; the final wrapper also allows a
finite-order zero at the origin by multiplying by a monomial.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Complex

/-- The variable-genus canonical product `∏' n, E_{m n}(z / a n)`. -/
def variableCanonicalProduct (m : ℕ → ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor (m n) (z / a n)

@[simp]
theorem variableCanonicalProduct_def (m : ℕ → ℕ) (a : ℕ → ℂ) (z : ℂ) :
    variableCanonicalProduct m a z = ∏' n : ℕ, weierstrassFactor (m n) (z / a n) :=
  rfl

/-- The variable-genus canonical product converges locally uniformly under the standard local
Weierstrass summability hypotheses. -/
theorem hasProdLocallyUniformlyOn_variableCanonicalProduct {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (variableCanonicalProduct m a) Set.univ := by
  simpa [variableCanonicalProduct] using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := m) (a := a) hsmall hsumm

/-- The variable-genus canonical product is locally uniformly multipliable under the standard local
Weierstrass summability hypotheses. -/
theorem multipliableLocallyUniformlyOn_variableCanonicalProduct {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_variableCanonicalProduct
      (m := m) (a := a) hsmall hsumm).multipliableLocallyUniformlyOn

/-- The variable-genus canonical product is entire under the standard local Weierstrass
summability hypotheses. -/
theorem differentiable_variableCanonicalProduct {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    Differentiable ℂ (variableCanonicalProduct m a) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_variableCanonicalProduct (m := m) (a := a) hsmall hsumm)
  have hfactor : ∀ i : ℕ, Differentiable ℂ (fun z ↦ weierstrassFactor (m i) (z / a i)) := by
    intro i
    simpa using (differentiable_weierstrassFactor (m i)).comp (differentiable_id.div_const (a i))
  have hpartial :
      ∀ᶠ N in atTop,
        DifferentiableOn ℂ
          (fun z ↦ ∏ n ∈ Finset.range N, weierstrassFactor (m n) (z / a n))
          Set.univ := by
    filter_upwards with N
    simpa [differentiableOn_univ] using
      (Differentiable.fun_finset_prod (u := Finset.range N) fun i _ ↦ hfactor i)
  exact differentiableOn_univ.mp <| hloc.differentiableOn hpartial isOpen_univ

/-- If `‖a n‖ → ∞`, then every compact radius is eventually at most half of `‖a n‖`. -/
theorem eventually_le_norm_div_two_of_tendsto_norm_atTop {a : ℕ → ℂ}
    (ha : Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop) :
    ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  filter_upwards [ha.eventually_ge_atTop (2 * R)] with n hn
  linarith

/-- Degree choice for the Weierstrass prescribed-zero theorem: choosing genus `m n = n` makes the
Weierstrass majorants summable on every compact radius once `‖a n‖ → ∞`. -/
theorem summable_weierstrass_degree_choice_of_tendsto_norm_atTop {a : ℕ → ℂ}
    (ha : Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop) :
    ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (n + 1) / ‖a n‖ ^ (n + 1)) := by
  intro R hR
  have hgeom₀ : Summable (fun n : ℕ ↦ ((1 / 2 : ℝ) ^ n)) :=
    summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hgeom₁ : Summable (fun n : ℕ ↦ ((1 / 2 : ℝ) ^ (n + 1))) :=
    (summable_nat_add_iff 1).mpr hgeom₀
  have hgeom : Summable (fun n : ℕ ↦ 4 * ((1 / 2 : ℝ) ^ (n + 1))) :=
    hgeom₁.mul_left 4
  refine Summable.of_norm_bounded_eventually_nat
    (E := ℝ)
    (f := fun n : ℕ ↦ 4 * R ^ (n + 1) / ‖a n‖ ^ (n + 1))
    (g := fun n : ℕ ↦ 4 * ((1 / 2 : ℝ) ^ (n + 1)))
    hgeom ?_
  filter_upwards [ha.eventually_ge_atTop (2 * max R 1)] with n hn
  have hnorm_pos : 0 < ‖a n‖ := by nlinarith [hn, le_max_right R (1 : ℝ)]
  have hratio : R / ‖a n‖ ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hnorm_pos]
    nlinarith [hn, le_max_left R (1 : ℝ)]
  have hratio_nonneg : 0 ≤ R / ‖a n‖ := div_nonneg hR hnorm_pos.le
  have hnum_nonneg : 0 ≤ 4 * R ^ (n + 1) :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg hR (n + 1))
  have hden_nonneg : 0 ≤ ‖a n‖ ^ (n + 1) :=
    pow_nonneg (norm_nonneg (a n)) (n + 1)
  have hterm_nonneg : 0 ≤ 4 * R ^ (n + 1) / ‖a n‖ ^ (n + 1) :=
    div_nonneg hnum_nonneg hden_nonneg
  rw [Real.norm_of_nonneg hterm_nonneg]
  have hpow :
      (R / ‖a n‖) ^ (n + 1) ≤ ((1 / 2 : ℝ) ^ (n + 1)) :=
    pow_le_pow_left₀ hratio_nonneg hratio (n + 1)
  calc
    4 * R ^ (n + 1) / ‖a n‖ ^ (n + 1)
        = 4 * (R ^ (n + 1) / ‖a n‖ ^ (n + 1)) := by rw [mul_div_assoc]
    _ = 4 * (R / ‖a n‖) ^ (n + 1) := by rw [div_pow]
    _ ≤ 4 * ((1 / 2 : ℝ) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)

/-- For sequences escaping to infinity, the degree choice `m n = n` gives locally uniform
convergence of the prescribed-zero Weierstrass product. -/
theorem hasProdLocallyUniformlyOn_variableCanonicalProduct_nat {a : ℕ → ℂ}
    (ha : Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor n (z / a n))
      (variableCanonicalProduct (fun n ↦ n) a) Set.univ :=
  hasProdLocallyUniformlyOn_variableCanonicalProduct
    (m := fun n ↦ n) (a := a)
    (eventually_le_norm_div_two_of_tendsto_norm_atTop ha)
    (summable_weierstrass_degree_choice_of_tendsto_norm_atTop ha)

/-- The degree-choice Weierstrass product is entire for sequences escaping to infinity. -/
theorem differentiable_variableCanonicalProduct_nat {a : ℕ → ℂ}
    (ha : Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop) :
    Differentiable ℂ (variableCanonicalProduct (fun n ↦ n) a) :=
  differentiable_variableCanonicalProduct
    (m := fun n ↦ n) (a := a)
    (eventually_le_norm_div_two_of_tendsto_norm_atTop ha)
    (summable_weierstrass_degree_choice_of_tendsto_norm_atTop ha)

/-- The variable-genus product vanishes at each prescribed nonzero point. -/
theorem variableCanonicalProduct_apply_eq_zero {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    variableCanonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor (m k) (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_variableCanonicalProduct
      (m := m) (a := a) hsmall hsumm).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) atTop
        (𝓝 (variableCanonicalProduct m a (a n))) := by
    simpa [f, variableCanonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[atTop] fun _ ↦ (0 : ℂ) := by
    refine eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero

/-- The variable-genus product vanishes at every point in the prescribed range. -/
theorem variableCanonicalProduct_eq_zero_of_mem_range {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) {z : ℂ} (hz : z ∈ Set.range a) :
    variableCanonicalProduct m a z = 0 := by
  rcases hz with ⟨n, rfl⟩
  exact variableCanonicalProduct_apply_eq_zero hsmall hsumm h_nonzero n

lemma summable_norm_variable_weierstrassFactor_div_sub_one {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1)))
    (z : ℂ) :
    Summable (fun n : ℕ ↦ ‖weierstrassFactor (m n) (z / a n) - 1‖) := by
  refine Summable.of_norm_bounded_eventually_nat (hsumm ‖z‖ (norm_nonneg z)) ?_
  filter_upwards [hsmall ‖z‖ (norm_nonneg z)] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) (a := a n) (z := z) hn

/-- Away from the prescribed range, the variable-genus product is nonzero. -/
theorem variableCanonicalProduct_ne_zero {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) {z : ℂ} (hz : z ∉ Set.range a) :
    variableCanonicalProduct m a z ≠ 0 := by
  let f : ℕ → ℂ := fun n ↦ weierstrassFactor (m n) (z / a n) - 1
  have hfn : ∀ n, 1 + f n ≠ 0 := by
    intro n
    have hza : z ≠ a n := by
      intro hza
      exact hz ⟨n, hza.symm⟩
    simpa [f] using (weierstrassFactor_div_ne_zero_iff (m := m n) (a := a n) (z := z)
      (h_nonzero n)).2 hza
  have hnormsumm : Summable (fun n : ℕ ↦ ‖f n‖) := by
    simpa [f] using summable_norm_variable_weierstrassFactor_div_sub_one hsmall hsumm z
  simpa [variableCanonicalProduct, f] using
    (tprod_one_add_ne_zero_of_summable (f := f) hfn hnormsumm)

/-- The zero set of the variable-genus product is exactly the prescribed range. -/
theorem variableCanonicalProduct_eq_zero_iff {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) {z : ℂ} :
    variableCanonicalProduct m a z = 0 ↔ z ∈ Set.range a := by
  constructor
  · intro hz0
    by_contra hzrange
    exact (variableCanonicalProduct_ne_zero hsmall hsumm h_nonzero hzrange) hz0
  · exact variableCanonicalProduct_eq_zero_of_mem_range hsmall hsumm h_nonzero

/-- Weierstrass prescribed-zero theorem for nonzero sequences escaping to infinity. The produced
entire function has zero set exactly `Set.range a`. While the sequence intrinsically supplies
multiplicities, this theorem characterizes only the vanishing locus. -/
theorem exists_differentiable_prescribedZeros_of_tendsto_norm_atTop
    (a : ℕ → ℂ) (ha : Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop)
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ z : ℂ, f z = 0 ↔ z ∈ Set.range a := by
  refine ⟨variableCanonicalProduct (fun n ↦ n) a,
    differentiable_variableCanonicalProduct_nat ha, ?_⟩
  intro z
  exact variableCanonicalProduct_eq_zero_iff
    (m := fun n ↦ n) (a := a)
    (eventually_le_norm_div_two_of_tendsto_norm_atTop ha)
    (summable_weierstrass_degree_choice_of_tendsto_norm_atTop ha)
    h_nonzero

/-- Weierstrass prescribed-zero theorem with a prescribed finite-order zero at the origin and a
nonzero sequence of roots escaping to infinity. The theorem characterizes the vanishing locus; it
does not assert the exact analytic order at each prescribed zero. -/
theorem exists_differentiable_prescribedZeros
    (k : ℕ) (a : ℕ → ℂ) (ha : Tendsto (fun n : ℕ ↦ ‖a n‖) atTop atTop)
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z : ℂ, f z = 0 ↔ (z = 0 ∧ k ≠ 0) ∨ z ∈ Set.range a := by
  rcases exists_differentiable_prescribedZeros_of_tendsto_norm_atTop a ha h_nonzero with
    ⟨g, hg_diff, hg_zero⟩
  refine ⟨fun z ↦ z ^ k * g z, (differentiable_id.pow k).mul hg_diff, ?_⟩
  intro z
  simp only [mul_eq_zero, pow_eq_zero_iff', hg_zero z]

end Complex
