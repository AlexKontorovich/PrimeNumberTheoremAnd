module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Series.lean — the digamma partial-fraction series.

Target:  digamma z = −γ − 1/z + ∑'_{n≥0} (1/(n+1) − 1/(z+n+1))   for z ∈ ℂ_ℤ,
the Mathlib-missing piece needed for the remaining H-Γ fields
([eq:mufacts]; see Zeta23/GammaFacts.lean).  Route (modelled on Mathlib's
Analysis/SpecialFunctions/Trigonometric/Cotangent.lean, which does the same for
sin → cot):
  1. Weierstrass factors  1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}, with
     ‖wTerm n z‖ ≤ 3(‖z‖/(n+1))² for n+1 ≥ ‖z‖  (M-test input);
  2. the finite identity  (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1+wTerm n z);
  3. N → ∞ (GammaSeq_tendsto_Gamma + tendsto_harmonic_sub_log):
       Γ(z)⁻¹ = z·e^{γz}·∏'_n (1 + wTerm n z)            [Weierstrass product]
  4. logDeriv via Complex.logDeriv_tprod_eq_tsum          [digamma series].
This file has steps 1–3; step 4 is `digamma_series` at the bottom.
-/
public import Zeta23.GammaFacts
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.PSeries

@[expose] public section

noncomputable section

namespace Zeta23
namespace DigammaSeries

open Complex Filter Topology

/-- Offset Weierstrass factor: `1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}`. -/
def wTerm (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1

lemma one_add_wTerm (n : ℕ) (z : ℂ) :
    1 + wTerm n z = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  unfold wTerm
  ring

lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The quadratic tail bound for the Weierstrass factor. -/
lemma norm_wTerm_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hwnorm : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, norm_natCast_add_one]
  have hwn : ‖w‖ ≤ 1 := by
    rw [hwnorm, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : wTerm n z = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    unfold wTerm
    ring
  have hnw2 : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖wTerm n z‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [hnw2]
                exact add_le_add hr le_rfl

        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [hwnorm]

lemma summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _

lemma summable_norm_wTerm (z : ℂ) : Summable (fun n => ‖wTerm n z‖) := by
  refine (summable_wBound ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine norm_wTerm_le ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

lemma multipliable_one_add_wTerm (z : ℂ) : Multipliable fun n => 1 + wTerm n z :=
  Complex.multipliable_one_add_of_summable ((summable_norm_wTerm z).of_norm)

/-! ### The finite identity and the Weierstrass product -/

lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

/-- The finite identity: (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1 + wTerm n z). -/
lemma inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the product of the Weierstrass factors
  have hprod : ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + wTerm n z)
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => one_add_wTerm n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  -- numeric ingredients
  have hfact_ne : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have hfactprod : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, hfactprod]
  have hsumcast : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have hzsum : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- assemble
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, hcpow, hzsum, ← hsumcast]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have hE1ne : E1 ≠ 0 := Complex.exp_ne_zero _
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hexpneg : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [hexpneg]
  field_simp

/-- **The Weierstrass product for 1/Γ** on the integer complement:
Γ(z)⁻¹ = z·e^{γz}·∏'ₙ (1 + z/(n+1))e^{−z/(n+1)}. -/
theorem inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + wTerm n z) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have hhar : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [harmonic_cast_eq]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hhar
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + wTerm n z))) :=
    (multipliable_one_add_wTerm z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + wTerm n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact inv_gammaSeq_eq hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS

/-- The logarithmic derivative of a single Weierstrass factor. -/
lemma logDeriv_one_add_wTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + wTerm n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + wTerm n s)
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact one_add_wTerm n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have hexpne : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply hzn'
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4

/-- Summability of the digamma partial-fraction series. -/
theorem summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [norm_natCast_add_one] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      norm_natCast_add_one]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp

/-- **The digamma partial-fraction series, HasSum form**:
Σₙ (1/(n+1) − 1/(z+n+1)) converges to ψ(z) + γ + 1/z on the integer complement. -/
theorem hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hγc
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun n (s : ℂ) => 1 + wTerm n s) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (summable_wBound (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖wTerm n x‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            norm_wTerm_le (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (wTerm n) := by
        unfold wTerm
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + wTerm n s) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [one_add_wTerm]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hPne : (∏' n : ℕ, (1 + wTerm n z)) ≠ 0 := by
    intro h
    have h2 := inv_gamma_eq_prod hz
    rw [← hγc, h, mul_zero] at h2
    exact inv_ne_zero hΓne h2
  have hsummable : Summable fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [hcongr]
    exact (summable_digamma_series hz).neg
  have hlogP : logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ hsummable htend hPne
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + wTerm n s := by
      unfold wTerm
      fun_prop
    exact hd.differentiableOn
  have hgdiff : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have hPdiff : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + wTerm n s)) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + wTerm n s)) := by
      filter_upwards [hopenZ.mem_nhds hz] with s hs
      have h2 := inv_gamma_eq_prod hs
      rw [← hγc] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (hgdiff z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have hldinv : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv hΓne
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have hev2 : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s) := by
    filter_upwards [hopenZ.mem_nhds hz] with s hs
    have h2 := inv_gamma_eq_prod hs
    rw [← hγc] at h2
    rw [h2]
  have hlogeq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, hev2.deriv_eq, hev2.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z :=
    logDeriv_mul z hgne hPne (hgdiff z) hPdiff
  have hldg : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    rw [← hldinv, hlogeq, hmul, hldg, hlogP]
  have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (summable_digamma_series hz).hasSum
  rwa [htsum] at h

/-- **The digamma partial-fraction series** (paper [eq:mufacts]'s parenthetical, the
keystone for the remaining H-Γ fields):
ψ(z) = −γ − 1/z + Σ'ₙ (1/(n+1) − 1/(z+n+1)) for z off the integers. -/
theorem digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  rw [(hasSum_digamma_series hz).tsum_eq]
  ring

end DigammaSeries
end Zeta23
