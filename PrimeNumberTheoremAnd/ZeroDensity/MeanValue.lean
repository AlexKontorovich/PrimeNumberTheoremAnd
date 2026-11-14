/-
Copyright (c) 2026 Devon Wright. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright (formalized with Grok Bot)
-/

module

public import PrimeNumberTheoremAnd.ZetaBounds

/-!
# Mean value theorem for generalized Dirichlet polynomials (explicit form)

For `F(t) = ∑_{n ∈ S} a n * exp(-i t λ n)` with distinct real frequencies `λ`,
  `|∫_0^T |F|^2 - T ∑ |a n|^2| ≤ ∑_{m ≠ n} 2 |a m| |a n| / |λ n - λ m|`.
Specializing `λ n = log n` gives the Dirichlet polynomial case `∑ a n n^{-it}`.
-/

@[expose] public section

open Complex Finset

namespace ZeroDensity

variable {ι : Type*}

/-- Generalized Dirichlet polynomial `∑ a n * exp(-i t λ n)`. -/
noncomputable def dpoly (S : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * cexp (-((t : ℂ) * (lam n : ℂ)) * I)

lemma norm_integral_exp_le (c T : ℝ) (hc : c ≠ 0) :
    ‖∫ t in (0:ℝ)..T, cexp ((t : ℂ) * (c : ℂ) * I)‖ ≤ 2 / |c| := by
  have hcI : (c : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hc) I_ne_zero
  have h : (fun t : ℝ => cexp ((t : ℂ) * (c : ℂ) * I)) =
      fun t : ℝ => cexp (((c : ℂ) * I) * t) := by
    funext t; ring_nf
  rw [h, integral_exp_mul_complex hcI]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [norm_div, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < |c| := abs_pos.mpr hc
  rw [div_le_div_iff_of_pos_right hpos]
  calc ‖cexp ((c : ℂ) * I * (T : ℂ)) - 1‖ ≤ ‖cexp ((c : ℂ) * I * (T : ℂ))‖ + ‖(1:ℂ)‖ :=
        norm_sub_le _ _
    _ = 2 := by
        have : (c : ℂ) * I * (T : ℂ) = ((c * T : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num

lemma mul_conj_dpoly (S : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (t : ℝ) :
    dpoly S a lam t * (starRingEnd ℂ) (dpoly S a lam t) =
      ∑ m ∈ S, ∑ n ∈ S, a m * (starRingEnd ℂ) (a n) *
        cexp ((t : ℂ) * ((lam n - lam m : ℝ) : ℂ) * I) := by
  unfold dpoly
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, conj_ofReal, conj_I]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2; push_cast; ring

lemma continuous_exp_term (c : ℝ) : Continuous fun t : ℝ => cexp ((t : ℂ) * (c : ℂ) * I) := by
  fun_prop

/-- Exact expansion of the mean square. -/
lemma integral_mul_conj (S : Finset ι) (a : ι → ℂ) (lam : ι → ℝ) (T : ℝ) :
    ∫ t in (0:ℝ)..T, dpoly S a lam t * (starRingEnd ℂ) (dpoly S a lam t) =
      ∑ m ∈ S, ∑ n ∈ S, a m * (starRingEnd ℂ) (a n) *
        ∫ t in (0:ℝ)..T, cexp ((t : ℂ) * ((lam n - lam m : ℝ) : ℂ) * I) := by
  simp_rw [mul_conj_dpoly]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      exact intervalIntegral.integral_const_mul _ _
    · intro n _
      exact ((continuous_exp_term _).const_mul _).intervalIntegrable _ _
  · intro m _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- **Explicit mean value theorem** for generalized Dirichlet polynomials with
distinct real frequencies. -/
@[blueprint
  "zd-mvt-explicit"
  (title := "Explicit mean value inequality for generalized Dirichlet polynomials")
  (statement := /--
    Let $S$ be a finite set, $a_n\in\mathbb{C}$, and let $\lambda_n\in\mathbb{R}$ be distinct for $n\in S$.
    Put $F(t)=\sum_{n\in S}a_n e^{-i\lambda_n t}$. Then for every real $T$,
    $$\Bigl|\int_0^T|F(t)|^2\,dt-T\sum_{n\in S}|a_n|^2\Bigr|
      \le\sum_{m\ne n}\frac{2|a_m||a_n|}{|\lambda_n-\lambda_m|}.$$
  -/)]
theorem mean_value_explicit [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) (lam : ι → ℝ)
    (hinj : Set.InjOn lam S) (T : ℝ) :
    |(∫ t in (0:ℝ)..T, ‖dpoly S a lam t‖ ^ 2) - T * ∑ n ∈ S, ‖a n‖ ^ 2| ≤
      ∑ m ∈ S, ∑ n ∈ S.erase m, 2 * ‖a m‖ * ‖a n‖ / |lam n - lam m| := by
  have hcast : (((∫ t in (0:ℝ)..T, ‖dpoly S a lam t‖ ^ 2) : ℝ) : ℂ) =
      ∫ t in (0:ℝ)..T, dpoly S a lam t * (starRingEnd ℂ) (dpoly S a lam t) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, show ((((∫ t in (0:ℝ)..T, ‖dpoly S a lam t‖ ^ 2) -
      T * ∑ n ∈ S, ‖a n‖ ^ 2 : ℝ)) : ℂ) = ((∫ t in (0:ℝ)..T, ‖dpoly S a lam t‖ ^ 2 : ℝ) : ℂ)
      - (T : ℂ) * ∑ n ∈ S, ((‖a n‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [hcast, integral_mul_conj]
  -- split diagonal
  have hdiag : ∀ m ∈ S, ∑ n ∈ S, a m * (starRingEnd ℂ) (a n) *
      (∫ t in (0:ℝ)..T, cexp ((t : ℂ) * ((lam n - lam m : ℝ) : ℂ) * I)) =
      (T : ℂ) * ((‖a m‖ ^ 2 : ℝ) : ℂ) + ∑ n ∈ S.erase m, a m * (starRingEnd ℂ) (a n) *
      (∫ t in (0:ℝ)..T, cexp ((t : ℂ) * ((lam n - lam m : ℝ) : ℂ) * I)) := by
    intro m hm
    rw [← Finset.add_sum_erase _ _ hm]
    congr 1
    simp only [sub_self, ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [Finset.sum_congr rfl hdiag, Finset.sum_add_distrib, ← Finset.mul_sum, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hne : lam n - lam m ≠ 0 := by
    intro h
    exact (Finset.ne_of_mem_erase hn) (hinj (Finset.mem_of_mem_erase hn) hm (by linarith))
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hb := norm_integral_exp_le (lam n - lam m) T hne
  calc ‖a m‖ * ‖a n‖ * ‖∫ t in (0:ℝ)..T, cexp ((t : ℂ) * ((lam n - lam m : ℝ) : ℂ) * I)‖
      ≤ ‖a m‖ * ‖a n‖ * (2 / |lam n - lam m|) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * ‖a m‖ * ‖a n‖ / |lam n - lam m| := by ring

end ZeroDensity
