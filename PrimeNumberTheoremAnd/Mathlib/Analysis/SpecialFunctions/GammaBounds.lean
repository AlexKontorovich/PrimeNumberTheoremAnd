/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Data.Real.StarOrdered

/-!
# Bounds for `Complex.Gammaℝ`

Cauchy bounds for derivatives of Deligne's real Gamma factor.
-/

@[expose] public section

noncomputable section

open Complex Real Set Metric
open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Real
namespace Gamma

-- On `[1 / 2, 1]`, convexity bounds `Γ` by its value at `1 / 2`.
private lemma le_Gamma_one_half {a : ℝ} (ha_low : 1 / 2 ≤ a) (ha_high : a ≤ 1) :
    Real.Gamma a ≤ Real.Gamma (1 / 2) := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h_half : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h_sqrt_pi_gt_one : 1 < Real.sqrt Real.pi := by
    rw [← Real.sqrt_one, Real.sqrt_lt_sqrt_iff (by aesop)]
    exact (by norm_num : (1 : ℝ) < 3).trans Real.pi_gt_three
  let t := 2 - 2 * a
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have ha_conv : a = t * (1 / 2) + (1 - t) * 1 := by
    field_simp [t]
    ring
  have hconv := h_convex.2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at hconv
  calc
    Real.Gamma a = Real.Gamma (t * (1 / 2) + (1 - t) * 1) := by rw [ha_conv]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma 1 := hconv
    _ = t * Real.Gamma (1 / 2) + (1 - t) * 1 := by rw [h1]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma (1 / 2) := by
      have hone : 1 ≤ Real.Gamma (1 / 2) := by
        rw [h_half]
        exact le_of_lt h_sqrt_pi_gt_one
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left
          (mul_le_mul_of_nonneg_left hone (sub_nonneg_of_le ht_le_one))
          (t * Real.Gamma (1 / 2))
    _ = Real.Gamma (1 / 2) := by ring

end Gamma
end Real

open Gamma Real

-- Tail bound for Euler's Gamma integral on `1 / 2 ≤ a ≤ 1`.
private lemma integral_exp_neg_rpow_Ioi_one_le {a : ℝ}
    (ha_low : (1 / 2 : ℝ) ≤ a) (ha_high : a ≤ 1) :
    ∫ t in Ioi 1, Real.exp (-t) * t ^ (a - 1) ≤ Real.sqrt Real.pi := by
  have h_split :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) ∂volume) =
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) ∂volume) +
        (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1) ∂volume) := by
    have h_int_Ioc :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioc 0 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set Ioc_subset_Ioi_self
    have h_int_Ioi :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioi 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set (by
        intro x hx
        exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi h_int_Ioc h_int_Ioi)
  have h_nonneg :
      (0 : ℝ) ≤ ∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht.1) _)
  have h_step₁ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := by
    exact le_add_of_nonneg_right h_nonneg
  have h_step₂ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) =
        ∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) := by
    simpa [add_comm] using h_split.symm
  have h_step₃ :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1)) = Real.Gamma a := by
    simpa using (Real.Gamma_eq_integral (by linarith : 0 < a)).symm
  have h_le_Gamma :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma a := by
    have := h_step₁
    simpa [h_step₂, h_step₃] using this
  have h_tail :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma (1 / 2) :=
    h_le_Gamma.trans (Gamma.le_Gamma_one_half ha_low ha_high)
  have hGammaHalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hGammaInv : Real.Gamma (2⁻¹) = Real.sqrt Real.pi := by
    simp_rw [inv_eq_one_div]
    aesop
  simpa [hGammaHalf, hGammaInv] using h_tail

private lemma integral_rpow_Ioc_zero_one {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
  have h_eq : ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = ∫ t in (0)..(1), t ^ (s - 1) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  rw [h_eq]
  have hne : s - 1 ≠ -1 := by linarith
  have hlt : -1 < s - 1 := by linarith
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hlt))
  simp [one_rpow, zero_rpow hs.ne'] at h
  simp only [one_div, h]

namespace Complex
namespace Gamma

/-- If `0 < a ≤ re w ≤ 1`, then `‖Γ(w)‖ ≤ 1 / a + √π`. -/
lemma norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le {w : ℂ} {a : ℝ}
    (ha_pos : 0 < a) (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  set f : ℝ → ℂ := fun t ↦ Complex.exp (-t) * t ^ (w - 1)
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (w.re - 1)
  have hw_pos : 0 < w.re := ha_pos.trans_le hw
  have hΓ : Complex.Gamma w = ∫ t in Ioi (0 : ℝ), f t := by
    rw [Complex.Gamma_eq_integral hw_pos]
    simp [Complex.GammaIntegral, f]
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), f t‖ := by
    simp [hΓ]
  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖f t‖
        = ∫ t in Ioi (0 : ℝ), g t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    simp [f, g, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)]
  have h_split :
      (∫ t in Ioi (0 : ℝ), g t)
        = (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
    have hIoc : IntegrableOn g (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn g (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := 0) (b := 1))
          measurableSet_Ioi hIoc hIoi)
  have h_ae_drop :
      (fun t : ℝ ↦ g t) ≤ᵐ[volume.restrict (Ioc 0 1)]
        (fun t : ℝ ↦ t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa [g] using mul_le_of_le_one_left h_nonneg h_exp
  have hIoc₁ : IntegrableOn g (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
  have hIoc₂ : IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 := by
      simpa using
        intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re - 1)
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (a := 0) (b := 1) zero_le_one).1 hInt
  have h_drop_exp :
      (∫ t in Ioc 0 1, g t)
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) :=
    MeasureTheory.setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae_drop
  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := by
    have step1 : ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
      simpa [h_int_real, h_split] using h_le_int
    have step2 : (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t)
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) :=
      add_le_add_left h_drop_exp _
    simpa [h_norm] using (le_trans step1 step2)
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    integral_rpow_Ioc_zero_one hw_pos
  have h_tail :
      ∫ t in Ioi 1, g t ≤ Real.sqrt Real.pi := by
    by_cases hhalf : (1 / 2 : ℝ) ≤ w.re
    · have := integral_exp_neg_rpow_Ioi_one_le hhalf hw_ub
      simpa [g] using this
    · have h_ae :
          (fun t : ℝ ↦ g t) ≤ᵐ[volume.restrict (Ioi 1)]
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hpow : t ^ (w.re - 1) ≤ t ^ ((1 / 2 : ℝ) - 1) := by
          have : w.re - 1 ≤ (1 / 2 : ℝ) - 1 := by linarith [hhalf]
          exact Real.rpow_le_rpow_of_exponent_le ht1 this
        have hnonneg : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
        simpa [g] using mul_le_mul_of_nonneg_left hpow hnonneg
      have hIntL : IntegrableOn g (Ioi 1) :=
        (Real.GammaIntegral_convergent hw_pos).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))
      have hIntR : IntegrableOn
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) (Ioi 1) :=
        (Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 2 : ℝ))).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))
      have h_le : ∫ t in Ioi 1, g t
            ≤ ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1) :=
        MeasureTheory.setIntegral_mono_ae_restrict hIntL hIntR h_ae
      have h_upper :
          ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)
            ≤ Real.sqrt Real.pi := by
        have := integral_exp_neg_rpow_Ioi_one_le
                  (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
                  (by norm_num : (1 / 2 : ℝ) ≤ (1 : ℝ))
        simpa using this
      exact h_le.trans h_upper
  have h_main :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    calc
      ‖Complex.Gamma w‖
          ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := h_big
      _ = 1 / w.re + (∫ t in Ioi 1, g t) := by rw [h_Ioc_exact]
      _ ≤ 1 / w.re + Real.sqrt Real.pi := by exact add_le_add_right h_tail _
  have h_one_div : (1 / w.re : ℝ) ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    add_le_add_left h_one_div _
  exact h_main.trans this

end Gamma
end Complex

namespace Complex

namespace Gammaℝ

/-- Closed vertical strip `σ ∈ [σ0, 1]` as a subset of `ℂ`. -/
def strip (σ0 : ℝ) : Set ℂ := { s : ℂ | σ0 ≤ s.re ∧ s.re ≤ 1 }

/-- Uniform bound for `‖(d/ds)Γ_ℝ(s)‖` on the closed strip `σ ∈ [σ0, 1]`. -/
def boundedHDerivOnStrip (σ0 : ℝ) (C : ℝ) : Prop :=
  (1 / 2 : ℝ) < σ0 ∧ σ0 ≤ 1 ∧ 0 ≤ C ∧ ∀ ⦃σ t : ℝ⦄, σ0 ≤ σ → σ ≤ 1 →
    ‖deriv Complex.Gammaℝ (σ + t * I)‖ ≤ C

/-! ### Analyticity of `Γ_ℝ` on the right half-plane -/

/-- `Γ_ℝ` is complex differentiable on the open half-plane `{s | 0 < re s}`. -/
lemma differentiableOn_halfplane :
    DifferentiableOn ℂ Complex.Gammaℝ {s : ℂ | 0 < s.re} := by
  intro s hs
  have h_cpow : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) s := by
    refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  have h_gamma : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    have hnot : ∀ m : ℕ, s / 2 ≠ -m := by
      intro m hsm
      have hre := congrArg Complex.re hsm
      have hdiv : s.re / 2 = -(m : ℝ) := by
        simpa [div_ofNat_re, Complex.ofReal_intCast] using hre
      have hsre_eq : s.re = -(2 * (m : ℝ)) := by
        have h' := congrArg (fun x : ℝ => x * 2) hdiv
        have hleft : (s.re / 2) * 2 = s.re := by
          have : s.re * (2 : ℝ) / 2 = s.re := by simp
          simp
        simpa [hleft, mul_comm, neg_mul] using h'
      have hle : s.re ≤ 0 := by
        have : 0 ≤ (2 : ℝ) * (m : ℝ) := by positivity
        simp [hsre_eq]
      exact (not_le.mpr hs) hle
    have hg : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      (differentiableAt_id.div_const (2 : ℂ))
    exact (differentiableAt_Gamma (s := s / 2) hnot).comp s hg
  simpa [Complex.Gammaℝ_def] using (h_cpow.mul h_gamma).differentiableWithinAt

/-! ### A Cauchy derivative bound -/

/-- Cauchy's derivative bound for `Γ_ℝ` on a circle in the right half-plane. -/
theorem deriv_bound_on_circle
    {s : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hBall : closedBall s r ⊆ {z : ℂ | 0 < z.re})
    (hM : ∀ z ∈ sphere s r, ‖Complex.Gammaℝ z‖ ≤ M) :
    ‖deriv Complex.Gammaℝ s‖ ≤ r⁻¹ * M := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUdiff : DifferentiableOn ℂ Complex.Gammaℝ {z : ℂ | 0 < z.re} :=
    differentiableOn_halfplane
  have hsub : closedBall s r ⊆ {z : ℂ | 0 < z.re} := hBall
  have hs_ball : s ∈ ball s r := by
    simp [mem_ball, dist_self, hr]
  have hCauchy : ((2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • Complex.Gammaℝ z)
       = deriv Complex.Gammaℝ s := by
    simpa using  (two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      (E := ℂ) hUopen (c := s) (w₀ := s) (R := r) (hc := hsub)
       (hf := hUdiff) (hw₀ := by simpa [mem_ball, dist_self] using hr))
  have hker :
      ∀ z ∈ sphere s r, ‖((z - s) ^ 2)⁻¹ • Complex.Gammaℝ z‖ ≤ (r ^ 2)⁻¹ * M := by
    intro z hz
    have hzR : ‖z - s‖ = r := by simpa [dist_eq_norm] using hz
    have : ‖(z - s) ^ 2‖ = ‖z - s‖ ^ 2 := by simp [norm_pow]
    have : ‖(z - s) ^ 2‖ = r ^ 2 := by simp [hzR]
    calc ‖((z - s) ^ 2)⁻¹ • Complex.Gammaℝ z‖
          = ‖(z - s) ^ 2‖⁻¹ * ‖Complex.Gammaℝ z‖ := by simp [norm_inv]
      _ ≤ (r ^ 2)⁻¹ * M := by
        have hHM : ‖Complex.Gammaℝ z‖ ≤ M := hM z hz
        have hnonneg : 0 ≤ ‖(z - s) ^ 2‖⁻¹ := by
          exact inv_nonneg.mpr (norm_nonneg _)
        have hnormpow : ‖(z - s) ^ 2‖ = ‖z - s‖ ^ 2 := by simp [norm_pow]
        have hnorm : ‖(z - s) ^ 2‖ = r ^ 2 := by simp [hzR]
        have hinv : ‖(z - s) ^ 2‖⁻¹ = (r ^ 2)⁻¹ := by simp [hnorm]
        have hmul :
            ‖(z - s) ^ 2‖⁻¹ * ‖Complex.Gammaℝ z‖ ≤ ‖(z - s) ^ 2‖⁻¹ * M :=
          mul_le_mul_of_nonneg_left hHM hnonneg
        simp_rw [hinv]; aesop
  have hbound :
      ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • Complex.Gammaℝ z‖
        ≤ r * ((r ^ 2)⁻¹ * M) :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (c := s) (R := r) (hR := hr.le) (hf := hker)
  have hbound' : ‖deriv Complex.Gammaℝ s‖ ≤ r * ((r ^ 2)⁻¹ * M) :=
    calc
      ‖deriv Complex.Gammaℝ s‖
          = ‖(2 * π * I : ℂ)⁻¹ •
              ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • Complex.Gammaℝ z‖ := by
            simp_rw [hCauchy]
      _ ≤ r * ((r ^ 2)⁻¹ * M) := hbound
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hrr : r * ((r ^ 2)⁻¹ * M) = M * r⁻¹ := by
    calc
      r * ((r ^ 2)⁻¹ * M) = (r * (r ^ 2)⁻¹) * M := by
        simp [mul_comm, mul_left_comm]
      _ = (r / r^2) * M := by simp [div_eq_mul_inv]
      _ = (1 / r) * M := by
        have : r / r^2 = 1 / r := by
          calc
            r / r^2 = r / (r * r) := by simp [pow_two]
            _ = (r / r) / r := by simp_rw [div_mul_eq_div_div]
            _ = 1 / r := by simp [hr0]
        simp [this]
      _ = M * r⁻¹ := by simp [one_div, mul_comm]
  have : ‖deriv Complex.Gammaℝ s‖ ≤ M * r⁻¹ := by simpa [hrr] using hbound'
  simpa [mul_comm] using this

/-- A ball of radius `σ0 / 2` around `σ + it` lies in the right half-plane if `σ0 ≤ σ`. -/
lemma closedBall_subset_halfplane_of_re_ge
    {σ0 σ t : ℝ} (hσ0 : 0 < σ0) (hσ : σ0 ≤ σ) :
    closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by
    simpa [dist_eq_norm] using hz
  have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
    have := (abs_re_le_norm (z - (σ + t * I)))
    have : |(z - (σ + t * I)).re| ≤ ‖z - (σ + t * I)‖ := this
    exact neg_le_of_abs_le this
  have : z.re ≥ σ - σ0 / 2 := by
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 :
        (σ + t * I).re - (σ0 / 2) ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have hneg := neg_le_neg hz'
      linarith
    have hzre_ge : (σ + t * I).re - (σ0 / 2) ≤ z.re := le_trans h2 (h1)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
      sub_zero] at hzre_ge
    linarith
  have : 0 < z.re := by
    have hσpos : 0 < σ - σ0 / 2 := by linarith
    exact lt_of_lt_of_le hσpos (by simpa [ge_iff_le] using this)
  simpa using this

/-- A uniform circle bound for `Γ_ℝ` gives a uniform derivative bound on the strip. -/
theorem boundedHDerivOnStrip_of_uniform_circle_bound
    {σ0 M : ℝ}
    (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) (hM0 : 0 ≤ M)
    (hM : ∀ ⦃σ t : ℝ⦄, σ0 ≤ σ → σ ≤ 1 →
            ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖Complex.Gammaℝ z‖ ≤ M) :
    boundedHDerivOnStrip σ0 ((2 / σ0) * M) := by
  refine ⟨hσ0, hσ1, ?_, ?_⟩
  · have : 0 ≤ 2 / σ0 := by
      have : 0 < σ0 := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ0)
      exact div_nonneg (by norm_num) this.le
    exact mul_nonneg this hM0
  · intro σ t hlo hhi
    have hr : 0 < σ0 / 2 := by
      have : 0 < σ0 := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ0)
      exact half_pos this
    have hBall :
        closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} :=
      closedBall_subset_halfplane_of_re_ge
        ((lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ0)) hlo
    have hMcircle : ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖Complex.Gammaℝ z‖ ≤ M :=
      hM hlo hhi
    have := deriv_bound_on_circle (s := σ + t * I) (r := σ0 / 2) (M := M)
                  hr hBall hMcircle
    simpa [inv_div, one_div, mul_comm, mul_left_comm, mul_assoc] using this

end Gammaℝ

end Complex

open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

-- Division by a positive real preserves order.
private lemma div_le_div_of_le_left {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  exact div_le_div_of_nonneg_right hab hc.le

namespace Complex.Gammaℝ

/-- Explicit circle bound for `Γ_ℝ` over the strip `σ0 ≤ re z ≤ 1`. -/
def circleBound (σ0 : ℝ) : ℝ := Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi)

lemma norm_Gammaℝ_on_sphere_le
    {σ0 σ t : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hlo : σ0 ≤ σ) (hhi : σ ≤ 1) :
    ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖Complex.Gammaℝ z‖ ≤ circleBound σ0 := by
  intro z hz
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by simpa [dist_eq_norm] using (mem_sphere.mp hz).le
  have h_re : (σ0 / 2) ≤ z.re := by
    have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
      have := (abs_re_le_norm (z - (σ + t * I)))
      exact (neg_le_of_abs_le this)
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : (σ + t * I).re - σ0 / 2 ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := neg_le_neg hz'
      linarith
    have : (σ + t * I).re - σ0 / 2 ≤ z.re := le_trans h2 h1
    have : σ - σ0 / 2 ≤ z.re := by simpa [sub_eq_add_neg] using this
    exact (le_trans (by have := hlo; linarith) this)
  have hπ : ‖(π : ℂ) ^ (-(z / 2))‖ ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
    have : Real.rpow Real.pi (-(z.re / 2)) ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
      have : (σ0 / 2) ≤ z.re := h_re
      have h_exp : -(z.re / 2) ≤ -(σ0 / 4) := by
        have : σ0 / 4 ≤ z.re / 2 := by linarith [h_re]
        linarith
      have hpi : (1 : ℝ) < Real.pi := by
        have : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      have hpow :
          Real.rpow Real.pi (-(z.re / 2)) ≤ Real.rpow Real.pi (-(σ0 / 4)) :=
        Real.rpow_le_rpow_of_exponent_le hpi.le h_exp
      exact hpow
    calc ‖(π : ℂ) ^ (-(z / 2))‖
        = Real.pi ^ (-(z / 2)).re := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
      _ = Real.pi ^ (-(z.re / 2)) := by simp [Complex.neg_re]
      _ ≤ Real.pi ^ (-(σ0 / 4)) := this
  let w := z / 2
  have hw_re : (σ0 / 4) ≤ w.re := by
    have : (σ0 / 2) ≤ z.re := h_re
    simpa [w, Complex.div_re] using
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  have hw_ub : w.re ≤ 1 := by
    have h_z_ub : z.re ≤ σ + σ0 / 2 := by
      have : |z.re - σ| ≤ σ0 / 2 := by
        have := (abs_re_le_norm (z - (σ + t * I))).trans hz'
        simpa [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
                Complex.mul_re, Complex.I_re, mul_zero, add_zero] using this
      linarith [(abs_sub_le_iff.mp this).left]
    have : z.re ≤ 3/2 := by
      calc z.re
          ≤ σ + σ0 / 2 := h_z_ub
        _ ≤ 1 + 1 / 2 := by linarith [hhi, hσ0]
        _ = 3 / 2 := by norm_num
    calc w.re
        = z.re / 2 := by simp [w]
      _ ≤ (3/2) / 2 := div_le_div_of_le_left this (by norm_num)
      _ = 3/4 := by norm_num
      _ ≤ 1 := by norm_num
  have hΓ : ‖Complex.Gamma w‖ ≤ 4 / σ0 + Real.sqrt Real.pi := by
    have ha : 0 < σ0 / 4 := by linarith [hσ0]
    calc ‖Complex.Gamma w‖
        ≤ 1 / (σ0 / 4) + Real.sqrt Real.pi :=
          Complex.Gamma.norm_le_one_div_add_sqrt_pi_of_re_ge_of_re_le ha hw_re hw_ub
      _ = 4 / σ0 + Real.sqrt Real.pi := by ring
  have : ‖Complex.Gammaℝ z‖ ≤
      Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) := by
    calc ‖Complex.Gammaℝ z‖
      _ = ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ := by rw [Complex.Gammaℝ_def]
      _ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ := Complex.norm_mul _ _
      _ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma w‖ := by rw [show z / 2 = w from rfl]
      _ ≤ Real.rpow Real.pi (-(σ0 / 4)) * ‖Complex.Gamma w‖ := by
        have : (π : ℂ) ^ (-z / 2) = (π : ℂ) ^ (-(z / 2)) := by ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_right hπ (norm_nonneg _)
      _ ≤ Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) :=
        mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg Real.pi_pos.le _)
  simpa [circleBound] using this

/-- The explicit circle bound gives a strip derivative bound. -/
theorem boundedHDerivOnStrip_via_explicit_bound
    {σ0 : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) :
    boundedHDerivOnStrip σ0 ((2 / σ0) * circleBound σ0) := by
  have h_nonneg : 0 ≤ circleBound σ0 := by
    have hσ0_pos : 0 < σ0 := by linarith
    unfold circleBound
    apply mul_nonneg
    · exact Real.rpow_nonneg Real.pi_pos.le _
    · apply add_nonneg
      · exact div_nonneg (by norm_num) hσ0_pos.le
      · exact Real.sqrt_nonneg _
  apply boundedHDerivOnStrip_of_uniform_circle_bound hσ0 hσ1 h_nonneg
  intro σ t hlo hhi z hz
  exact norm_Gammaℝ_on_sphere_le hσ0 hlo hhi z hz

/-- Existence of a bounded derivative on the strip for `1 / 2 < σ0 ≤ 1`. -/
theorem exists_boundedHDerivOnStrip_of
    {σ0 : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) :
    ∃ C : ℝ, Complex.Gammaℝ.boundedHDerivOnStrip σ0 C := by
  refine ⟨(2 / σ0) * Complex.Gammaℝ.circleBound σ0, ?_⟩
  exact Complex.Gammaℝ.boundedHDerivOnStrip_via_explicit_bound hσ0 hσ1

end Gammaℝ
end Complex
end
