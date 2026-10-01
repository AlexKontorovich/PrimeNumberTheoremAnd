import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

namespace Kadiri

open MeasureTheory Complex
open Asymptotics
open ArithmeticFunction hiding log
open Filter
open scoped Topology
open scoped FourierTransform

lemma kadiri_digamma_half_poles_near_zero {s : ℂ} (hsnorm : ‖s‖ < 1)
    (hs0 : s ≠ 0) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  intro n hn
  have hs_eq : s = -((2 * n : ℕ) : ℂ) := by
    calc
      s = (2 : ℂ) * (s / 2) := by ring
      _ = (2 : ℂ) * (-(n : ℂ)) := by rw [hn]
      _ = -((2 * n : ℕ) : ℂ) := by
        norm_num [Nat.cast_mul]
  have hge : (1 : ℝ) ≤ ‖s‖ := by
    by_cases hn0 : n = 0
    · subst hn0
      have hszero : s = 0 := by simpa using hs_eq
      exact False.elim (hs0 hszero)
    · rw [hs_eq, norm_neg, Complex.norm_natCast]
      have h2n : (1 : ℝ) ≤ (2 * n : ℕ) := by
        exact_mod_cast
          (Nat.succ_le_iff.mpr (Nat.mul_pos (by norm_num) (Nat.pos_iff_ne_zero.mpr hn0)))
      exact h2n
  linarith

lemma kadiri_digamma_half_poles_eventually_nhdsNE_zero :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  have hball : {s : ℂ | ‖s‖ < 1} ∈ 𝓝 (0 : ℂ) := by
    simpa [Metric.ball, dist_eq_norm] using
      Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hball, eventually_mem_nhdsWithin]
    with s hsnorm hsne
  exact kadiri_digamma_half_poles_near_zero hsnorm hsne

lemma kadiri_gamma_factor_punctured_eq_shifted :
    (fun s : ℂ =>
      (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) + s⁻¹)
      =ᶠ[𝓝[≠] (0 : ℂ)]
    (fun s : ℂ =>
      (1 / 2 : ℂ) * (digamma (s / 2 + 1) + digamma ((1 - s) / 2))) := by
  filter_upwards [kadiri_digamma_half_poles_eventually_nhdsNE_zero, eventually_mem_nhdsWithin]
    with s hpoles hsne
  have hrec := Complex.digamma_apply_add_one (s / 2) hpoles
  rw [hrec]
  field_simp [hsne]
  ring

lemma kadiri_gamma_factor_shifted_tendsto_zero :
    Tendsto
      (fun s : ℂ =>
        (1 / 2 : ℂ) * (digamma (s / 2 + 1) + digamma ((1 - s) / 2)))
      (𝓝 (0 : ℂ))
      (𝓝 ((1 / 2 : ℂ) * (digamma 1 + digamma (1 / 2)))) := by
  have h1arg : ContinuousAt (fun s : ℂ => s / 2 + 1) 0 := by fun_prop
  have h1 : ContinuousAt (fun s : ℂ => digamma (s / 2 + 1)) 0 := by
    simpa [Function.comp_def] using
      ContinuousAt.comp (g := digamma) (f := fun s : ℂ => s / 2 + 1)
        (Complex.continuousAt_digamma_of_re_pos
          (by norm_num : (0 : ℝ) < ((fun s : ℂ => s / 2 + 1) 0).re)) h1arg
  have h2arg : ContinuousAt (fun s : ℂ => (1 - s) / 2) 0 := by fun_prop
  have h2 : ContinuousAt (fun s : ℂ => digamma ((1 - s) / 2)) 0 := by
    simpa [Function.comp_def] using
      ContinuousAt.comp (g := digamma) (f := fun s : ℂ => (1 - s) / 2)
        (Complex.continuousAt_digamma_of_re_pos
          (by norm_num : (0 : ℝ) < ((fun s : ℂ => (1 - s) / 2) 0).re)) h2arg
  simpa using ((h1.add h2).const_mul (1 / 2 : ℂ)).tendsto

lemma kadiri_gamma_factor_add_inv_isBigO_one :
    (fun s : ℂ =>
      (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) + s⁻¹)
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  have hO :
      (fun s : ℂ =>
        (1 / 2 : ℂ) * (digamma (s / 2 + 1) + digamma ((1 - s) / 2)))
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) :=
    (kadiri_gamma_factor_shifted_tendsto_zero.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  exact kadiri_gamma_factor_punctured_eq_shifted.trans_isBigO hO

lemma kadiri_digamma_half_poles {s : ℂ} {T : ℝ}
    (hsim : (s / 2).im = T / 2) (hT : 1 ≤ T) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  intro n h
  have hzero : (-(n : ℂ)).im = 0 := by simp
  have : T / 2 = 0 := by
    calc T / 2 = (s / 2).im := hsim.symm
      _ = (-(n : ℂ)).im := by rw [h]
      _ = 0 := hzero
  linarith

lemma kadiri_norm_inv_half_le_two {s : ℂ} {T : ℝ}
    (hsim : (s / 2).im = T / 2) (hT : 1 ≤ T) :
    ‖(s / 2)⁻¹‖ ≤ (2 : ℝ) := by
  have him_nonneg : 0 ≤ T / 2 := by linarith
  have hnorm_ge : T / 2 ≤ ‖s / 2‖ := by
    calc T / 2 = |(s / 2).im| := by rw [hsim, abs_of_nonneg him_nonneg]
      _ ≤ ‖s / 2‖ := Complex.abs_im_le_norm _
  have hnorm_pos : 0 < ‖s / 2‖ := by linarith
  rw [norm_inv]
  rw [inv_le_comm₀ hnorm_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

lemma kadiri_digamma_half_shift {s : ℂ} {T : ℝ}
    (hsim : (s / 2).im = T / 2) (hT : 1 ≤ T) :
    digamma (s / 2) = digamma ((s + 2) / 2) - (s / 2)⁻¹ := by
  have hrec := Complex.digamma_apply_add_one (s / 2) (kadiri_digamma_half_poles hsim hT)
  have hshift : s / 2 + 1 = (s + 2) / 2 := by ring
  rw [hshift] at hrec
  rw [hrec]
  abel

lemma kadiri_gamma_factor_horizontal_norm_le_log
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T σ : ℝ, 1 ≤ T → -a ≤ σ → σ ≤ 1 / 2 →
      ‖(1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
           digamma ((((1 : ℂ) - ((σ : ℂ) + (T : ℂ) * I)) / 2)))‖
        ≤ C * Real.log (T + 2) := by
  obtain ⟨C1, hC1, hC1_bound⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1) (b := 5 / 2) (by norm_num)
  obtain ⟨C2, hC2, hC2_bound⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1 / 2) (b := 1 + a) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C1 + C2 + 2 / Real.log 2, ?_, fun T σ hT hσlo hσhi => ?_⟩
  · positivity
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = T := by simp [s]
  have hsim2 : (s / 2).im = T / 2 := by simp [s]
  have hlog_mono : Real.log 2 ≤ Real.log (T + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hshift : ‖digamma ((s + 2) / 2)‖ ≤ C1 * Real.log (T + 2) := by
    have hrelo : (1 : ℝ) ≤ (s + 2).re := by
      rw [Complex.add_re, hsre]
      norm_num
      linarith
    have hrehi : (s + 2).re ≤ (5 / 2 : ℝ) := by
      rw [Complex.add_re, hsre]
      norm_num
      linarith
    have h := hC1_bound (s + 2) hrelo hrehi
    have him_eq : (s + 2).im = T := by simp [Complex.add_im, hsim]
    simpa [him_eq, abs_of_nonneg (by linarith : 0 ≤ T)] using h
  have hinv : ‖(s / 2)⁻¹‖ ≤ (2 / Real.log 2) * Real.log (T + 2) := by
    calc ‖(s / 2)⁻¹‖ ≤ (2 : ℝ) := kadiri_norm_inv_half_le_two hsim2 hT
      _ = (2 / Real.log 2) * Real.log 2 := by field_simp [hlog2.ne']
      _ ≤ (2 / Real.log 2) * Real.log (T + 2) :=
          mul_le_mul_of_nonneg_left hlog_mono (div_nonneg (by norm_num) hlog2.le)
  have hleft : ‖digamma (s / 2)‖ ≤
      (C1 + 2 / Real.log 2) * Real.log (T + 2) := by
    rw [kadiri_digamma_half_shift hsim2 hT]
    calc ‖digamma ((s + 2) / 2) - (s / 2)⁻¹‖
        ≤ ‖digamma ((s + 2) / 2)‖ + ‖(s / 2)⁻¹‖ := norm_sub_le _ _
      _ ≤ C1 * Real.log (T + 2) + (2 / Real.log 2) * Real.log (T + 2) :=
          add_le_add hshift hinv
      _ = (C1 + 2 / Real.log 2) * Real.log (T + 2) := by ring
  have hright : ‖digamma ((1 - s) / 2)‖ ≤ C2 * Real.log (T + 2) := by
    have hrelo : (1 / 2 : ℝ) ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re, hsre]
      linarith
    have hrehi : (1 - s).re ≤ 1 + a := by
      rw [Complex.sub_re, Complex.one_re, hsre]
      linarith
    have h := hC2_bound (1 - s) hrelo hrehi
    have him_eq : (1 - s).im = -T := by simp [Complex.sub_im, Complex.one_im, hsim]
    simpa [him_eq, abs_of_nonneg (by linarith : 0 ≤ T)] using h
  calc
    ‖(1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))‖
        ≤ ‖digamma (s / 2) + digamma ((1 - s) / 2)‖ := by
          rw [norm_mul]
          have hhalf : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by norm_num [Complex.normSq]
          exact mul_le_of_le_one_left (norm_nonneg _) hhalf
    _ ≤ ‖digamma (s / 2)‖ + ‖digamma ((1 - s) / 2)‖ := norm_add_le _ _
    _ ≤ (C1 + 2 / Real.log 2) * Real.log (T + 2) + C2 * Real.log (T + 2) :=
        add_le_add hleft hright
    _ = (C1 + C2 + 2 / Real.log 2) * Real.log (T + 2) := by ring

end Kadiri
