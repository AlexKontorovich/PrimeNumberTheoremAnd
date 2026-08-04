import PrimeNumberTheoremAnd.LaplaceInversion
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Foundations
import PrimeNumberTheoremAnd.Fourier
import PrimeNumberTheoremAnd.SincKernelErrorBounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Shared support lemmas for the Kadiri equation files

Lemmas used by more than one of the Kadiri equation developments
(`KadiriEq11Reduction`, `KadiriEq14`, `KadiriEq15LaplaceStrip`), factored out so each
file states its instances as short corollaries.

Contents:
* exponential-kernel micro-lemmas (`kadiri_exp_mul_hasDerivAt`,
  `kadiri_exp_neg_mul_hasDerivAt`, `laplaceKernel_contDiff_paren`);
* asymptotics, boundedness, integrability and derivative bounds for the weighted
  source `y ↦ exp (-(σ y)) · ψ y` under the Kadiri decay hypothesis, on the widest
  strip `-(1+b) < σ < b` where they hold;
* the Kadiri-strip instances of the full-strip Laplace lemmas from
  `KadiriEq12Foundations`;
* von Mangoldt Dirichlet-series glue (`tsum_vonMangoldt_eq`,
  `summable_vonMangoldt_cpow`);
* a convex-set generalization of the sin-div window error bounds from
  `SincKernelErrorBounds`.
-/

namespace Kadiri

open MeasureTheory Complex
open Asymptotics
open ArithmeticFunction hiding log
open Filter
open scoped Topology

noncomputable section

/-! ## Exponential-kernel micro-lemmas -/

/-- Derivative of the exponential weight `y ↦ exp (σ y)` along the real line. -/
lemma kadiri_exp_mul_hasDerivAt (sigma x : ℝ) :
    HasDerivAt (fun y : ℝ => exp ((sigma : ℂ) * (y : ℂ)))
      ((sigma : ℂ) * exp ((sigma : ℂ) * (x : ℂ))) x := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).ofReal_comp.const_mul (sigma : ℂ)).cexp

/-- Derivative of the exponential weight `y ↦ exp (-(σ y))` along the real line. -/
lemma kadiri_exp_neg_mul_hasDerivAt (sigma x : ℝ) :
    HasDerivAt (fun y : ℝ => exp (-((sigma : ℂ) * (y : ℂ))))
      (-(sigma : ℂ) * exp (-((sigma : ℂ) * (x : ℂ)))) x := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).ofReal_comp.const_mul (-(sigma : ℂ))).cexp

/-- `C¹` smoothness of the bilateral Laplace kernel `y ↦ exp (-(s y))`. -/
lemma laplaceKernel_contDiff_paren (s : ℂ) :
    ContDiff ℝ 1 (fun y : ℝ => exp (-(s * (y : ℂ)))) := by
  have hofReal : ContDiff ℝ 1 (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hlinear : ContDiff ℝ 1 (fun y : ℝ => -(s * (y : ℂ))) := by
    simpa using
      ((contDiff_const.mul hofReal).neg :
        ContDiff ℝ 1 (fun y : ℝ => -(s * (y : ℂ))))
  exact hlinear.cexp

/-! ## The weighted source `exp (-(σ y)) · ψ y` under the Kadiri decay hypothesis -/

/-- Norm shape of the weighted source: peeling off the `exp (x/2)` factor. -/
lemma kadiri_laplace_neg_line_weight_norm_eq {ψ : ℝ → ℂ} (sigma x : ℝ) :
    ‖exp (-((sigma : ℂ) * (x : ℂ))) * ψ x‖ =
      Real.exp (-(sigma + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(↑sigma * ↑x) : ℂ).re = -sigma * x := by
    norm_num [Complex.mul_re]
  have h2 : ((x : ℂ) / 2).re = x / 2 := by
    norm_num
  rw [h1, h2]
  calc
    Real.exp (-sigma * x) * ‖ψ x‖
        = (Real.exp (-(sigma + 1 / 2) * x) * Real.exp (x / 2)) * ‖ψ x‖ := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ = Real.exp (-(sigma + 1 / 2) * x) * (‖ψ x‖ * Real.exp (x / 2)) := by
          ring_nf

/-- On `atBot`, the weighted source is `O(exp ((b - σ) x))`; no constraint on `σ`. -/
lemma kadiri_laplace_neg_line_weight_isBigO_atBot {ψ : ℝ → ℂ} {b : ℝ} (sigma : ℝ)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.atBot] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun x : ℝ => exp (-((sigma : ℂ) * (x : ℂ))) * ψ x)
      =O[Filter.atBot] fun x : ℝ => Real.exp ((b - sigma) * x) := by
  rw [Asymptotics.isBigO_iff] at hψ_decay ⊢
  obtain ⟨C, hC⟩ := hψ_decay
  refine ⟨C, ?_⟩
  filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
  rw [kadiri_laplace_neg_line_weight_norm_eq]
  calc
    Real.exp (-(sigma + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
        ≤ Real.exp (-(sigma + 1 / 2) * x) *
            (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
          exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
    _ = C * ‖Real.exp ((b - sigma) * x)‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
          calc
            Real.exp (-(sigma + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * -x))
                = C * (Real.exp (-(sigma + 1 / 2) * x) *
                    Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
            _ = C * Real.exp (-(sigma + 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                  rw [Real.exp_add]
            _ = C * Real.exp ((b - sigma) * x) := by ring_nf

/-- On `atTop`, the weighted source is `O(exp (-(1 + b + σ) x))`; no constraint on `σ`. -/
lemma kadiri_laplace_neg_line_weight_isBigO_atTop {ψ : ℝ → ℂ} {b : ℝ} (sigma : ℝ)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.atTop] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun x : ℝ => exp (-((sigma : ℂ) * (x : ℂ))) * ψ x)
      =O[Filter.atTop] fun x : ℝ => Real.exp (-(1 + b + sigma) * x) := by
  rw [Asymptotics.isBigO_iff] at hψ_decay ⊢
  obtain ⟨C, hC⟩ := hψ_decay
  refine ⟨C, ?_⟩
  filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
  rw [kadiri_laplace_neg_line_weight_norm_eq]
  calc
    Real.exp (-(sigma + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
        ≤ Real.exp (-(sigma + 1 / 2) * x) *
            (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
          exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
    _ = C * ‖Real.exp (-(1 + b + sigma) * x)‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
          calc
            Real.exp (-(sigma + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * x))
                = C * (Real.exp (-(sigma + 1 / 2) * x) *
                    Real.exp (-(1 / 2 + b) * x)) := by ring_nf
            _ = C * Real.exp (-(sigma + 1 / 2) * x + (-(1 / 2 + b) * x)) := by
                  rw [Real.exp_add]
            _ = C * Real.exp (-(1 + b + sigma) * x) := by ring_nf

/-- Global boundedness of the weighted source for `-(1+b) < σ < b`. -/
lemma kadiri_laplace_neg_line_weight_bounded_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b sigma : ℝ}
    (hlo : -(1 + b) < sigma) (hhi : sigma < b)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖exp (-((sigma : ℂ) * (x : ℂ))) * ψ x‖ ≤ B := by
  have htop := kadiri_laplace_neg_line_weight_isBigO_atTop (ψ := ψ) (b := b) sigma
    (hψ_decay.mono atTop_le_cocompact)
  have hbot := kadiri_laplace_neg_line_weight_isBigO_atBot (ψ := ψ) (b := b) sigma
    (hψ_decay.mono atBot_le_cocompact)
  exact bounded_of_continuous_of_isBigO_exp_atBot_atTop
    ((laplaceKernel_contDiff_paren ((sigma : ℝ) : ℂ)).continuous.mul hψ)
    (show -(1 + b + sigma) < 0 by linarith) (show 0 < b - sigma by linarith)
    htop hbot

/-- Integrability of the weighted source for `-(1+b) < σ < b`: the `σ ↦ -σ` instance of
`kadiri_laplace_full_strip_weight_integrable_of_continuous`. -/
lemma kadiri_laplace_neg_line_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b sigma : ℝ}
    (hlo : -(1 + b) < sigma) (hhi : sigma < b)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    Integrable (fun y : ℝ => exp (-((sigma : ℂ) * (y : ℂ))) * ψ y) := by
  have hbase := kadiri_laplace_full_strip_weight_integrable_of_continuous
    (ψ := ψ) hψ (σ := -sigma) (by linarith) (by linarith) hψ_decay
  refine hbase.congr ?_
  filter_upwards with y
  have harg : ((-sigma : ℝ) : ℂ) * (y : ℂ) = -((sigma : ℂ) * (y : ℂ)) := by
    push_cast
    ring
  rw [harg]

/-- Product-rule derivative of the weighted source. -/
lemma kadiri_laplace_neg_line_weight_deriv {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (sigma y : ℝ) :
    deriv (fun x : ℝ => exp (-((sigma : ℂ) * (x : ℂ))) * φ x) y =
      -(sigma : ℂ) * (exp (-((sigma : ℂ) * (y : ℂ))) * φ y) +
        exp (-((sigma : ℂ) * (y : ℂ))) * deriv φ y := by
  rw [deriv_fun_mul (kadiri_exp_neg_mul_hasDerivAt sigma y).differentiableAt
    ((hφ.differentiable (by norm_num)) y)]
  rw [HasDerivAt.deriv (kadiri_exp_neg_mul_hasDerivAt sigma y)]
  ring

/-- Global bound for the derivative of the weighted source for `-(1+b) < σ < b`. -/
lemma kadiri_laplace_neg_line_weight_deriv_bounded {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b sigma : ℝ} (hlo : -(1 + b) < sigma) (hhi : sigma < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ,
      ‖deriv (fun x : ℝ => exp (-((sigma : ℂ) * (x : ℂ))) * φ x) y‖ ≤ D := by
  obtain ⟨Bφ, hBφ_nonneg, hBφ⟩ :=
    kadiri_laplace_neg_line_weight_bounded_of_continuous hφ.continuous hlo hhi hφ_decay
  obtain ⟨Bφ', hBφ'_nonneg, hBφ'⟩ :=
    kadiri_laplace_neg_line_weight_bounded_of_continuous
      (hφ.continuous_deriv (by norm_num)) hlo hhi hφ'_decay
  refine ⟨‖(sigma : ℂ)‖ * Bφ + Bφ',
    add_nonneg (mul_nonneg (norm_nonneg _) hBφ_nonneg) hBφ'_nonneg, ?_⟩
  intro y
  rw [kadiri_laplace_neg_line_weight_deriv hφ sigma y]
  calc
    ‖-(sigma : ℂ) * (exp (-((sigma : ℂ) * (y : ℂ))) * φ y) +
        exp (-((sigma : ℂ) * (y : ℂ))) * deriv φ y‖
        ≤ ‖-(sigma : ℂ) * (exp (-((sigma : ℂ) * (y : ℂ))) * φ y)‖ +
            ‖exp (-((sigma : ℂ) * (y : ℂ))) * deriv φ y‖ := norm_add_le _ _
    _ ≤ ‖(sigma : ℂ)‖ * Bφ + Bφ' := by
          have hfirst :
              ‖-(sigma : ℂ) * (exp (-((sigma : ℂ) * (y : ℂ))) * φ y)‖ ≤
                ‖(sigma : ℂ)‖ * Bφ := by
            rw [norm_mul, norm_neg]
            exact mul_le_mul_of_nonneg_left (hBφ y) (norm_nonneg _)
          exact add_le_add hfirst (hBφ' y)

/-! ## Kadiri-strip instances of the full-strip Laplace lemmas -/

/-- Kadiri-strip instance of the full-strip weight integrability. -/
lemma kadiri_laplace_strip_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a σ : ℝ} (ha : 0 < a) (hab : a < b) (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    Integrable (fun y : ℝ => exp ((σ : ℂ) * (y : ℂ)) * ψ y) :=
  kadiri_laplace_full_strip_weight_integrable_of_continuous hψ
    (by linarith) (by linarith) hψ_decay

/-- Kadiri-strip instance of the full-strip derivative formula for the two-sided
Laplace transform. -/
lemma kadiri_laplace_exp_hasDerivAt_of_kadiri_strip {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b a : ℝ} (ha : 0 < a) (hab : a < b) {s0 : ℂ}
    (hs0lo : -a ≤ s0.re) (hs0hi : s0.re ≤ 1 / 2)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    HasDerivAt
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (∫ y : ℝ, φ y * ((y : ℂ) * exp (s0 * (y : ℂ))) ∂volume) s0 :=
  kadiri_laplace_exp_hasDerivAt_of_full_strip hφ (by linarith) (by linarith) hφ_decay

/-- Complex differentiability of the two-sided Laplace transform on the closed Kadiri
strip `-a ≤ Re s ≤ 1/2`. -/
lemma kadiri_laplace_exp_differentiableOn_kadiri_strip {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b a : ℝ} (ha : 0 < a) (hab : a < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (Set.Icc (-a) (1 / 2 : ℝ) ×ℂ Set.univ) := by
  intro s hs
  have hsre := Complex.mem_reProdIm.mp hs |>.1
  exact DifferentiableAt.differentiableWithinAt
    ((kadiri_laplace_exp_hasDerivAt_of_kadiri_strip
      hφ ha hab hsre.1 hsre.2 hφ_decay).differentiableAt)

/-- Derivative of the two-sided Laplace transform at `0`: the `s0 = 0` instance of the
full-strip derivative formula. -/
lemma kadiri_laplace_exp_hasDerivAt_zero {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    HasDerivAt
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (∫ y : ℝ, φ y * (y : ℂ) ∂volume) 0 := by
  have h := kadiri_laplace_exp_hasDerivAt_of_full_strip (φ := φ) hφ (b := b) (s0 := 0)
    (by simp only [Complex.zero_re]; linarith)
    (by simp only [Complex.zero_re]; linarith) hφ_decay
  have heq : (∫ y : ℝ, φ y * ((y : ℂ) * exp ((0 : ℂ) * (y : ℂ))) ∂volume) =
      ∫ y : ℝ, φ y * (y : ℂ) ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    simp
  rw [← heq]
  exact h

/-! ## Von Mangoldt Dirichlet-series glue -/

/-- The raw von Mangoldt Dirichlet sum is `-ζ'/ζ` on `1 < Re s` (the tsum form of
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). -/
lemma tsum_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) = -deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]

/-- Summability of the von Mangoldt Dirichlet series on `1 < Re s`. -/
lemma summable_vonMangoldt_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ s) := by
  refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]

/-- Norm summability of the von Mangoldt Dirichlet series on `1 < Re s`. -/
lemma summable_norm_vonMangoldt_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖(Λ n : ℂ) / (n : ℂ) ^ s‖) :=
  (summable_vonMangoldt_cpow hs).norm

/-! ## Convex-set sin-div window error bounds -/

/-- Convex-set version of `sin_div_error_pointwise_bound`: the mean-value estimate only
needs differentiability and the derivative bound on a convex set containing both
points. -/
theorem sin_div_error_pointwise_bound_of_convex
    {g : ℝ → ℂ} {s : Set ℝ} (hs : Convex ℝ s) {D x T u : ℝ}
    (hD : 0 ≤ D) (hx : x ∈ s) (hxu : x - u ∈ s)
    (hgdiff : ∀ y ∈ s, DifferentiableAt ℝ g y)
    (hderiv : ∀ y ∈ s, ‖deriv g y‖ ≤ D) :
    ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
        (g (x - u) - g x)‖ ≤ D / Real.pi := by
  by_cases hu : u = 0
  · simp [hu, div_nonneg hD Real.pi_pos.le]
  · rw [if_neg hu, norm_smul]
    have hscalar :
        ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 1 / (Real.pi * |u|) := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      have hsin : |Real.sin (T * u)| ≤ 1 := Real.abs_sin_le_one _
      exact div_le_div_of_nonneg_right hsin
        (mul_nonneg Real.pi_pos.le (abs_nonneg u))
    have hdiff : ‖g (x - u) - g x‖ ≤ D * |u| := by
      have hmv := hs.norm_image_sub_le_of_norm_deriv_le hgdiff hderiv hx hxu
      have hnorm : ‖(x - u) - x‖ = |u| := by
        rw [Real.norm_eq_abs]
        have hsub : (x - u) - x = -u := by ring
        rw [hsub, abs_neg]
      simpa [hnorm] using hmv
    have hupper_nonneg : 0 ≤ 1 / (Real.pi * |u|) := by positivity
    calc
      ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ * ‖g (x - u) - g x‖
          ≤ (1 / (Real.pi * |u|)) * (D * |u|) := by
            exact mul_le_mul hscalar hdiff (norm_nonneg _) hupper_nonneg
      _ = D / Real.pi := by
            field_simp [Real.pi_ne_zero, abs_pos.mpr hu]

/-- Interval form of `sin_div_error_pointwise_bound_of_convex` over a symmetric
window `[-R, R]`. -/
theorem sin_div_error_interval_bound_of_convex
    {g : ℝ → ℂ} {s : Set ℝ} (hs : Convex ℝ s) {D x T R : ℝ}
    (hD : 0 ≤ D) (hx : x ∈ s) (hmem : ∀ u ∈ Set.uIoc (-R) R, x - u ∈ s)
    (hgdiff : ∀ y ∈ s, DifferentiableAt ℝ g y)
    (hderiv : ∀ y ∈ s, ‖deriv g y‖ ≤ D) :
    ‖∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (g (x - u) - g x)‖ ≤ (D / Real.pi) * |R - (-R)| :=
  intervalIntegral.norm_integral_le_of_norm_le_const fun u hu =>
    sin_div_error_pointwise_bound_of_convex hs hD hx (hmem u hu) hgdiff hderiv

end

end Kadiri
