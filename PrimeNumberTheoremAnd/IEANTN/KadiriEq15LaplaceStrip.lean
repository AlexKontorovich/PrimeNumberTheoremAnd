import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.KadiriSupport

/-!
# Laplace-strip estimates for Kadiri equation (15)

Uniform-in-`σ` estimates for the weighted sources `exp (σ z) · φ z` on the Kadiri
strip `-a ≤ σ ≤ 1/2`, and the difference-quotient bounds for the two-sided Laplace
transform at `0`. The strip-instance integrability and derivative lemmas live in
`PrimeNumberTheoremAnd.IEANTN.KadiriSupport`.
-/

namespace Kadiri

open MeasureTheory Complex
open Asymptotics
open ArithmeticFunction hiding log
open Filter
open scoped Topology
open scoped FourierTransform

lemma kadiri_laplace_exp_zero_sub_div_isBigO_one {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun s : ℂ =>
        ((∫ y : ℝ, φ y * exp ((0 : ℂ) * (y : ℂ)) ∂volume) -
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) / s)
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  let f : ℂ → ℂ := fun s => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  have hderiv := kadiri_laplace_exp_hasDerivAt_zero hφ hb hφ_decay
  have hslopeO : slope f 0 =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) :=
    hderiv.tendsto_slope.isBigO_one ℂ
  refine hslopeO.neg_left.congr' ?_ .rfl
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  dsimp [f]
  simp [slope, div_eq_mul_inv, sub_eq_add_neg]
  ring

lemma kadiri_laplace_exp_integral_sub_div_isBigO_one {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun s : ℂ =>
        ((∫ y : ℝ, φ y ∂volume) -
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) / s)
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  have hO := kadiri_laplace_exp_zero_sub_div_isBigO_one hφ hb hφ_decay
  have hzero :
      (∫ y : ℝ, φ y * exp ((0 : ℂ) * (y : ℂ)) ∂volume) =
        ∫ y : ℝ, φ y ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    simp
  refine hO.congr' ?_ .rfl
  filter_upwards with s
  rw [hzero]

lemma kadiri_laplace_strip_weight_differentiable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (sigma : ℝ) :
    Differentiable ℝ (fun z : ℝ => exp ((sigma : ℂ) * (z : ℂ)) * φ z) := by
  intro y
  exact (kadiri_exp_mul_hasDerivAt sigma y).differentiableAt.mul
    ((hφ.differentiable (by norm_num)) y)

lemma kadiri_laplace_strip_weight_deriv_integrable
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a σ : ℝ} (ha : 0 < a) (hab : a < b) (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    Integrable (deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z)) := by
  let F : ℝ → ℂ := fun y => exp ((σ : ℂ) * (y : ℂ)) * φ y
  let G : ℝ → ℂ := fun y => exp ((σ : ℂ) * (y : ℂ)) * deriv φ y
  have hF_int : Integrable F :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab hσlo hσhi
  have hG_int : Integrable G :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay ha hab hσlo hσhi
  have hsum : Integrable (fun y : ℝ => (σ : ℂ) * F y + G y) :=
    (hF_int.const_mul (σ : ℂ)).add hG_int
  refine hsum.congr ?_
  filter_upwards with y
  dsimp [F, G]
  symm
  rw [deriv_fun_mul (kadiri_exp_mul_hasDerivAt σ y).differentiableAt
    ((hφ.differentiable (by norm_num)) y)]
  rw [HasDerivAt.deriv (kadiri_exp_mul_hasDerivAt σ y)]
  ring

lemma kadiri_laplace_strip_weight_norm_le_endpoints
    {ψ : ℝ → ℂ} {a σ x : ℝ} (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    ‖exp ((σ : ℂ) * (x : ℂ)) * ψ x‖ ≤
      ‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * ψ x‖ +
        ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * ψ x‖ := by
  have hnorm (τ : ℝ) :
      ‖exp ((τ : ℂ) * (x : ℂ)) * ψ x‖ = Real.exp (τ * x) * ‖ψ x‖ := by
    rw [norm_mul, Complex.norm_exp]
    have hτ : ((τ : ℂ) * (x : ℂ)).re = τ * x := by
      norm_num [Complex.mul_re]
    rw [hτ]
  by_cases hx : 0 ≤ x
  · have hcoeff : Real.exp (σ * x) ≤ Real.exp ((1 / 2 : ℝ) * x) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσhi hx)
    rw [hnorm σ, hnorm (-a), hnorm (1 / 2 : ℝ)]
    calc
      Real.exp (σ * x) * ‖ψ x‖
          ≤ Real.exp ((1 / 2 : ℝ) * x) * ‖ψ x‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ Real.exp ((-a) * x) * ‖ψ x‖ +
          Real.exp ((1 / 2 : ℝ) * x) * ‖ψ x‖ :=
            le_add_of_nonneg_left (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hcoeff : Real.exp (σ * x) ≤ Real.exp ((-a) * x) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσlo hxle)
    rw [hnorm σ, hnorm (-a), hnorm (1 / 2 : ℝ)]
    calc
      Real.exp (σ * x) * ‖ψ x‖
          ≤ Real.exp ((-a) * x) * ‖ψ x‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ Real.exp ((-a) * x) * ‖ψ x‖ +
          Real.exp ((1 / 2 : ℝ) * x) * ‖ψ x‖ :=
            le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))

lemma kadiri_laplace_strip_deriv_integral_bounded
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ : ℝ, -a ≤ σ → σ ≤ 1 / 2 →
      ∫ x, ‖deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z) x‖ ∂volume ≤ D := by
  let Lφ : ℝ → ℂ := fun x => exp (((-a : ℝ) : ℂ) * (x : ℂ)) * φ x
  let Rφ : ℝ → ℂ := fun x => exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * φ x
  let Lφ' : ℝ → ℂ := fun x => exp (((-a : ℝ) : ℂ) * (x : ℂ)) * deriv φ x
  let Rφ' : ℝ → ℂ := fun x => exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * deriv φ x
  let K : ℝ := max a (1 / 2)
  let M : ℝ → ℝ := fun x => K * (‖Lφ x‖ + ‖Rφ x‖) + (‖Lφ' x‖ + ‖Rφ' x‖)
  have hK_nonneg : 0 ≤ K := by
    exact ha.le.trans (le_max_left a (1 / 2))
  have hleft_le_half : -a ≤ (1 / 2 : ℝ) := by linarith
  have hLφ_int : Integrable Lφ :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab le_rfl hleft_le_half
  have hRφ_int : Integrable Rφ :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab hleft_le_half le_rfl
  have hLφ'_int : Integrable Lφ' :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay ha hab
      le_rfl hleft_le_half
  have hRφ'_int : Integrable Rφ' :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay ha hab
      hleft_le_half le_rfl
  have hM_int : Integrable M := by
    have hφsum : Integrable (fun x => ‖Lφ x‖ + ‖Rφ x‖) :=
      hLφ_int.norm.add hRφ_int.norm
    have hφ'sum : Integrable (fun x => ‖Lφ' x‖ + ‖Rφ' x‖) :=
      hLφ'_int.norm.add hRφ'_int.norm
    exact (hφsum.const_mul K).add hφ'sum
  have hM_nonneg : ∀ x, 0 ≤ M x := by
    intro x
    dsimp [M]
    exact add_nonneg
      (mul_nonneg hK_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)))
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨∫ x, M x ∂volume, integral_nonneg hM_nonneg, ?_⟩
  intro σ hσlo hσhi
  have hσnorm : ‖(σ : ℂ)‖ ≤ K := by
    rw [norm_real, Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hKa : a ≤ K := le_max_left a (1 / 2)
      linarith
    · have hKh : (1 / 2 : ℝ) ≤ K := le_max_right a (1 / 2)
      linarith
  have hderiv_int : Integrable (deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z)) :=
    kadiri_laplace_strip_weight_deriv_integrable
      (φ := φ) hφ hφ_decay hφ'_decay ha hab hσlo hσhi
  have hpoint : ∀ x,
      ‖deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z) x‖ ≤ M x := by
    intro x
    have hderiv :
        deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z) x =
          (σ : ℂ) * (exp ((σ : ℂ) * (x : ℂ)) * φ x) +
            exp ((σ : ℂ) * (x : ℂ)) * deriv φ x := by
      rw [deriv_fun_mul (kadiri_exp_mul_hasDerivAt σ x).differentiableAt
        ((hφ.differentiable (by norm_num)) x)]
      rw [HasDerivAt.deriv (kadiri_exp_mul_hasDerivAt σ x)]
      ring
    have hφ_end := kadiri_laplace_strip_weight_norm_le_endpoints
      (ψ := φ) (a := a) (σ := σ) (x := x) hσlo hσhi
    have hφ'_end := kadiri_laplace_strip_weight_norm_le_endpoints
      (ψ := deriv φ) (a := a) (σ := σ) (x := x) hσlo hσhi
    rw [hderiv]
    dsimp [M, Lφ, Rφ, Lφ', Rφ']
    calc
      ‖(σ : ℂ) * (exp ((σ : ℂ) * (x : ℂ)) * φ x) +
          exp ((σ : ℂ) * (x : ℂ)) * deriv φ x‖
          ≤ ‖(σ : ℂ) * (exp ((σ : ℂ) * (x : ℂ)) * φ x)‖ +
              ‖exp ((σ : ℂ) * (x : ℂ)) * deriv φ x‖ := norm_add_le _ _
      _ = ‖(σ : ℂ)‖ * ‖exp ((σ : ℂ) * (x : ℂ)) * φ x‖ +
              ‖exp ((σ : ℂ) * (x : ℂ)) * deriv φ x‖ := by rw [norm_mul]
      _ ≤ K *
              (‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * φ x‖ +
                ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * φ x‖) +
            (‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * deriv φ x‖ +
              ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * deriv φ x‖) := by
          have hfirst :
              ‖(σ : ℂ)‖ * ‖exp ((σ : ℂ) * (x : ℂ)) * φ x‖ ≤
                K *
                  (‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * φ x‖ +
                    ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * φ x‖) := by
            exact mul_le_mul hσnorm hφ_end (norm_nonneg _) hK_nonneg
          exact add_le_add hfirst hφ'_end
  exact integral_mono hderiv_int.norm hM_int hpoint

end Kadiri
