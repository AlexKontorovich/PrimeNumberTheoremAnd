import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.LaplaceInversion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log
open Filter
open scoped Topology
open scoped FourierTransform

@[blueprint
  "kadiri-thm-3-1-q1-I-1"
  (title := "Kadiri's $I_1(T)$: the constant $\\log(1/\\pi)$ piece")
  (statement := /-- Kadiri's $I_1(T)$ from \cite[p.~12]{Kadiri2005}: the constant-prefactor
  piece of the functional-equation rewrite of the $\sigma = -a$ integral,
  $$ I_1(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \log\!\Big(\frac{1}{\pi}\Big)\, \Phi(-s)\, ds. $$
  Its $T \to \infty$ limit is given by \ref{kadiri-thm-3-1-q1-eq-13}. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_1 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      ((-Real.log Real.pi : ℝ) : ℂ) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))


private lemma kadiri_laplace_positive_line_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * ψ y) := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) * ψ y
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      ‖F x‖ = Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : (-(↑a * ↑x) : ℂ).re = -a * x := by
      norm_num [Complex.mul_re]
    have h2 : ((x : ℂ) / 2).re = x / 2 := by
      norm_num
    rw [h1, h2]
    calc
      Real.exp (-a * x) * ‖ψ x‖
          = (Real.exp (-(a + 1 / 2) * x) * Real.exp (x / 2)) * ‖ψ x‖ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ = Real.exp (-(a + 1 / 2) * x) * (‖ψ x‖ * Real.exp (x / 2)) := by ring_nf
  have htop_decay := hψ_decay.mono (show Filter.atTop ≤ Filter.cocompact ℝ from
    atTop_le_cocompact)
  have hbot_decay := hψ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  have htop : F =O[Filter.atTop] fun x : ℝ => Real.exp (-(a + b + 1) * x) := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    rw [hshape]
    calc
      Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp (-(a + 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp (-(a + b + 1) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
            calc
              Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (Real.exp (-(a + 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * x)) := by ring_nf
              _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp (-(a + b + 1) * x) := by ring_nf
  have hbot : F =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    rw [hshape]
    calc
      Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp (-(a + 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((b - a) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
            calc
              Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * -x))
                  = C * (Real.exp (-(a + 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
              _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((b - a) * x) := by ring_nf
  have htop_int : IntegrableAtFilter (fun x : ℝ => Real.exp (-(a + b + 1) * x))
      Filter.atTop volume := by
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    exact exp_neg_integrableOn_Ioi 0 (show 0 < a + b + 1 by linarith)
  have hbot_int : IntegrableAtFilter (fun x : ℝ => Real.exp ((b - a) * x))
      Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
      simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hab) using 1
    ext x
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

private lemma kadiri_laplace_positive_line_weight_integrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
  kadiri_laplace_positive_line_weight_integrable_of_continuous hφ.continuous hφ_decay ha hab

private lemma kadiri_laplace_shifted_vertical_segment_continuousOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (_ha1 : a < 1) :
    ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T) := by
  have h_weighted :
      Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
    kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
  have hcont :=
    continuous_laplaceIntegral_verticalLine_of_integrable
      (f := φ) (sigma := a) hφ.continuous h_weighted
  refine hcont.continuousOn.congr ?_
  intro t _ht
  dsimp [laplaceIntegral]
  apply integral_congr_ae
  filter_upwards with y
  apply congrArg (fun z : ℂ => φ y * exp (-z * (y : ℂ)))
  simp [sub_eq_add_neg, add_comm]


private lemma kadiri_laplace_line_weight_differentiable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (sigma : ℝ) :
    Differentiable ℝ (fun z : ℝ => exp (-((sigma : ℂ) * (z : ℂ))) * φ z) := by
  intro y
  have hofReal : DifferentiableAt ℝ (fun z : ℝ => (z : ℂ)) y :=
    Complex.ofRealCLM.differentiable.differentiableAt
  have hlin : DifferentiableAt ℝ (fun z : ℝ => -((sigma : ℂ) * (z : ℂ))) y := by
    simpa only [neg_mul] using hofReal.const_mul (-(sigma : ℂ))
  exact hlin.cexp.mul ((hφ.differentiable (by norm_num)).differentiableAt)

private lemma kadiri_laplace_line_local_quotient_integrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (sigma x : ℝ) {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (exp (-((sigma : ℂ) * ((x - u : ℝ) : ℂ))) * φ (x - u) -
              exp (-((sigma : ℂ) * (x : ℂ))) * φ x))
      volume (-R) R := by
  let g : ℝ → ℂ := fun y => exp (-((sigma : ℂ) * (y : ℂ))) * φ y
  have hg_cont : ContinuousOn g (Set.Icc (x - R) (x + R)) := by
    dsimp [g]
    exact (Complex.continuous_exp.comp (by continuity)).continuousOn.mul
      hφ.continuous.continuousOn
  have hg_diff : DifferentiableAt ℝ g x :=
    (kadiri_laplace_line_weight_differentiable hφ sigma) x
  simpa [g] using
    intervalIntegrable_local_quotient_of_differentiableAt (E := ℂ)
      (f := g) (x := x) hR hg_cont hg_diff

private theorem kadiri_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (sigma : ℝ) (f : ℝ → E) (x T : ℝ) :
    laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  unfold laplaceInvLineTrunc fourierInvTrunc
  simp_rw [laplaceTransformBilateral_eq_fourier]
  simp only [one_div, mul_inv_rev, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_mul, add_im, mul_im, zero_add]
  rw [show (Real.pi⁻¹ * 2⁻¹ : ℝ) = (1 / (2 * Real.pi) : ℝ) by ring]
  change (1 / (2 * Real.pi) : ℝ) •
      ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
        𝓕 g (t / (2 * Real.pi)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            𝓕 g (t / (2 * Real.pi)))
  have hsplit :
      (∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
          𝓕 g (t / (2 * Real.pi))) =
        Complex.exp ((sigma : ℂ) * (x : ℂ)) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            𝓕 g (t / (2 * Real.pi)) := by
    rw [← intervalIntegral.integral_smul]
    congr with t
    rw [← smul_assoc]
    congr 1
    change Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) * Complex.exp (((t * x : ℝ) : ℂ) * I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hsplit]
  rw [SMulCommClass.smul_comm (M := ℝ) (N := ℂ) (α := E)]

private theorem kadiri_laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (sigma : ℝ) (f : ℝ → E) {x : ℝ}
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (x : ℂ))) • f x))) :
    Filter.Tendsto
      (fun T : ℝ => laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T)
      Filter.atTop (nhds (f x)) := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  have hlim' : Filter.Tendsto (fun T : ℝ => fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (g x)) := by
    simpa [g] using hlim
  have hscaled : Filter.Tendsto
      (fun T : ℝ =>
        Complex.exp ((sigma : ℂ) * (x : ℂ)) • fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x)) :=
    hlim'.const_smul (Complex.exp ((sigma : ℂ) * (x : ℂ)))
  have htarget : Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x = f x := by
    simp [g, ← smul_assoc, ← Complex.exp_add]
  rw [htarget] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with T
  exact (kadiri_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    sigma f x T).symm

private theorem kadiri_exp_mul_log_of_pos_eq_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Complex.exp (s * (Real.log x : ℂ)) = (x : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

private theorem kadiri_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    laplaceIntegralCpowTrunc f sigma x T =
      laplaceInvLineTrunc sigma (laplaceTransformBilateral f) (Real.log x) T := by
  unfold laplaceIntegralCpowTrunc laplaceInvLineTrunc
  simp_rw [laplaceIntegral_eq_laplaceTransformBilateral, smul_eq_mul]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  · push_cast
    field_simp [Real.pi_ne_zero]
    rfl
  · apply intervalIntegral.integral_congr
    intro t _ht
    change laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I) *
        (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * I) =
      Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (Real.log x : ℂ)) *
        laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I)
    rw [← kadiri_exp_mul_log_of_pos_eq_cpow hx ((sigma : ℂ) + (t : ℂ) * I)]
    ring

private theorem kadiri_laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
    (sigma : ℝ) (f : ℝ → ℂ) {x R : ℝ} (hx : 0 < x) (hR : 0 < R)
    (hg : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (Complex.exp (-((sigma : ℂ) * ((Real.log x - u : ℝ) : ℂ))) *
                f (Real.log x - u) -
              Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))
      volume (-R) R) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  have hfourier : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) • f (Real.log x))) := by
    exact fourierInvTrunc_tendsto_of_sinc_kernel (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
      (by simpa [smul_eq_mul] using hg)
      (sinc_kernel_tendsto_of_integrable_local_quotient (E := ℂ)
        (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
        (x := Real.log x) (R := R) (by simpa [smul_eq_mul] using hg) hR hq)
  have hline := kadiri_laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (E := ℂ) sigma f (x := Real.log x) hfourier
  refine hline.congr' ?_
  filter_upwards with T
  exact (kadiri_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma f hx T).symm

private lemma kadiri_laplace_positive_line_pv {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a x : ℝ} (ha : 0 < a) (hab : a < b) (hx : 0 < x) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc φ a x T)
      Filter.atTop (nhds (φ (Real.log x))) := by
  have h_weighted :
      Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
    kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
  have hq :
      IntervalIntegrable
        (fun u : ℝ =>
          if u = 0 then 0 else
            (1 / (Real.pi * u) : ℂ) •
              (exp (-((a : ℂ) * ((Real.log x - u : ℝ) : ℂ))) *
                  φ (Real.log x - u) -
                exp (-((a : ℂ) * (Real.log x : ℂ))) *
                  φ (Real.log x)))
        volume (-1) 1 := by
    simpa using kadiri_laplace_line_local_quotient_integrable
      (φ := φ) hφ a (Real.log x) (by norm_num : (0 : ℝ) < 1)
  exact kadiri_laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
    (sigma := a) (f := φ) (x := x) (R := 1) hx
    (by norm_num : (0 : ℝ) < 1) h_weighted hq

private lemma kadiri_laplace_positive_line_pv_one {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (_ha1 : a < 1) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc φ a 1 T)
      Filter.atTop (nhds (φ 0)) := by
  simpa using kadiri_laplace_positive_line_pv
    (φ := φ) hφ _hb hφ_decay ha hab (by norm_num : (0 : ℝ) < 1)

private lemma kadiri_thm_3_1_q1_I_1_eventually_eq_const_mul_trunc
    (φ : ℝ → ℂ) (a : ℝ) :
    (fun T : ℝ => kadiri_thm_3_1_q1_I_1 φ a T)
      =ᶠ[Filter.atTop]
    (fun T : ℝ => (((-Real.log Real.pi : ℝ) : ℂ) *
      laplaceIntegralCpowTrunc φ a 1 T)) := by
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  have hle : -T ≤ T := by linarith
  have hset_to_interval :
      ∫ t in Set.Ioo (-T) T, Φ (((a : ℝ) : ℂ) - (t : ℂ) * I) =
        ∫ t in (-T)..T, Φ (((a : ℝ) : ℂ) - (t : ℂ) * I) := by
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hflip :
      ∫ t in (-T)..T, Φ (((a : ℝ) : ℂ) - (t : ℂ) * I) =
        ∫ t in (-T)..T, Φ (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
    simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_comp_neg
        (fun t : ℝ => Φ (((a : ℝ) : ℂ) + (t : ℂ) * I))
        (a := -T) (b := T))
  rw [kadiri_thm_3_1_q1_I_1, laplaceIntegralCpowTrunc]
  dsimp only
  have h_integrand :
      (fun t : ℝ =>
        (((-Real.log Real.pi : ℝ) : ℂ) *
          ∫ y, φ y * exp (- -(((-a : ℝ) : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume))
        =
      (fun t : ℝ =>
        (((-Real.log Real.pi : ℝ) : ℂ) *
          Φ (((a : ℝ) : ℂ) - (t : ℂ) * I))) := by
    funext t
    congr 1
    simp [Φ]
    congr 1
    ring_nf
  rw [show
      (∫ t in Set.Ioo (-T) T,
        (((-Real.log Real.pi : ℝ) : ℂ) *
          ∫ y, φ y * exp (- -(((-a : ℝ) : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume))
        =
      ∫ t in Set.Ioo (-T) T,
        (((-Real.log Real.pi : ℝ) : ℂ) *
          Φ (((a : ℝ) : ℂ) - (t : ℂ) * I)) by
        rw [h_integrand]]
  rw [MeasureTheory.integral_const_mul]
  have h_laplace :
      ∫ t in (-T)..T, Φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
        ∫ t in (-T)..T,
          laplaceIntegral φ (((a : ℝ) : ℂ) + I * (t : ℂ)) *
            (((1 : ℝ) : ℂ) ^ (((a : ℝ) : ℂ) + I * (t : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    simp only [Complex.ofReal_one, one_cpow, mul_one]
    dsimp [laplaceIntegral, Φ]
    apply integral_congr_ae
    filter_upwards with y
    apply congrArg (fun z : ℂ => φ y * exp (-z * (y : ℂ)))
    ring_nf
  rw [hset_to_interval, hflip, h_laplace]
  ring_nf

theorem kadiri_thm_3_1_q1_eq_13_core
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_1 φ a T)
      Filter.atTop (nhds (φ 0 * ((-Real.log Real.pi : ℝ) : ℂ))) := by
  let c : ℂ := ((-Real.log Real.pi : ℝ) : ℂ)
  have hraw := kadiri_laplace_positive_line_pv_one
    (φ := φ) _hφ _hb _hφ_decay _ha _hab _ha1
  have hmul : Filter.Tendsto
      (fun T : ℝ => c * laplaceIntegralCpowTrunc φ a 1 T)
      Filter.atTop (nhds (c * φ 0)) := hraw.const_mul c
  have heq := kadiri_thm_3_1_q1_I_1_eventually_eq_const_mul_trunc φ a
  refine hmul.congr' ?_ |>.trans_eq ?_
  · exact heq.symm
  · simp [c, mul_comm]

end Kadiri

