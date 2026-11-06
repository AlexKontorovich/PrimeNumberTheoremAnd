import RSBounds.RS75RealAxisGamma
import RSBounds.RS75XiIncrement
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# A real-axis logarithmic-derivative estimate for the RS75 argument

The analytic completion at one is Mathlib's `riemannZeta₁`, whose derivative
there is Euler's constant. The Gamma increment is bounded by the IEANTN
Gauss series after its first term cancels. The unconditional first-29 xi
increment supplies the remaining improvement. No RH premise is needed.
-/

open Complex Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.RS75RealAxisLogDerivative

open TernaryGoldbach.Explicit RS75RealAxisGamma

theorem zetaF_eq_riemannZeta₁ : zetaF = riemannZeta₁ := by
  funext s
  by_cases hs : s = 1
  · subst s
    rw [zetaF_one, riemannZeta₁_one]
  · rw [zetaF_of_ne hs, riemannZeta_eq_inv_sub_mul hs]
    field_simp [sub_ne_zero.mpr hs]

theorem logDeriv_zetaF_one :
    logDeriv zetaF 1 = (Real.eulerMascheroniConstant : ℂ) := by
  rw [zetaF_eq_riemannZeta₁, logDeriv_apply, deriv_riemannZeta₁_one,
    riemannZeta₁_one, div_one]

/-- The product factorization extends across the removable point at one. -/
theorem xi_factorization {s : ℂ} (hs : 0 < s.re) :
    xiF s = s * Gammaℝ s * zetaF s := by
  by_cases h1 : s = 1
  · subst s
    simp only [xiF_one, Gammaℝ_one, zetaF_one, one_mul]
  · exact xiF_eq hs h1

/-- The xi logarithmic-derivative identity, including the point one. -/
theorem logDeriv_xiF_including_one {s : ℂ} (hs : 0 < s.re) (hxi : xiF s ≠ 0) :
    logDeriv xiF s = 1 / s +
      (-(1 / 2) * Complex.log Real.pi + (1 / 2) * Complex.digamma (s / 2)) +
        logDeriv zetaF s := by
  have hs0 : s ≠ 0 := by intro h; simpa [h] using hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : zetaF s ≠ 0 := by
    intro h
    apply hxi
    rw [xi_factorization hs, h, mul_zero]
  have hGd : DifferentiableAt ℂ Gammaℝ s := by
    have hd := (differentiable_Gammaℝ_inv s).inv (inv_ne_zero hG)
    change DifferentiableAt ℂ (fun w => ((Gammaℝ w)⁻¹)⁻¹) s at hd
    simpa only [inv_inv] using hd
  have hloc : xiF =ᶠ[𝓝 s] fun w => w * Gammaℝ w * zetaF w := by
    have hU : {w : ℂ | 0 < w.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with w hw using xi_factorization hw
  rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
    show (fun w => w * Gammaℝ w * zetaF w) =
      (fun w => w * Gammaℝ w) * zetaF from rfl,
    logDeriv_mul (f := fun w => w * Gammaℝ w) (g := zetaF) s
      (mul_ne_zero hs0 hG) hz (differentiableAt_id.mul hGd) (differentiable_zetaF s),
    show (fun w => w * Gammaℝ w) = (fun w : ℂ => w) * Gammaℝ from rfl,
    logDeriv_mul (f := fun w : ℂ => w) (g := Gammaℝ) s hs0 hG differentiableAt_id hGd,
    logDeriv_id', logDeriv_Gammaℝ hs]

theorem re_logDeriv_xiF_real {s : ℝ} (hs : 1 ≤ s) :
    (logDeriv xiF (s : ℂ)).re = gammaAxis s - Real.log Real.pi / 2 +
      (logDeriv zetaF (s : ℂ)).re := by
  have hpos : 0 < (s : ℂ).re := by simpa using (show 0 < s by linarith)
  have he := logDeriv_xiF_including_one hpos
    (xiF_ne_zero_of_one_le_re (by simpa using hs))
  rw [← Complex.ofReal_log Real.pi_pos.le] at he
  have hr := congrArg Complex.re he
  have hdiv : (1 / (s : ℂ)).re = 1 / s := by norm_cast
  norm_num only [Complex.add_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.one_re, Complex.one_im, zero_mul, sub_zero,
    mul_zero, hdiv] at hr
  unfold gammaAxis
  linarith

theorem endpoint_normalization :
    gammaAxis 1 - Real.log Real.pi / 2 - (logDeriv xiF 1).re =
      -Real.eulerMascheroniConstant := by
  have h := re_logDeriv_xiF_real (s := 1) le_rfl
  rw [Complex.ofReal_one, logDeriv_zetaF_one, Complex.ofReal_re] at h
  linarith

theorem re_logDeriv_zetaF_real {s : ℝ} (hs : 1 < s) :
    (logDeriv zetaF (s : ℂ)).re = 1 / (s - 1) +
      (logDeriv riemannZeta (s : ℂ)).re := by
  have h1 : (s : ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at he
    linarith
  rw [logDeriv_zetaF_eq h1 (riemannZeta_ne_zero_of_one_le_re (by simpa using hs.le)),
    Complex.add_re]
  congr 1
  norm_cast

/-- A sufficient real-axis estimate for the RS75 zero-free-region argument. -/
theorem neg_re_logDeriv_zeta_lt {s : ℝ} (hs : 1 < s) (hs' : s < 1.03) :
    -(logDeriv riemannZeta (s : ℂ)).re <
      1 / (s - 1) - Real.eulerMascheroniConstant + 0.2 * (s - 1) := by
  have hgamma := gammaAxis_increment_le hs.le
  have hxi := RS75XiIncrement.xi_logDeriv_increment_lower hs.le hs'.le
  have hs_id := re_logDeriv_xiF_real hs.le
  have hnorm := endpoint_normalization
  have hz := re_logDeriv_zetaF_real hs
  linarith

end TernaryGoldbach.RSBounds.RS75RealAxisLogDerivative
