import RSBounds.PolynomialAveragedFormula
import RSBounds.PolynomialLeftRemainder

/-!
# The averaged left remainder as an integral

The fourth finite difference is taken inside the convergent left-line
integral. This identifies the exact remainder that must be estimated after
fourfold additive smoothing.
-/

open Complex Set MeasureTheory
open scoped Real

namespace TernaryGoldbach.RSBounds.PolynomialRemainderIntegral

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialQuartic QuarticMellin
open PolynomialZeta PolynomialZeroKernel PolynomialAveraged

noncomputable def leftLine (t : ℝ) : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I

theorem leftLine_re (t : ℝ) : (leftLine t).re = -1 / 2 := by simp [leftLine]

theorem leftLine_ne_one (t : ℝ) : leftLine t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [leftLine] at this
  norm_num at this

theorem zeta_leftLine_ne_zero (t : ℝ) : riemannZeta (leftLine t) ≠ 0 :=
  zeta_ne_zero_of_zetaF (leftLine_ne_one t)
    (zetaF_ne_zero_strip (by rw [leftLine_re]; norm_num)
      (by rw [leftLine_re]; norm_num))

theorem integrable_zeta_contour_left {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => contourIntegrand riemannZeta kernel x (leftLine t)) := by
  have hF := integrable_contour_left ldatum_zeta decayFive_kernel hx
  have h1 := integrable_contour_left ldatum_sub_one decayFive_kernel hx
  convert hF.sub h1 using 1
  funext t
  dsimp only [Pi.sub_apply, contourIntegrand]
  change logDeriv riemannZeta (leftLine t) * (kernel (leftLine t) * (x : ℂ) ^ leftLine t) =
    logDeriv zetaF (leftLine t) * (kernel (leftLine t) * (x : ℂ) ^ leftLine t) -
    logDeriv (fun s : ℂ => s - 1) (leftLine t) * (kernel (leftLine t) * (x : ℂ) ^ leftLine t)
  rw [logDeriv_zetaF_eq (leftLine_ne_one t) (zeta_leftLine_ne_zero t),
    logDeriv_sub_one]
  ring

noncomputable def primitiveIntegrand (x t : ℝ) : ℂ :=
  logDeriv riemannZeta (leftLine t) * antiderivative (leftLine t) 4 x

theorem primitiveIntegrand_eq {x : ℝ} (hx : 0 < x) (t : ℝ) :
    primitiveIntegrand x t = (x : ℂ) ^ 4 *
      contourIntegrand riemannZeta kernel x (leftLine t) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold primitiveIntegrand antiderivative contourIntegrand kernel
  norm_num only [rising, Nat.cast_ofNat]
  rw [Complex.cpow_add _ _ hx0, Complex.cpow_ofNat]
  ring

theorem integrable_primitiveIntegrand {x : ℝ} (hx : 0 < x) :
    Integrable (primitiveIntegrand x) := by
  change Integrable (fun t => primitiveIntegrand x t)
  simpa only [primitiveIntegrand_eq hx] using
    (integrable_zeta_contour_left hx).const_mul ((x : ℂ) ^ 4)

theorem psi4LeftRemainder_eq_integral {x : ℝ} (hx : 0 < x) :
    psi4LeftRemainder x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, primitiveIntegrand x t := by
  simp_rw [primitiveIntegrand_eq hx]
  rw [integral_const_mul]
  unfold psi4LeftRemainder leftLine
  ring

theorem leftRemainder_eq_integral {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    leftRemainder x h = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
        zeroCoefficient x h (leftLine t) := by
  have h0 := integrable_primitiveIntegrand hx
  have h1 := integrable_primitiveIntegrand (show 0 < x + h by linarith)
  have h2 := integrable_primitiveIntegrand (show 0 < x + 2 * h by linarith)
  have h3 := integrable_primitiveIntegrand (show 0 < x + 3 * h by linarith)
  have h4 := integrable_primitiveIntegrand (show 0 < x + 4 * h by linarith)
  have he (t : ℝ) : logDeriv riemannZeta (leftLine t) * zeroCoefficient x h (leftLine t) =
      (primitiveIntegrand (x + 4 * h) t - 4 * primitiveIntegrand (x + 3 * h) t +
        6 * primitiveIntegrand (x + 2 * h) t - 4 * primitiveIntegrand (x + h) t +
          primitiveIntegrand x t) / (h : ℂ) ^ 4 := by
    unfold zeroCoefficient primitiveIntegrand
    rw [forwardDiff_four]
    ring
  simp_rw [he]
  have e4 := integral_sub h4 (h3.const_mul 4)
  have e3 := integral_add (h4.sub (h3.const_mul 4)) (h2.const_mul 6)
  have e2 := integral_sub ((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)) (h1.const_mul 4)
  have e1 := integral_add (((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
    (h1.const_mul 4)) h0
  simp only [Pi.add_apply, Pi.sub_apply, integral_const_mul] at e1 e2 e3 e4
  rw [integral_div, e1, e2, e3, e4]
  unfold leftRemainder
  rw [forwardDiff_four, psi4LeftRemainder_eq_integral hx,
    psi4LeftRemainder_eq_integral (show 0 < x + h by linarith),
    psi4LeftRemainder_eq_integral (show 0 < x + 2 * h by linarith),
    psi4LeftRemainder_eq_integral (show 0 < x + 3 * h by linarith),
    psi4LeftRemainder_eq_integral (show 0 < x + 4 * h by linarith)]
  ring

theorem integrable_averagedIntegrand {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    Integrable (fun t : ℝ => logDeriv riemannZeta (leftLine t) *
      zeroCoefficient x h (leftLine t)) := by
  have h0 := integrable_primitiveIntegrand hx
  have h1 := integrable_primitiveIntegrand (show 0 < x + h by linarith)
  have h2 := integrable_primitiveIntegrand (show 0 < x + 2 * h by linarith)
  have h3 := integrable_primitiveIntegrand (show 0 < x + 3 * h by linarith)
  have h4 := integrable_primitiveIntegrand (show 0 < x + 4 * h by linarith)
  convert ((((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
    (h1.const_mul 4)).add h0).div_const ((h : ℂ) ^ 4) using 1
  funext t
  dsimp only [Pi.add_apply, Pi.sub_apply]
  unfold zeroCoefficient primitiveIntegrand
  rw [forwardDiff_four]
  ring

end TernaryGoldbach.RSBounds.PolynomialRemainderIntegral
