import RSBounds.BacklundGammaModulusDigamma
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A horizontal Gamma modulus comparison

The logarithm here is the real logarithm of a positive norm, so no
choice of a complex logarithm of Gamma is needed.  The quantitative
input is the unconditional Zeta23/IEANTN digamma estimate.
-/

open Complex Real Set
open scoped RealInnerProductSpace

namespace TernaryGoldbach.RSBounds.BacklundGammaModulus

theorem hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun u => Real.log ‖f u‖) (f' / f x).re x := by
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have h := (hf.norm_sq.log (pow_ne_zero 2 hn)).div_const 2
  convert h using 1
  · funext u
    rw [Real.log_pow]
    ring
  · rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.div_re,
      Complex.sq_norm]
    change f'.re * (f x).re / Complex.normSq (f x) +
      f'.im * (f x).im / Complex.normSq (f x) =
      2 * (f' * (starRingEnd ℂ) (f x)).re / Complex.normSq (f x) / 2
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

theorem hasDerivAt_log_norm_Gamma {a t : ℝ} (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖)
      (Complex.digamma ((a : ℂ) + t * I)).re a := by
  have hz : 0 < ((a : ℂ) + t * I).re := by simpa using ha
  have hne := GammaSolution.ne_neg_natCast_of_mem hz
  have hG := (Complex.differentiableAt_Gamma _ hne).hasDerivAt
  have hC := hG.comp (a : ℂ) ((hasDerivAt_id (a : ℂ)).add_const ((t : ℂ) * I))
  have hreal : HasDerivAt (fun x : ℝ => Complex.Gamma ((x : ℂ) + t * I))
      (deriv Complex.Gamma ((a : ℂ) + t * I)) a := by
    simpa using hC.comp_ofReal
  have h := hasDerivAt_log_norm hreal (Complex.Gamma_ne_zero hne)
  simpa [Complex.digamma_def, logDeriv_apply] using h

theorem abs_log_norm_Gamma_sub_le {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ -
      Real.log ‖Complex.Gamma (1 + t * I)‖ - (a - 1) * Real.log t| ≤
      9 / (4 * t ^ 2) := by
  let f : ℝ → ℝ := fun x => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖ - x * Real.log t
  let f' : ℝ → ℝ := fun x => (Complex.digamma ((x : ℂ) + t * I)).re - Real.log t
  have hd : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), HasDerivWithinAt f (f' x)
      (Icc (1 / 2 : ℝ) (3 / 2)) x := by
    intro x hx
    convert! ((hasDerivAt_log_norm_Gamma (t := t)
      (by linarith [hx.1] : 0 < x)).sub
        ((hasDerivAt_id x).mul_const (Real.log t))).hasDerivWithinAt using 1
    simp [f']
  have hb : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), ‖f' x‖ ≤ 9 / (2 * t ^ 2) := by
    intro x hx
    simpa [f', Real.norm_eq_abs] using abs_digamma_re_sub_log_le hx.1 hx.2 ht
  have h := (convex_Icc (1 / 2 : ℝ) (3 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (x := 1) (y := a) (by norm_num) ⟨ha, ha'⟩
  have hdist : |a - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hc : 0 ≤ 9 / (2 * t ^ 2) := by positivity
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (show ‖a - 1‖ ≤ (1 / 2 : ℝ) by simpa [Real.norm_eq_abs] using hdist) hc)
  rw [Real.norm_eq_abs] at h'
  convert h' using 1
  · congr 1
    dsimp [f]
    norm_num
    ring
  · ring

/-- Horizontal comparison, including the reflected bottom edge `1/2 ≤ a ≤ 1`.
The exponent allowance is small enough to retain Backlund's final zeta bound. -/
theorem norm_Gamma_horizontal_le {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      ‖Complex.Gamma (1 + t * I)‖ * t ^ (a - 1) * Real.exp (9 / (4 * t ^ 2)) := by
  have h := (abs_le.mp (abs_log_norm_Gamma_sub_le ha ha' ht)).2
  have hGa : 0 < ‖Complex.Gamma ((a : ℂ) + t * I)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    linarith
  have hG1 : 0 < ‖Complex.Gamma (1 + t * I)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  have ht0 : 0 < t := by linarith
  have he := Real.exp_le_exp.mpr (show
    Real.log ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Real.log ‖Complex.Gamma (1 + t * I)‖ + (a - 1) * Real.log t +
        9 / (4 * t ^ 2) by linarith)
  rw [Real.exp_log hGa, Real.exp_add, Real.exp_add, Real.exp_log hG1] at he
  rw [Real.rpow_def_of_pos ht0]
  simpa [mul_comm (a - 1) (Real.log t)] using he

end TernaryGoldbach.RSBounds.BacklundGammaModulus
