import TernaryGoldbach.Explicit.ZeroFreeRegion
import RSBounds.BacklundGammaModulusDigamma

/-!
# The nonzero-frequency bound in the RS75 Stechkin argument

The actual zeta/xi identity is reused from the pinned explicit development.
The Gamma estimate is the checked IEANTN/Zeta23-based bound already used
in the Rosser count proof. Its two errors cost at most `13.5 / t^2`;
the positive rational poles cost at most `1.5 / t^2`.

The result is deliberately stated for independent real parameters, so the
RS75 choice of sigma0 and kappa can be substituted without introducing a
dependency on its separate scalar certificate.
-/

open Complex Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.RS75Frequency

open TernaryGoldbach.Explicit

noncomputable section

def point (a t : ℝ) : ℂ := (a : ℂ) + t * I

def poles (a t : ℝ) : ℝ :=
  a / (a ^ 2 + t ^ 2) + (a - 1) / ((a - 1) ^ 2 + t ^ 2)

theorem inv_re_point (a t : ℝ) :
    (1 / point a t).re = a / (a ^ 2 + t ^ 2) := by
  simp [point, one_div, Complex.inv_re, Complex.normSq_apply, pow_two]

theorem poles_eq (a t : ℝ) :
    (1 / point a t).re + (1 / (point a t - 1)).re = poles a t := by
  have he : point a t - 1 = point (a - 1) t := by
    simp only [point, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he, inv_re_point, inv_re_point]
  rfl

theorem poles_nonneg {a t : ℝ} (ha : 1 ≤ a) : 0 ≤ poles a t := by
  unfold poles
  apply add_nonneg
  · exact div_nonneg (by linarith) (by positivity)
  · exact div_nonneg (by linarith) (by positivity)

theorem poles_le {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t) :
    poles a t ≤ (2 * a - 1) / t ^ 2 := by
  have ht2 : 0 < t ^ 2 := by positivity
  have h1 : a / (a ^ 2 + t ^ 2) ≤ a / t ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) ht2 (by nlinarith [sq_nonneg a])
  have h2 : (a - 1) / ((a - 1) ^ 2 + t ^ 2) ≤ (a - 1) / t ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) ht2 (by nlinarith [sq_nonneg (a - 1)])
  calc
    _ ≤ a / t ^ 2 + (a - 1) / t ^ 2 := add_le_add h1 h2
    _ = _ := by ring

theorem neg_zeta_logDeriv_re_eq {a t : ℝ} (ha : 1 < a) :
    -(logDeriv riemannZeta (point a t)).re =
      -(logDeriv xiF (point a t)).re + poles a t -
        1 / 2 * Real.log Real.pi +
        1 / 2 * (Complex.digamma (point a t / 2)).re := by
  have hs : 1 < (point a t).re := by simpa [point] using ha
  have hid := re_vM_eq hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hid
  have hleft : (-(deriv riemannZeta (point a t)) / riemannZeta (point a t)).re =
      -(logDeriv riemannZeta (point a t)).re := by
    simp only [logDeriv_apply, neg_div, Complex.neg_re]
  rw [hleft] at hid
  calc
    _ = -(logDeriv xiF (point a t)).re + (1 / point a t).re +
        (1 / (point a t - 1)).re - 1 / 2 * Real.log Real.pi +
        1 / 2 * (Complex.digamma (point a t / 2)).re := hid
    _ = _ := by linarith [poles_eq a t]

theorem abs_digamma_half_re_sub_log_le {a t : ℝ}
    (ha : 1 ≤ a) (ha' : a ≤ 3) (ht : 100 ≤ t) :
    |(Complex.digamma (point a t / 2)).re - Real.log (t / 2)| ≤ 18 / t ^ 2 := by
  have h := BacklundGammaModulus.abs_digamma_re_sub_log_le
    (a := a / 2) (t := t / 2) (by linarith) (by linarith) (by linarith)
  have hp : point a t / 2 = ((a / 2 : ℝ) : ℂ) + (t / 2 : ℝ) * I := by
    simp only [point, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  calc
    _ = |(Complex.digamma (((a / 2 : ℝ) : ℂ) + (t / 2 : ℝ) * I)).re -
          Real.log (t / 2)| := by rw [hp]
    _ ≤ 9 / (2 * (t / 2) ^ 2) := h
    _ = 18 / t ^ 2 := by
      field_simp [show t ≠ 0 by linarith] <;> ring

theorem digamma_half_re_bounds {a t : ℝ}
    (ha : 1 ≤ a) (ha' : a ≤ 3) (ht : 100 ≤ t) :
    Real.log (t / 2) - 18 / t ^ 2 ≤ (Complex.digamma (point a t / 2)).re ∧
      (Complex.digamma (point a t / 2)).re ≤ Real.log (t / 2) + 18 / t ^ 2 := by
  have h := abs_le.mp (abs_digamma_half_re_sub_log_le ha ha' ht)
  constructor <;> linarith [h.1, h.2]

/-- The actual nonzero-frequency estimate. No zero-count, finite-RH or
quantitative zero-free-region premise is used. -/
theorem logDeriv_difference_le {σ σ₀ κ t : ℝ}
    (hσ : 1 < σ) (hσ' : σ ≤ 5 / 4)
    (hσ₀ : 1 < σ₀) (hσ₀' : σ₀ ≤ 3)
    (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 2) (ht : 100 ≤ t) :
    -(logDeriv riemannZeta (point σ t)).re +
        κ * (logDeriv riemannZeta (point σ₀ t)).re ≤
      (1 - κ) / 2 * Real.log (t / (2 * Real.pi)) + 15 / t ^ 2 -
        ((logDeriv xiF (point σ t)).re - κ * (logDeriv xiF (point σ₀ t)).re) := by
  have ht0 : 0 < t := by linarith
  have hg := digamma_half_re_bounds hσ.le (by linarith : σ ≤ 3) ht
  have hg₀ := digamma_half_re_bounds hσ₀.le hσ₀' ht
  have hgamma :
      ((Complex.digamma (point σ t / 2)).re -
          κ * (Complex.digamma (point σ₀ t / 2)).re) / 2 ≤
        (1 - κ) / 2 * Real.log (t / 2) + 9 * (1 + κ) / t ^ 2 := by
    calc
      _ ≤ ((Real.log (t / 2) + 18 / t ^ 2) -
          κ * (Real.log (t / 2) - 18 / t ^ 2)) / 2 :=
        div_le_div_of_nonneg_right
          (sub_le_sub hg.2 (mul_le_mul_of_nonneg_left hg₀.1 hκ)) (by norm_num)
      _ = _ := by ring
  have hpoles : poles σ t - κ * poles σ₀ t ≤ (2 * σ - 1) / t ^ 2 :=
    (sub_le_self _ (mul_nonneg hκ (poles_nonneg hσ₀.le))).trans (poles_le hσ.le ht0)
  have hcost : (2 * σ - 1) / t ^ 2 + 9 * (1 + κ) / t ^ 2 ≤ 15 / t ^ 2 := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
  have hlog : Real.log (t / 2) - Real.log Real.pi =
      Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_div (by positivity : t / 2 ≠ 0) Real.pi_ne_zero, div_div]
  calc
    _ = (-(logDeriv riemannZeta (point σ t)).re) -
        κ * (-(logDeriv riemannZeta (point σ₀ t)).re) := by ring
    _ = -((logDeriv xiF (point σ t)).re -
          κ * (logDeriv xiF (point σ₀ t)).re) +
        (poles σ t - κ * poles σ₀ t) - (1 - κ) / 2 * Real.log Real.pi +
        ((Complex.digamma (point σ t / 2)).re -
          κ * (Complex.digamma (point σ₀ t / 2)).re) / 2 := by
      rw [neg_zeta_logDeriv_re_eq hσ, neg_zeta_logDeriv_re_eq hσ₀]
      ring
    _ ≤ -((logDeriv xiF (point σ t)).re -
          κ * (logDeriv xiF (point σ₀ t)).re) +
        (2 * σ - 1) / t ^ 2 - (1 - κ) / 2 * Real.log Real.pi +
        ((1 - κ) / 2 * Real.log (t / 2) + 9 * (1 + κ) / t ^ 2) := by
      linarith
    _ = (1 - κ) / 2 * (Real.log (t / 2) - Real.log Real.pi) +
        ((2 * σ - 1) / t ^ 2 + 9 * (1 + κ) / t ^ 2) -
        ((logDeriv xiF (point σ t)).re - κ * (logDeriv xiF (point σ₀ t)).re) := by ring
    _ ≤ (1 - κ) / 2 * (Real.log (t / 2) - Real.log Real.pi) + 15 / t ^ 2 -
        ((logDeriv xiF (point σ t)).re - κ * (logDeriv xiF (point σ₀ t)).re) := by linarith
    _ = _ := by rw [hlog]

end

end TernaryGoldbach.RSBounds.RS75Frequency
