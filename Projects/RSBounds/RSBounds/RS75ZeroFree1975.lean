import RSBounds.RS75DirichletPositivity
import RSBounds.RS75RealAxisLogDerivative
import RSBounds.RS75GoldenRatio
import RSBounds.RS75Frequency
import RSBounds.RS75ZeroFreeOptimization
import RSBounds.RS75FiniteHandoff

/-!
# The Rosser--Schoenfeld 1975 zero-free region

The high-height part is unconditional. The finite-RH premise is used only
on the closed interval of absolute ordinates from 21 through 1894439.
The proof uses the actual Dirichlet-series difference, the actual xi
logarithmic derivative and Stechkin's theorem, the exact RS75 polynomial,
and the separately checked real-axis, Gamma and scalar estimates.

Source: Rosser--Schoenfeld (1975), Theorem 1, pp. 247--250,
https://doi.org/10.1090/S0025-5718-1975-0457373-7.
-/

open Complex Finset
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.RS75ZeroFree1975

open TernaryGoldbach.Explicit RS75Parameters RS75Polynomial
open RS75ZeroFreeScalars RS75Frequency

noncomputable section

/-- The actual series difference at the variable RS75 parameters. -/
def difference (σ t : ℝ) : ℝ :=
  RS75DirichletPositivity.D σ (sigma0 σ) (kappa σ) t

/-- The actual xi logarithmic-derivative difference. -/
def xiDifference (σ t : ℝ) : ℝ :=
  (logDeriv xiF (point σ t)).re -
    kappa σ * (logDeriv xiF (point (sigma0 σ) t)).re

def frequencyMain (σ t : ℝ) : ℝ :=
  (1 - kappa σ) / 2 * Real.log (t / (2 * Real.pi)) + 15 / t ^ 2

private theorem point_re (a t : ℝ) : (point a t).re = a := by simp [point]
private theorem point_im (a t : ℝ) : (point a t).im = t := by simp [point]

theorem xiDifference_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ xiDifference σ t := by
  have h := stechkin_xi_nonneg (s := point σ t) (s1 := point (sigma0 σ) t)
    (by rw [point_re]; exact hσ)
    (by rw [point_re, point_re]; exact sigma0_gt hσ.le)
    (by rw [point_im, point_im])
    (by rw [point_re, point_re]; exact stechkin_square_condition hσ.le)
  rw [point_re, point_re, ← kappa_eq_half_ratio hσ.le] at h
  exact h

/-- At the ordinate of the chosen zero, both Phi terms are real reciprocals. -/
theorem Phi_point_aligned (a : ℝ) (ρ : ℂ) :
    Phi (point a ρ.im) ρ = 1 / (a - ρ.re) + 1 / (a - 1 + ρ.re) := by
  have h1 : point a ρ.im - ρ = ((a - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [point]
  have h2 : point a ρ.im - (1 - conj ρ) = ((a - 1 + ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [point]
    ring
  rw [Phi, h1, h2]
  simp only [← Complex.ofReal_inv, Complex.ofReal_re, one_div]

/-- The reflected partner pays for the shifted pair, retaining the full pole. -/
theorem xiDifference_ge_reciprocal {σ : ℝ} (hσ : 1 < σ) {ρ : ℂ}
    (hρ : xiF ρ = 0) (hρre : ρ.re ≠ 1 / 2) :
    1 / (σ - ρ.re) ≤ xiDifference σ ρ.im := by
  have hz := xiF_zero_re hρ
  have h := stechkin_xi (s := point σ ρ.im) (s1 := point (sigma0 σ) ρ.im)
    (by rw [point_re]; exact hσ)
    (by rw [point_re, point_re]; exact sigma0_gt hσ.le)
    (by rw [point_im, point_im])
    (by rw [point_re, point_re]; exact stechkin_square_condition hσ.le)
    hρ hρre
  rw [point_re, point_re, ← kappa_eq_half_ratio hσ.le,
    Phi_point_aligned, Phi_point_aligned] at h
  have hr := shifted_pair_le_reflected hσ hz.1.le hz.2.le
  unfold xiDifference
  linarith

theorem difference_zero_lt {σ : ℝ} (hσ : 1 < σ) (hσ' : σ < 1.03) :
    difference σ 0 < 1 / (σ - 1) +
      (kappa σ * (-1.1398 + 3.3606 * (σ - 1)) -
        Real.eulerMascheroniConstant + 0.2 * (σ - 1)) := by
  unfold difference
  rw [RS75DirichletPositivity.D_eq_logDeriv hσ (sigma0_gt_one hσ)]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  have hn := RS75RealAxisLogDerivative.neg_re_logDeriv_zeta_lt hσ hσ'
  have hg := RS75GoldenRatio.shifted_real_axis_bound hσ hσ'
  have hkg := mul_lt_mul_of_pos_left hg (kappa_pos hσ.le)
  linarith

theorem difference_le_frequency {σ t : ℝ} (hσ : 1 < σ) (hσ' : σ < 1.03)
    (ht : 100 ≤ t) : difference σ t ≤ frequencyMain σ t - xiDifference σ t := by
  have hf := RS75Frequency.logDeriv_difference_le hσ
    (sigma_le_five_fourths hσ'.le) (sigma0_gt_one hσ)
    (sigma0_lt_three hσ.le hσ'.le).le (kappa_pos hσ.le).le
    (kappa_lt_half hσ.le hσ'.le).le ht
  unfold difference
  rw [RS75DirichletPositivity.D_eq_logDeriv hσ (sigma0_gt_one hσ)]
  exact hf

private theorem sum_all_eq (f : ℝ → ℝ) (t : ℝ) :
    (∑ k ∈ Finset.range 5, coeff k * f ((k : ℝ) * t)) =
      a0 * f 0 + ∑ k ∈ Finset.Icc 1 4, coeff k * f ((k : ℝ) * t) := by
  norm_num [Finset.sum_range_succ, Finset.sum_Icc_succ_top, coeff, a0]
  ring

/-- Exact logarithmic and reciprocal-square sums for the four frequencies. -/
theorem sum_frequencyMain_eq {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    (∑ k ∈ Finset.Icc 1 4, coeff k * frequencyMain σ ((k : ℝ) * t)) =
      (1 - kappa σ) / 2 * (A0 * Real.log t - RS75ZeroFreeScalars.D) +
        15 * H / t ^ 2 := by
  have hpoint : ∀ k ∈ Finset.Icc 1 4,
      coeff k * frequencyMain σ ((k : ℝ) * t) =
        (1 - kappa σ) / 2 *
          (coeff k * Real.log t - coeff k * Real.log (2 * Real.pi / k)) +
        (15 / t ^ 2) * (coeff k / (k : ℝ) ^ 2) := by
    intro k hk
    have hkN : 0 < k := by have hh := (Finset.mem_Icc.mp hk).1; omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hkN
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    have he : (k : ℝ) * t / (2 * Real.pi) = t / (2 * Real.pi / k) := by
      field_simp [hk0.ne', hpi]
    have hl : Real.log ((k : ℝ) * t / (2 * Real.pi)) =
        Real.log t - Real.log (2 * Real.pi / k) := by
      rw [he, Real.log_div ht.ne' (div_ne_zero hpi hk0.ne')]
    unfold frequencyMain
    rw [hl]
    field_simp [ht.ne', hk0.ne']
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_positive_coefficients_Icc]
  unfold A0 RS75ZeroFreeScalars.D H
  ring

/-- Summing the actual frequency estimates retains the chosen zero's pole. -/
theorem positive_frequency_sum_le {σ : ℝ} (hσ : 1 < σ) (hσ' : σ < 1.03)
    {ρ : ℂ} (hρ : xiF ρ = 0) (hρre : ρ.re ≠ 1 / 2) (ht : 100 ≤ ρ.im) :
    (∑ k ∈ Finset.Icc 1 4, coeff k * difference σ ((k : ℝ) * ρ.im)) +
      a1 / (σ - ρ.re) ≤
        (1 - kappa σ) / 2 * (A0 * Real.log ρ.im - RS75ZeroFreeScalars.D) +
          15 * H / ρ.im ^ 2 := by
  have hsum :
      (∑ k ∈ Finset.Icc 1 4, coeff k * difference σ ((k : ℝ) * ρ.im)) +
      (∑ k ∈ Finset.Icc 1 4, coeff k * xiDifference σ ((k : ℝ) * ρ.im)) ≤
      ∑ k ∈ Finset.Icc 1 4, coeff k * frequencyMain σ ((k : ℝ) * ρ.im) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkt : 100 ≤ (k : ℝ) * ρ.im := ht.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hk1 (show 0 ≤ ρ.im by linarith))
    have hf := difference_le_frequency hσ hσ' hkt
    have hh := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hf) (coeff_nonneg k)
    simpa only [mul_add] using hh
  have hchosen : a1 / (σ - ρ.re) ≤
      ∑ k ∈ Finset.Icc 1 4, coeff k * xiDifference σ ((k : ℝ) * ρ.im) := by
    have hp := mul_le_mul_of_nonneg_left (xiDifference_ge_reciprocal hσ hρ hρre)
      (coeff_nonneg 1)
    have hs : coeff 1 * xiDifference σ ρ.im ≤
        ∑ k ∈ Finset.Icc 1 4, coeff k * xiDifference σ ((k : ℝ) * ρ.im) := by
      simpa only [Nat.cast_one, one_mul] using
        (Finset.single_le_sum (s := Finset.Icc (1 : ℕ) 4) (a := 1)
        (f := fun k => coeff k * xiDifference σ ((k : ℝ) * ρ.im))
        (fun k _ => mul_nonneg (coeff_nonneg k) (xiDifference_nonneg hσ _))
        (by norm_num : (1 : ℕ) ∈ Finset.Icc 1 4))
    have he : coeff 1 * (1 / (σ - ρ.re)) = a1 / (σ - ρ.re) := by
      norm_num [coeff, a1]
      <;> ring
    rw [he] at hp
    exact hp.trans hs
  rw [sum_frequencyMain_eq (by linarith) σ] at hsum
  linarith

/-- The complete analytic inequality, before the exact optimized scalar step. -/
theorem analytic_inequality {σ : ℝ} (hσ : 1 < σ) (hσ' : σ < 1.03)
    {ρ : ℂ} (hρ : xiF ρ = 0) (hρre : ρ.re ≠ 1 / 2) (ht : 100 ≤ ρ.im) :
    a1 / (σ - ρ.re) < a0 / (σ - 1) +
      a0 * (kappa σ * (-1.1398 + 3.3606 * (σ - 1)) -
        Real.eulerMascheroniConstant + 0.2 * (σ - 1)) +
      (1 - kappa σ) / 2 * (A0 * Real.log ρ.im - 52.38865) +
      15 * H / ρ.im ^ 2 := by
  have hpos := RS75DirichletPositivity.weighted_D_nonneg hσ (sigma0_gt hσ.le).le
    ⟨(kappa_pos hσ.le).le, (kappa_lt_one hσ.le).le⟩ ρ.im
  change 0 ≤ ∑ k ∈ Finset.range 5, coeff k * difference σ ((k : ℝ) * ρ.im) at hpos
  rw [sum_all_eq] at hpos
  have hz := mul_lt_mul_of_pos_left (difference_zero_lt hσ hσ') a0_pos
  have hf := positive_frequency_sum_le hσ hσ' hρ hρre ht
  have hreplace :
      (1 - kappa σ) / 2 * (A0 * Real.log ρ.im - RS75ZeroFreeScalars.D) ≤
      (1 - kappa σ) / 2 * (A0 * Real.log ρ.im - 52.38865) := by
    have hD : (52.38865 : ℝ) < RS75ZeroFreeScalars.D := by linarith [D_lower]
    apply mul_le_mul_of_nonneg_left (sub_le_sub_left hD.le _)
    linarith [kappa_lt_one hσ.le]
  have ha : a0 * (1 / (σ - 1)) = a0 / (σ - 1) := by ring
  rw [mul_add, ha] at hz
  linarith

/-- The high-height xi-zero bound is unconditional and has a strict boundary. -/
theorem xi_zero_re_lt_pos {ρ : ℂ} (hρ : xiF ρ = 0) (ht : 1894439 ≤ ρ.im) :
    ρ.re < 1 - 1 / (9.645908801 * Real.log (ρ.im / 17)) := by
  by_cases hb : ρ.re ≤ 1 / 2
  · exact hb.trans_lt (RS75FiniteHandoff.boundary_gt_half (by linarith))
  have hb' : ρ.re ≠ 1 / 2 := ne_of_gt (lt_of_not_ge hb)
  have hz := xiF_zero_re hρ
  let w := Real.log (ρ.im / 17)
  let x := v / w
  have hw : 0 < w := Real.log_pos
    ((lt_div_iff₀ (show (0 : ℝ) < 17 by norm_num)).mpr (by linarith))
  have hx : 0 < x ∧ x < 0.029172 := chosen_x_bounds ht
  have hσ : 1 < 1 + x := by linarith [hx.1]
  have hσ' : 1 + x < 1.03 := by linarith [hx.2]
  have hi := analytic_inequality hσ hσ' hρ hb' (by linarith)
  have hr : rawResidual x + 15 * H / ρ.im ^ 2 < -0.0009 := chosen_residual_lt ht
  have hdiv : v / x = w := by
    dsimp [x]
    field_simp [hw.ne', v_pos.ne']
  have hlog : Real.log ρ.im = w + Real.log 17 := by
    dsimp [w]
    rw [Real.log_div (show ρ.im ≠ 0 by linarith) (by norm_num)]
    ring
  have ha : a0 / x = a0 / v * w := by
    dsimp [x]
    field_simp [hw.ne', v_pos.ne']
  have he : a0 / x +
      a0 * (kappa (1 + x) * (-1.1398 + 3.3606 * x) -
        Real.eulerMascheroniConstant + 0.2 * x) +
      (1 - kappa (1 + x)) / 2 * (A0 * Real.log ρ.im - 52.38865) +
      15 * H / ρ.im ^ 2 =
        (a0 / v + h) * w + rawResidual x + 15 * H / ρ.im ^ 2 := by
    rw [ha, hlog]
    unfold rawResidual
    rw [hdiv]
    unfold h
    ring
  simp only [add_sub_cancel_left] at hi
  rw [he] at hi
  have hop : a1 / (1 + v / w - ρ.re) < (a0 / v + h) * w := by
    change a1 / (1 + x - ρ.re) < _
    linarith
  have hbR := beta_lt_of_optimized_inequality hw hz.2.le hop
  have hR : R1 < (9.645908801 : ℝ) := by linarith [R1_upper]
  have hd : 1 / (9.645908801 * w) < 1 / (R1 * w) :=
    one_div_lt_one_div_of_lt (mul_pos R1_pos hw) (mul_lt_mul_of_pos_right hR hw)
  change ρ.re < 1 - 1 / (9.645908801 * w)
  linarith

/-- The unconditional high-height result for either sign of the ordinate. -/
theorem xi_zero_re_lt {ρ : ℂ} (hρ : xiF ρ = 0) (ht : 1894439 ≤ |ρ.im|) :
    ρ.re < 1 - 1 / (9.645908801 * Real.log (|ρ.im| / 17)) := by
  by_cases hi : 0 ≤ ρ.im
  · rw [abs_of_nonneg hi] at ht ⊢
    exact xi_zero_re_lt_pos hρ ht
  · have hneg : ρ.im < 0 := lt_of_not_ge hi
    have hc : xiF (conj ρ) = 0 := by rw [xiF_conj, hρ, map_zero]
    have habs : (conj ρ).im = |ρ.im| := by simp [abs_of_neg hneg]
    have hh := xi_zero_re_lt_pos hc (by rw [habs]; exact ht)
    simpa only [Complex.conj_re, habs] using hh

/-- High-height nonvanishing for the actual Riemann zeta function. -/
theorem zero_free_high {s : ℂ} (ht : 1894439 ≤ |s.im|)
    (hσ : 1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hh := RS75FiniteHandoff.boundary_gt_half (t := |s.im|) (by linarith)
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by
    by_contra hn
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hn) hz
  have hξ := (xiF_eq_zero_iff hs0 hs1).2 hz
  exact (xi_zero_re_lt hξ ht).not_ge hσ

/-- The complete RS75 target, with finite RH confined to the finite handoff. -/
theorem proved : Goals.ZeroFreeRegion1975 :=
  RS75FiniteHandoff.of_high (fun _ ht hσ => zero_free_high ht hσ)

theorem zero_free (hRH : Goals.FiniteRH 1894439) {s : ℂ}
    (ht : 21 ≤ |s.im|)
    (hσ : 1 - 1 / (9.645908801 * Real.log (|s.im| / 17)) ≤ s.re) :
    riemannZeta s ≠ 0 :=
  proved hRH s ht hσ

end
end TernaryGoldbach.RSBounds.RS75ZeroFree1975
