import RSBounds.PolynomialZeroKernel

/-!
# Cancellation in one of the four additive integrals

This is a refinement of the fourfold method of Rosser--Schoenfeld (1975),
Lemma 8. It uses the cubic sine estimate already proved in Mathlib.
Both the upper and lower averages use the common ordinate band
`4/(3*delta) <= gamma <= 2*(1-4*delta)/delta`.

Build and axiom-audit evidence is recorded in the accompanying verification files.
-/

open Complex MeasureTheory Set
open scoped Interval
open TernaryGoldbach.RSBounds.PolynomialZeroKernel

namespace TernaryGoldbach.RSBounds.PolynomialZeroCancellation

theorem sin_le_cubic {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sin t ≤ t - (47 / 300 : ℝ) * t ^ 3 := by
  have h := (abs_le.mp (Real.sin_bound (x := t) (by simpa [abs_of_nonneg ht0] using ht1))).2
  rw [abs_of_nonneg ht0] at h
  have hp : t ^ 5 ≤ t ^ 3 := by
    calc t ^ 5 = t ^ 3 * t ^ 2 := by ring
      _ ≤ t ^ 3 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1) (pow_nonneg ht0 3)
      _ = t ^ 3 := mul_one _
  nlinarith

theorem cpow_positive_phase {a : ℝ} (ha : 0 < a) (z : ℂ) :
    (a : ℂ) ^ z = (a ^ z.re : ℝ) * Complex.exp (Complex.I * (z.im * Real.log a : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'),
    ← Complex.ofReal_log ha.le, Real.rpow_def_of_pos ha,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

theorem norm_phase_sub (u v : ℝ) :
    ‖Complex.exp (Complex.I * u) - Complex.exp (Complex.I * v)‖ =
      2 * |Real.sin ((u - v) / 2)| := by
  have he : Complex.exp (Complex.I * u) - Complex.exp (Complex.I * v) =
      Complex.exp (Complex.I * v) * (Complex.exp (Complex.I * (u - v : ℝ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  norm_num

theorem norm_cpow_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z : ℂ) (hz : 0 ≤ z.re) :
    ‖(b : ℂ) ^ z - (a : ℂ) ^ z‖ ≤ b ^ z.re - a ^ z.re +
      2 * a ^ z.re * |Real.sin ((z.im * (Real.log b - Real.log a)) / 2)| := by
  have hb : 0 < b := ha.trans_le hab
  have hp : a ^ z.re ≤ b ^ z.re := Real.rpow_le_rpow ha.le hab hz
  have ha0 : 0 ≤ a ^ z.re := Real.rpow_nonneg ha.le _
  rw [cpow_positive_phase hb, cpow_positive_phase ha]
  have he : (b ^ z.re : ℝ) * Complex.exp (Complex.I * (z.im * Real.log b : ℝ)) -
      (a ^ z.re : ℝ) * Complex.exp (Complex.I * (z.im * Real.log a : ℝ)) =
      ((b ^ z.re - a ^ z.re : ℝ) : ℂ) *
        Complex.exp (Complex.I * (z.im * Real.log b : ℝ)) +
      (a ^ z.re : ℝ) * (Complex.exp (Complex.I * (z.im * Real.log b : ℝ)) -
        Complex.exp (Complex.I * (z.im * Real.log a : ℝ))) := by
    push_cast
    ring
  rw [he]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hp), abs_of_nonneg ha0, norm_phase_sub]
  congr 1
  rw [show z.im * Real.log b - z.im * Real.log a = z.im * (Real.log b - Real.log a) by ring]
  ring

theorem rpow_three_halves_increment {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 4 / 3) : b ^ (3 / 2 : ℝ) - a ^ (3 / 2 : ℝ) ≤ 2 * (b - a) := by
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun u : ℝ => u ^ (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * t ^ (1 / 2 : ℝ)) (Icc a b) t := by
    intro t ht
    convert (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (ha.trans_le ht.1)))).hasDerivWithinAt using 1 <;>
      norm_num
  have hm : ∀ t ∈ Ico a b, ‖(3 / 2 : ℝ) * t ^ (1 / 2 : ℝ)‖ ≤ 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hp : t ^ (1 / 2 : ℝ) ≤ 4 / 3 := by
      calc t ^ (1 / 2 : ℝ) ≤ (4 / 3 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow ht0.le (ht.2.le.trans hb) (by norm_num)
        _ ≤ (4 / 3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 / 3 := Real.rpow_one _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hm b (right_mem_Icc.mpr hab)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)

/-- Phase bounds valid simultaneously for the upper and lower smoothing intervals. -/
theorem phase_bounds {δ y γ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.000022)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1 + 3 * δ)
    (hv0 : 4 / 3 ≤ γ * δ) (hv1 : γ * δ ≤ 2 * (1 - 4 * δ)) :
    let θ := γ * (Real.log (y + δ) - Real.log y) / 2
    0 ≤ θ ∧ θ ≤ 1 ∧ γ * δ / (2 * (1 + 4 * δ)) ≤ θ ∧
      θ ≤ γ * δ / (2 * (1 - 4 * δ)) := by
  dsimp only
  have hL : 0 < 1 - 4 * δ := by linarith
  have hy : 0 < y := hL.trans_le hy0
  have hyδ : 0 < y + δ := by linarith
  have hγ : 0 < γ := by nlinarith
  have hq : 0 < (y + δ) / y := div_pos hyδ hy
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  have hhi := Real.log_le_sub_one_of_pos hq
  have hlog : Real.log ((y + δ) / y) = Real.log (y + δ) - Real.log y :=
    Real.log_div hyδ.ne' hy.ne'
  rw [hlog] at hlo hhi
  have helo : 1 - ((y + δ) / y)⁻¹ = δ / (y + δ) := by field_simp; ring
  have hehi : (y + δ) / y - 1 = δ / y := by field_simp; ring
  rw [helo] at hlo
  rw [hehi] at hhi
  have hlow : δ / (1 + 4 * δ) ≤ Real.log (y + δ) - Real.log y := by
    refine (div_le_div_of_nonneg_left hδ.le hyδ (by linarith : y + δ ≤ 1 + 4 * δ)).trans hlo
  have hupp : Real.log (y + δ) - Real.log y ≤ δ / (1 - 4 * δ) := by
    refine hhi.trans ?_
    gcongr
  have hlow' : γ * δ / (2 * (1 + 4 * δ)) ≤ γ * (Real.log (y + δ) - Real.log y) / 2 := by
    convert mul_le_mul_of_nonneg_left hlow (show 0 ≤ γ / 2 by positivity) using 1 <;> field_simp <;> ring
  have hupp' : γ * (Real.log (y + δ) - Real.log y) / 2 ≤ γ * δ / (2 * (1 - 4 * δ)) := by
    convert mul_le_mul_of_nonneg_left hupp (show 0 ≤ γ / 2 by positivity) using 1 <;> field_simp <;> ring
  refine ⟨(by positivity : 0 ≤ γ * δ / (2 * (1 + 4 * δ))).trans hlow',
    hupp'.trans ?_, hlow', hupp'⟩
  exact (div_le_one (by positivity)).mpr hv1

private theorem coefficient_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.000022) :
    (3 / 2 : ℝ) * δ + (1 + 3 * δ) ^ 2 / (1 - 4 * δ) -
      (47 / 675 : ℝ) * (1 + 3 * δ) ^ 2 / (1 + 4 * δ) ^ 3 ≤ 0.931 := by
  have hL : 0 < 1 - 4 * δ := by linarith
  have hB : 0 < 1 + 4 * δ := by positivity
  have hu : (1 + 3 * δ) ^ 2 / (1 - 4 * δ) ≤
      (1 + 3 * (0.000022 : ℝ)) ^ 2 / (1 - 4 * (0.000022 : ℝ)) := by gcongr
  have hl : 1 / (1 + 4 * (0.000022 : ℝ)) ^ 3 ≤
      (1 + 3 * δ) ^ 2 / (1 + 4 * δ) ^ 3 := by
    calc 1 / (1 + 4 * (0.000022 : ℝ)) ^ 3 ≤ 1 / (1 + 4 * δ) ^ 3 := by gcongr
      _ ≤ (1 + 3 * δ) ^ 2 / (1 + 4 * δ) ^ 3 := by
        gcongr
        nlinarith
  norm_num at hu hl ⊢
  simp only [mul_div_assoc] at *
  linarith

private theorem numerator_scalar_bound {δ v : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.000022)
    (hv : 4 / 3 ≤ v) :
    2 * δ + (1 + 3 * δ) ^ 2 *
      (v / (1 - 4 * δ) - (47 / 1200 : ℝ) * v ^ 3 / (1 + 4 * δ) ^ 3) ≤
      0.931 * v := by
  have hv0 : 0 ≤ v := by linarith
  have hpow : (16 / 9 : ℝ) * v ≤ v ^ 3 := by
    nlinarith [sq_nonneg (v - 4 / 3)]
  have hM : 0 ≤ (1 + 3 * δ) ^ 2 := sq_nonneg _
  have hB : 0 < (1 + 4 * δ) ^ 3 := by positivity
  have hneg : (47 / 675 : ℝ) * v / (1 + 4 * δ) ^ 3 ≤
      (47 / 1200 : ℝ) * v ^ 3 / (1 + 4 * δ) ^ 3 := by
    apply (div_le_div_iff_of_pos_right hB).mpr
    nlinarith
  have hc := mul_le_mul_of_nonneg_right (coefficient_le hδ hδ1) hv0
  have hmain : 2 * δ ≤ (3 / 2 : ℝ) * δ * v := by nlinarith
  calc 2 * δ + (1 + 3 * δ) ^ 2 *
      (v / (1 - 4 * δ) - (47 / 1200 : ℝ) * v ^ 3 / (1 + 4 * δ) ^ 3) ≤
      (3 / 2 : ℝ) * δ * v + (1 + 3 * δ) ^ 2 *
        (v / (1 - 4 * δ) - (47 / 675 : ℝ) * v / (1 + 4 * δ) ^ 3) := by
        gcongr
    _ = ((3 / 2 : ℝ) * δ + (1 + 3 * δ) ^ 2 / (1 - 4 * δ) -
        (47 / 675 : ℝ) * (1 + 3 * δ) ^ 2 / (1 + 4 * δ) ^ 3) * v := by ring
    _ ≤ 0.931 * v := hc

/-- Cancellation in the numerator of the first antiderivative. -/
theorem norm_first_numerator_le {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.000022)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1 + 3 * δ)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hv0 : 4 / 3 ≤ ρ.im * δ) (hv1 : ρ.im * δ ≤ 2 * (1 - 4 * δ)) :
    ‖((y + δ : ℝ) : ℂ) ^ (ρ + 1) - (y : ℂ) ^ (ρ + 1)‖ ≤
      0.931 * δ * ρ.im := by
  have hy : 0 < y := by linarith
  have hγ : 0 < ρ.im := by nlinarith
  have hB : 0 < 1 + 4 * δ := by positivity
  have hL : 0 < 1 - 4 * δ := by linarith
  set θ := ρ.im * (Real.log (y + δ) - Real.log y) / 2
  obtain ⟨hθ0, hθ1, hθlo, hθhi⟩ := phase_bounds hδ hδ1 hy0 hy1 hv0 hv1
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0
    (hθ1.trans (by linarith [Real.pi_gt_three]))
  have hs := sin_le_cubic hθ0 hθ1
  have hamp := rpow_three_halves_increment hy (by linarith : y ≤ y + δ)
    (by linarith : y + δ ≤ 4 / 3)
  have hpow : y ^ (3 / 2 : ℝ) ≤ (1 + 3 * δ) ^ 2 := by
    calc y ^ (3 / 2 : ℝ) ≤ (1 + 3 * δ) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hy.le hy1 (by norm_num)
      _ ≤ (1 + 3 * δ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = _ := Real.rpow_ofNat _ _
  have hnum := norm_cpow_sub_le hy (by linarith : y ≤ y + δ) (ρ + 1) (by norm_num [hρ])
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero, hρ] at hnum
  norm_num at hnum
  simp only [← Complex.ofReal_add] at hnum
  rw [abs_of_nonneg hs0] at hnum
  have hcube : (ρ.im * δ / (2 * (1 + 4 * δ))) ^ 3 ≤ θ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hθlo 3
  have hprod := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 2 * Real.sin θ by positivity)
  calc ‖((y + δ : ℝ) : ℂ) ^ (ρ + 1) - (y : ℂ) ^ (ρ + 1)‖ ≤
      2 * δ + 2 * (1 + 3 * δ) ^ 2 * Real.sin θ := by nlinarith
    _ ≤ 2 * δ + 2 * (1 + 3 * δ) ^ 2 * (θ - (47 / 300 : ℝ) * θ ^ 3) := by gcongr
    _ ≤ 2 * δ + 2 * (1 + 3 * δ) ^ 2 *
        (ρ.im * δ / (2 * (1 - 4 * δ)) -
          (47 / 300 : ℝ) * (ρ.im * δ / (2 * (1 + 4 * δ))) ^ 3) := by gcongr
    _ = 2 * δ + (1 + 3 * δ) ^ 2 *
        (ρ.im * δ / (1 - 4 * δ) - (47 / 1200 : ℝ) * (ρ.im * δ) ^ 3 / (1 + 4 * δ) ^ 3) := by
      field_simp [hB.ne', hL.ne']
      ring
    _ ≤ 0.931 * (ρ.im * δ) := numerator_scalar_bound hδ.le hδ1 hv0
    _ = 0.931 * δ * ρ.im := by ring



/-- One step of the same exact fundamental-theorem-of-calculus identity. -/
theorem first_integral_identity {ρ : ℂ} (hρ : 0 < ρ.re) {δ y : ℝ}
    (hδ : 0 ≤ δ) (hy : 0 < y) :
    iteratedIntegral δ 1 (fun t : ℝ => (t : ℂ) ^ ρ / ρ) y =
      (((y + δ : ℝ) : ℂ) ^ (ρ + 1) - (y : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)) := by
  have hz : antiderivative ρ 0 = fun t : ℝ => (t : ℂ) ^ ρ / ρ := by
    funext t
    simp [antiderivative, rising]
  have hc : ∀ x, 0 < x → ContinuousAt (antiderivative ρ 0) x := by
    intro x hx
    rw [hz]
    have hn : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
    exact ((hasDerivAt_ofReal_cpow_const hx.ne' hn).div_const ρ).continuousAt
  have he := iteratedIntegral_eq_forwardDiff hδ (antiderivative ρ)
    (fun n x hx => antiderivative_hasDerivAt hρ n hx) hc 1 y hy
  rw [hz] at he
  rw [he]
  simp only [forwardDiff, antiderivative, rising, Nat.cast_one, Nat.cast_zero, zero_add]
  ring

/-- The first integral gains a uniform factor on the common ordinate band. -/
theorem norm_first_integral_le {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.000022)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1 + 3 * δ)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hv0 : 4 / 3 ≤ ρ.im * δ) (hv1 : ρ.im * δ ≤ 2 * (1 - 4 * δ)) :
    ‖iteratedIntegral δ 1 (fun t : ℝ => (t : ℂ) ^ ρ / ρ) y‖ ≤
      0.931 * δ / ρ.im := by
  have hγ : 0 < ρ.im := by nlinarith
  have hy : 0 < y := by linarith
  have hρ0 : 0 < ρ.re := by rw [hρ]; norm_num
  have hnorm0 : ρ.im ≤ ‖ρ‖ := Complex.im_le_norm ρ
  have hnorm1 : ρ.im ≤ ‖ρ + 1‖ := by simpa using Complex.im_le_norm (ρ + 1)
  have hden : ρ.im ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by nlinarith
  rw [first_integral_identity hρ0 hδ.le hy, norm_div, norm_mul]
  calc ‖((y + δ : ℝ) : ℂ) ^ (ρ + 1) - (y : ℂ) ^ (ρ + 1)‖ / (‖ρ‖ * ‖ρ + 1‖) ≤
      ‖((y + δ : ℝ) : ℂ) ^ (ρ + 1) - (y : ℂ) ^ (ρ + 1)‖ / ρ.im ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hγ 2) hden
    _ ≤ (0.931 * δ * ρ.im) / ρ.im ^ 2 := by
      gcongr
      exact norm_first_numerator_le hδ hδ1 hy0 hy1 hρ hv0 hv1
    _ = 0.931 * δ / ρ.im := by field_simp

/-- Constant norm bounds propagate through the remaining additive averages. -/
theorem norm_iteratedIntegral_le_const_on {h : ℝ} (hh : 0 ≤ h)
    (f : ℝ → ℂ) (C : ℝ) (n : ℕ) :
    ∀ x, (∀ t ∈ Icc x (x + n * h), ‖f t‖ ≤ C) →
      ‖iteratedIntegral h n f x‖ ≤ h ^ n * C := by
  induction n with
  | zero =>
    intro x hf
    simpa [iteratedIntegral] using hf x (by simp)
  | succ n ih =>
    intro x hf
    change ‖∫ u in 0..h, iteratedIntegral h n f (x + u)‖ ≤ _
    have hm : ∀ᵐ u : ℝ, u ∈ Ioc 0 h → ‖iteratedIntegral h n f (x + u)‖ ≤ h ^ n * C := by
      filter_upwards [] with u hu
      apply ih (x + u)
      intro t ht
      apply hf t
      constructor
      · linarith [hu.1, ht.1]
      · simp only [Nat.cast_add, Nat.cast_one] at *
        nlinarith [hu.2, ht.2]
    refine (intervalIntegral.norm_integral_le_of_norm_le hh hm
      (continuous_const.intervalIntegrable 0 h)).trans_eq ?_
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, pow_succ]
    ring

/-- The normalized fourth-difference estimate, for either smoothing interval.
The start point is `1` for the upper average and `1-4*delta` for the lower. -/
theorem norm_normalized_difference_le_band {δ x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.000022)
    (hx0 : 1 - 4 * δ ≤ x) (hx1 : x ≤ 1)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hv0 : 4 / 3 ≤ ρ.im * δ) (hv1 : ρ.im * δ ≤ 2 * (1 - 4 * δ)) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) x / (δ : ℂ) ^ 4‖ ≤ 0.931 / ρ.im := by
  have hx : 0 < x := by linarith
  have hρ0 : 0 < ρ.re := by rw [hρ]; norm_num
  rw [← zero_term_fourfold_identity hρ0 hx hδ.le]
  have hm := norm_iteratedIntegral_le_const_on hδ.le
    (iteratedIntegral δ 1 (fun t : ℝ => (t : ℂ) ^ ρ / ρ))
    (0.931 * δ / ρ.im) 3 x (by
      intro t ht
      apply norm_first_integral_le hδ hδ1 _ _ hρ hv0 hv1
      · exact hx0.trans ht.1
      · norm_num at ht
        linarith [ht.2])
  have he : iteratedIntegral δ 4 (fun t : ℝ => (t : ℂ) ^ ρ / ρ) x =
      iteratedIntegral δ 3 (iteratedIntegral δ 1 (fun t : ℝ => (t : ℂ) ^ ρ / ρ)) x := rfl
  rw [he, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_iff₀ (pow_pos hδ 4)).mpr
  convert hm using 1 <;> ring

theorem norm_upperKernel_le_band {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.000022)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hv0 : 4 / 3 ≤ ρ.im * δ) (hv1 : ρ.im * δ ≤ 2 * (1 - 4 * δ)) :
    ‖upperKernel δ ρ‖ ≤ 0.931 / ρ.im := by
  rw [upperKernel_eq_normalized_difference]
  exact norm_normalized_difference_le_band hδ hδ1 (by linarith) le_rfl hρ hv0 hv1

theorem norm_lower_difference_le_band {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.000022)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hv0 : 4 / 3 ≤ ρ.im * δ) (hv1 : ρ.im * δ ≤ 2 * (1 - 4 * δ)) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ) / (δ : ℂ) ^ 4‖ ≤ 0.931 / ρ.im :=
  norm_normalized_difference_le_band hδ hδ1 le_rfl (by linarith) hρ hv0 hv1

/-- The historical step size is retained exactly. -/
theorem norm_upperKernel_le_band_rs75 {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hlo : 4 / (3 * (0.0000211 : ℝ)) ≤ ρ.im)
    (hhi : ρ.im ≤ 2 * (1 - 4 * (0.0000211 : ℝ)) / 0.0000211) :
    ‖upperKernel 0.0000211 ρ‖ ≤ 0.931 / ρ.im := by
  apply norm_upperKernel_le_band (by norm_num) (by norm_num) hρ <;> norm_num at * <;> linarith

theorem norm_lower_difference_le_band_rs75 {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hlo : 4 / (3 * (0.0000211 : ℝ)) ≤ ρ.im)
    (hhi : ρ.im ≤ 2 * (1 - 4 * (0.0000211 : ℝ)) / 0.0000211) :
    ‖forwardDiff 0.0000211 4 (antiderivative ρ 4) (1 - 4 * 0.0000211) /
      ((0.0000211 : ℝ) : ℂ) ^ 4‖ ≤ 0.931 / ρ.im := by
  apply norm_lower_difference_le_band (by norm_num) (by norm_num) hρ <;> norm_num at * <;> linarith

end TernaryGoldbach.RSBounds.PolynomialZeroCancellation
