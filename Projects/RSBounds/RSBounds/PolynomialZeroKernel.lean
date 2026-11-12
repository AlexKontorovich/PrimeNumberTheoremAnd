import Mathlib

/-!
# Fourfold additive integration of a single zeta-zero term

These identities and bounds concern the kernel in Rosser--Schoenfeld (1975),
Lemma 8. No statement about the zeros or the prime-counting functions is assumed.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace TernaryGoldbach.RSBounds.PolynomialZeroKernel

/-- Iterated forward differences with additive step `h`. -/
def forwardDiff (h : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | n + 1, f => fun x => forwardDiff h n f (x + h) - forwardDiff h n f x

/-- Iterated integrals over `[0,h]`, with every integration adding its variable. -/
noncomputable def iteratedIntegral (h : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | n + 1, f => fun x => ∫ u in 0..h, iteratedIntegral h n f (x + u)

theorem forwardDiff_four (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    forwardDiff h 4 f x = f (x + 4 * h) - 4 * f (x + 3 * h) +
      6 * f (x + 2 * h) - 4 * f (x + h) + f x := by
  simp only [forwardDiff]
  rw [show x + h + h + h + h = x + 4 * h by ring,
    show x + h + h + h = x + 3 * h by ring,
    show x + h + h = x + 2 * h by ring]
  ring

theorem hasDerivAt_forwardDiff {h : ℝ} (hh : 0 ≤ h) {F f : ℝ → ℂ}
    (hF : ∀ x, 0 < x → HasDerivAt F (f x) x) (n : ℕ) :
    ∀ x, 0 < x → HasDerivAt (forwardDiff h n F) (forwardDiff h n f x) x := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    intro x hx
    have hd := (ih (x + h) (by linarith)).scomp x ((hasDerivAt_id x).add_const h)
    convert hd.sub (ih x hx) using 1
    · funext y; rfl
    · simp only [forwardDiff, one_smul]

theorem continuousAt_forwardDiff {h : ℝ} (hh : 0 ≤ h) {f : ℝ → ℂ}
    (hf : ∀ x, 0 < x → ContinuousAt f x) (n : ℕ) :
    ∀ x, 0 < x → ContinuousAt (forwardDiff h n f) x := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro x hx
    have hs : ContinuousAt (fun y : ℝ => y + h) x := continuousAt_id.add_const h
    have hc : ContinuousAt (fun y => forwardDiff h n f (y + h)) x :=
      (ih (x + h) (by linarith)).comp (f := fun y : ℝ => y + h) hs
    exact hc.sub (ih x hx)

/-- Repeated fundamental theorem of calculus, with all domain restrictions visible. -/
theorem iteratedIntegral_eq_forwardDiff {h : ℝ} (hh : 0 ≤ h)
    (F : ℕ → ℝ → ℂ)
    (hF : ∀ n x, 0 < x → HasDerivAt (F (n + 1)) (F n x) x)
    (hc : ∀ x, 0 < x → ContinuousAt (F 0) x) (n : ℕ) :
    ∀ x, 0 < x → iteratedIntegral h n (F 0) x = forwardDiff h n (F n) x := by
  have hcont : ∀ n x, 0 < x → ContinuousAt (F n) x := by
    intro n x hx
    cases n with
    | zero => exact hc x hx
    | succ n => exact (hF n x hx).continuousAt
  induction n with
  | zero => intro x hx; rfl
  | succ n ih =>
    intro x hx
    change (∫ u in 0..h, iteratedIntegral h n (F 0) (x + u)) = _
    have heq : (∫ u in 0..h, iteratedIntegral h n (F 0) (x + u)) =
        ∫ u in 0..h, forwardDiff h n (F n) (x + u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hh] at hu
      exact ih (x + u) (by linarith [hu.1])
    rw [heq]
    have hd : ∀ u ∈ uIcc 0 h,
        HasDerivAt (fun v => forwardDiff h n (F (n + 1)) (x + v))
          (forwardDiff h n (F n) (x + u)) u := by
      intro u hu
      rw [uIcc_of_le hh] at hu
      have h := (hasDerivAt_forwardDiff hh (hF n) n (x + u) (by linarith [hu.1])).scomp u
        ((hasDerivAt_id u).const_add x)
      simpa only [Function.comp_def, one_smul] using h
    have hi : IntervalIntegrable (fun u => forwardDiff h n (F n) (x + u)) volume 0 h := by
      apply ContinuousOn.intervalIntegrable
      intro u hu
      rw [uIcc_of_le hh] at hu
      exact ((continuousAt_forwardDiff hh (hcont n) n (x + u) (by linarith [hu.1])).comp
        (continuousAt_id.const_add x)).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    simp only [add_zero, forwardDiff]

/-- The product `rho (rho+1) ... (rho+n)`. -/
def rising (ρ : ℂ) : ℕ → ℂ
  | 0 => ρ
  | n + 1 => rising ρ n * (ρ + (n + 1 : ℕ))

/-- Successive antiderivatives of `x^rho/rho`. -/
noncomputable def antiderivative (ρ : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (ρ + n) / rising ρ n

theorem add_nat_ne_zero {ρ : ℂ} (hρ : 0 < ρ.re) (n : ℕ) : ρ + n ≠ 0 := by
  intro heq
  have h := congrArg Complex.re heq
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h
  linarith

theorem antiderivative_hasDerivAt {ρ : ℂ} (hρ : 0 < ρ.re)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (antiderivative ρ (n + 1)) (antiderivative ρ n x) x := by
  have hr : ρ + (n : ℂ) ≠ -1 := by
    intro heq
    have h := congrArg Complex.re heq
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re, Complex.one_re] at h
    linarith
  have hd := (hasDerivAt_ofReal_cpow_const' hx.ne' hr).div_const (rising ρ n)
  convert hd using 1
  · funext y
    simp only [antiderivative, rising, Nat.cast_add, Nat.cast_one, add_assoc]
    rw [div_div]
    congr 1
    ring
  · rfl

/-- The repeated integral is exactly the finite difference of the fourth antiderivative. -/
theorem zero_term_fourfold_identity {ρ : ℂ} (hρ : 0 < ρ.re)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    iteratedIntegral h 4 (fun t => (t : ℂ) ^ ρ / ρ) x =
      forwardDiff h 4 (antiderivative ρ 4) x := by
  have hz : antiderivative ρ 0 = fun t : ℝ => (t : ℂ) ^ ρ / ρ := by
    funext t
    simp [antiderivative, rising]
  have hc : ∀ x, 0 < x → ContinuousAt (antiderivative ρ 0) x := by
    intro x hx
    have hr : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
    rw [hz]
    exact ((hasDerivAt_ofReal_cpow_const hx.ne' hr).div_const ρ).continuousAt
  simpa only [hz] using
    iteratedIntegral_eq_forwardDiff hh (antiderivative ρ)
      (fun n x hx => antiderivative_hasDerivAt hρ n hx) hc 4 x hx

private theorem integral_affine (A B h : ℝ) :
    (∫ u in 0..h, A + B * u) = A * h + B * h ^ 2 / 2 := by
  have hiA : IntervalIntegrable (fun _ : ℝ => A) volume 0 h :=
    continuous_const.intervalIntegrable 0 h
  have hiB : IntervalIntegrable (fun u : ℝ => B * u) volume 0 h :=
    (show Continuous (fun u : ℝ => B * u) by fun_prop).intervalIntegrable 0 h
  rw [intervalIntegral.integral_add hiA hiB,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    smul_eq_mul]
  ring

/-- The norm of an iterated integral is bounded by the exact average of any
affine majorant valid to the right of the initial point. -/
theorem norm_iteratedIntegral_le_affine {h : ℝ} (hh : 0 ≤ h)
    (f : ℝ → ℂ) (A B : ℝ) (n : ℕ) :
    ∀ x, (∀ t, x ≤ t → ‖f t‖ ≤ A + B * t) →
      ‖iteratedIntegral h n f x‖ ≤
        h ^ n * (A + B * x + B * (n : ℝ) * h / 2) := by
  induction n with
  | zero =>
    intro x hf
    simpa only [iteratedIntegral, pow_zero, Nat.cast_zero, mul_zero, zero_mul,
      zero_div, add_zero, one_mul] using hf x le_rfl
  | succ n ih =>
    intro x hf
    change ‖∫ u in 0..h, iteratedIntegral h n f (x + u)‖ ≤ _
    have hm : ∀ᵐ u : ℝ, u ∈ Ioc 0 h →
        ‖iteratedIntegral h n f (x + u)‖ ≤
          h ^ n * (A + B * (x + u) + B * (n : ℝ) * h / 2) := by
      filter_upwards [] with u hu
      exact ih (x + u) (fun t ht => hf t (by linarith [hu.1]))
    have hc : Continuous (fun u : ℝ =>
        h ^ n * (A + B * (x + u) + B * (n : ℝ) * h / 2)) := by fun_prop
    refine (intervalIntegral.norm_integral_le_of_norm_le hh hm
      (hc.intervalIntegrable 0 h)).trans_eq ?_
    have heq : (fun u : ℝ => h ^ n * (A + B * (x + u) + B * (n : ℝ) * h / 2)) =
        fun u => h ^ n * ((A + B * x + B * (n : ℝ) * h / 2) + B * u) := by
      funext u
      ring
    rw [heq, intervalIntegral.integral_const_mul, integral_affine]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem norm_zero_term_le_affine {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {x t : ℝ} (hx : 0 < x) (ht : x ≤ t) :
    ‖(t : ℂ) ^ ρ / ρ‖ ≤ (x ^ ρ.re / (x * ‖ρ‖)) * t := by
  have ht0 : 0 < t := hx.trans_le ht
  have hn : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hn
  have hr : 1 ≤ t / x := (le_div_iff₀ hx).2 (by simpa using ht)
  have hp : (t / x) ^ ρ.re ≤ t / x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr hρ1
  have he : t ^ ρ.re = x ^ ρ.re * (t / x) ^ ρ.re := by
    calc t ^ ρ.re = (x * (t / x)) ^ ρ.re := by congr 1; field_simp
      _ = _ := Real.mul_rpow hx.le (by positivity)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0, he]
  calc (x ^ ρ.re * (t / x) ^ ρ.re) / ‖ρ‖ ≤
      (x ^ ρ.re * (t / x)) / ‖ρ‖ := by gcongr
    _ = (x ^ ρ.re / (x * ‖ρ‖)) * t := by field_simp

/-- The low-zero estimate, before dividing by the smoothing volume `h^4`. -/
theorem norm_fourth_difference_le_low {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖forwardDiff h 4 (antiderivative ρ 4) x‖ ≤
      h ^ 4 * (x ^ ρ.re / ‖ρ‖) * (1 + 2 * h / x) := by
  rw [← zero_term_fourfold_identity hρ hx hh]
  have hf : ∀ t, x ≤ t → ‖(t : ℂ) ^ ρ / ρ‖ ≤ 0 + (x ^ ρ.re / (x * ‖ρ‖)) * t := by
    intro t ht
    simpa only [zero_add] using norm_zero_term_le_affine hρ hρ1 hx ht
  have hm := norm_iteratedIntegral_le_affine hh (fun t => (t : ℂ) ^ ρ / ρ)
    0 (x ^ ρ.re / (x * ‖ρ‖)) 4 x hf
  have hn : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
  have hn0 : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  refine hm.trans_eq ?_
  norm_num
  field_simp [hx.ne', hn0]
  ring

theorem norm_normalized_fourth_difference_le_low {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖forwardDiff h 4 (antiderivative ρ 4) x / (h : ℂ) ^ 4‖ ≤
      (x ^ ρ.re / ‖ρ‖) * (1 + 2 * h / x) := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_iff₀ (pow_pos hh 4)]
  have hm := norm_fourth_difference_le_low hρ hρ1 hx hh.le
  nlinarith

/-- The dimensionless fourth-difference numerator. -/
noncomputable def numerator (δ : ℝ) (ρ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 5,
    (-1 : ℂ) ^ j * (Nat.choose 4 j : ℂ) * ((1 + (j : ℝ) * δ : ℝ) : ℂ) ^ (ρ + 4)

/-- The normalized zero coefficient for the upper fourfold average. -/
noncomputable def upperKernel (δ : ℝ) (ρ : ℂ) : ℂ :=
  numerator δ ρ / ((δ : ℂ) ^ 4 * rising ρ 4)

def R4 (δ : ℝ) : ℝ := ((1 + δ) ^ 5 + 1) ^ 4

theorem upperKernel_eq_normalized_difference (δ : ℝ) (ρ : ℂ) :
    upperKernel δ ρ = forwardDiff δ 4 (antiderivative ρ 4) 1 / (δ : ℂ) ^ 4 := by
  simp only [upperKernel, numerator, forwardDiff_four, antiderivative]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The dimensionless low-zero estimate from RS75 Lemma 8. -/
theorem norm_upperKernel_le_low {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ (1 + 2 * δ) / ‖ρ‖ := by
  rw [upperKernel_eq_normalized_difference]
  have hm := norm_normalized_fourth_difference_le_low hρ hρ1 (by norm_num : (0 : ℝ) < 1) hδ
  simpa only [Real.one_rpow, one_div, div_one, inv_one, one_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hm

theorem norm_numerator_le_R4 {δ : ℝ} (hδ : 0 ≤ δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖numerator δ ρ‖ ≤ R4 δ := by
  have hterm (j : ℕ) :
      ‖(-1 : ℂ) ^ j * (Nat.choose 4 j : ℂ) *
          ((1 + (j : ℝ) * δ : ℝ) : ℂ) ^ (ρ + 4)‖ ≤
        (Nat.choose 4 j : ℝ) * (((1 + δ) ^ 5) ^ j) := by
    have hb : 1 ≤ 1 + (j : ℝ) * δ := by
      linarith [mul_nonneg (Nat.cast_nonneg j) hδ]
    have hb0 : 0 < 1 + (j : ℝ) * δ := by linarith
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_natCast, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb0]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hp : (1 + (j : ℝ) * δ) ^ (ρ + 4).re ≤ (1 + (j : ℝ) * δ) ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb (by simpa using (show ρ.re + 4 ≤ 5 by linarith))
    rw [Real.rpow_ofNat] at hp
    have hber : 1 + (j : ℝ) * δ ≤ (1 + δ) ^ j :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) j
    calc (1 + (j : ℝ) * δ) ^ (ρ + 4).re ≤ (1 + (j : ℝ) * δ) ^ 5 := hp
      _ ≤ ((1 + δ) ^ j) ^ 5 := pow_le_pow_left₀ hb0.le hber 5
      _ = ((1 + δ) ^ 5) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold numerator
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq ?_)
  set z := (1 + δ) ^ 5
  change (∑ j ∈ Finset.range 5, (Nat.choose 4 j : ℝ) * z ^ j) = (z + 1) ^ 4
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The high-zero estimate from RS75 Lemma 8, with its exact polynomial numerator bound. -/
theorem norm_upperKernel_le_high {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ R4 δ / (δ ^ 4 * ‖rising ρ 4‖) := by
  unfold upperKernel
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (norm_numerator_le_R4 hδ.le hρ) (by positivity)


/-! The same integration argument extends to the left contour Re(s) = -1/2. -/

theorem antiderivative_hasDerivAt_of_neg_one_lt {ρ : ℂ} (hρ : -1 < ρ.re)
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (antiderivative ρ (n + 1)) (antiderivative ρ n x) x := by
  have hr : ρ + (n : ℂ) ≠ -1 := by
    intro heq
    have h := congrArg Complex.re heq
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re, Complex.one_re] at h
    linarith
  have hd := (hasDerivAt_ofReal_cpow_const' hx.ne' hr).div_const (rising ρ n)
  convert hd using 1
  · funext y
    simp only [antiderivative, rising, Nat.cast_add, Nat.cast_one, add_assoc]
    rw [div_div]
    congr 1
    ring
  · rfl

theorem zero_term_fourfold_identity_of_neg_one_lt {ρ : ℂ} (hρ : -1 < ρ.re) (hn : ρ ≠ 0)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    iteratedIntegral h 4 (fun t => (t : ℂ) ^ ρ / ρ) x =
      forwardDiff h 4 (antiderivative ρ 4) x := by
  have hz : antiderivative ρ 0 = fun t : ℝ => (t : ℂ) ^ ρ / ρ := by
    funext t
    simp [antiderivative, rising]
  have hc : ∀ x, 0 < x → ContinuousAt (antiderivative ρ 0) x := by
    intro x hx
    rw [hz]
    exact ((hasDerivAt_ofReal_cpow_const hx.ne' hn).div_const ρ).continuousAt
  simpa only [hz] using
    iteratedIntegral_eq_forwardDiff hh (antiderivative ρ)
      (fun n x hx => antiderivative_hasDerivAt_of_neg_one_lt hρ n hx) hc 4 x hx

theorem norm_zero_term_le_affine_of_ne_zero {ρ : ℂ} (hn : ρ ≠ 0) (hρ1 : ρ.re ≤ 1)
    {x t : ℝ} (hx : 0 < x) (ht : x ≤ t) :
    ‖(t : ℂ) ^ ρ / ρ‖ ≤ (x ^ ρ.re / (x * ‖ρ‖)) * t := by
  have ht0 : 0 < t := hx.trans_le ht
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hn
  have hr : 1 ≤ t / x := (le_div_iff₀ hx).2 (by simpa using ht)
  have hp : (t / x) ^ ρ.re ≤ t / x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr hρ1
  have he : t ^ ρ.re = x ^ ρ.re * (t / x) ^ ρ.re := by
    calc t ^ ρ.re = (x * (t / x)) ^ ρ.re := by congr 1; field_simp
      _ = _ := Real.mul_rpow hx.le (by positivity)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0, he]
  calc (x ^ ρ.re * (t / x) ^ ρ.re) / ‖ρ‖ ≤
      (x ^ ρ.re * (t / x)) / ‖ρ‖ := by gcongr
    _ = (x ^ ρ.re / (x * ‖ρ‖)) * t := by field_simp

theorem norm_fourth_difference_le_low_of_neg_one_lt {ρ : ℂ} (hρ : -1 < ρ.re) (hn : ρ ≠ 0) (hρ1 : ρ.re ≤ 1)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖forwardDiff h 4 (antiderivative ρ 4) x‖ ≤
      h ^ 4 * (x ^ ρ.re / ‖ρ‖) * (1 + 2 * h / x) := by
  rw [← zero_term_fourfold_identity_of_neg_one_lt hρ hn hx hh]
  have hf : ∀ t, x ≤ t → ‖(t : ℂ) ^ ρ / ρ‖ ≤ 0 + (x ^ ρ.re / (x * ‖ρ‖)) * t := by
    intro t ht
    simpa only [zero_add] using norm_zero_term_le_affine_of_ne_zero hn hρ1 hx ht
  have hm := norm_iteratedIntegral_le_affine hh (fun t => (t : ℂ) ^ ρ / ρ)
    0 (x ^ ρ.re / (x * ‖ρ‖)) 4 x hf
  have hn0 : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  refine hm.trans_eq ?_
  norm_num
  field_simp [hx.ne', hn0]
  ring

theorem norm_normalized_fourth_difference_le_low_of_neg_one_lt {ρ : ℂ}
    (hρ : -1 < ρ.re) (hn : ρ ≠ 0) (hρ1 : ρ.re ≤ 1) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖forwardDiff h 4 (antiderivative ρ 4) x / (h : ℂ) ^ 4‖ ≤
      (x ^ ρ.re / ‖ρ‖) * (1 + 2 * h / x) := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_iff₀ (pow_pos hh 4)]
  have hm := norm_fourth_difference_le_low_of_neg_one_lt hρ hn hρ1 hx hh.le
  nlinarith

theorem norm_upperKernel_le_low_of_neg_one_lt {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (hρ : -1 < ρ.re) (hn : ρ ≠ 0) (hρ1 : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ (1 + 2 * δ) / ‖ρ‖ := by
  rw [upperKernel_eq_normalized_difference]
  have hm := norm_normalized_fourth_difference_le_low_of_neg_one_lt hρ hn hρ1 (by norm_num : (0 : ℝ) < 1) hδ
  simpa only [Real.one_rpow, one_div, div_one, inv_one, one_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hm

end TernaryGoldbach.RSBounds.PolynomialZeroKernel
