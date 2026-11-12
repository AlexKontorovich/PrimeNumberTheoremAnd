import TernaryGoldbach.Prelim.LogWalk
import RSBounds.BacklundCenterNumericsBase
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Rational certificates for the finite zeta sum at height 50

Logs reuse calr3's existing integer artanh walk. Trigonometric values use
Mathlib's eighth-order complex exponential bound after quarter-turn reduction.
All numerical comparisons are rational and intended for kernel reduction.
-/

open Complex Real Finset

namespace TernaryGoldbach.RSBounds.BacklundBottomCertificates
open TernaryGoldbach.Prelim.LogWalk

/-- Integer lower and upper bounds on `10^30 log n`. -/
def logLo : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n = 0 then 0 else logLo n + incrLo n

def logHi : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n = 0 then 0 else logHi n + incrHi n

theorem log_bounds (n : ℕ) (hn : 1 ≤ n) :
    (logLo n : ℝ) ≤ 10 ^ 30 * Real.log n ∧
      10 ^ 30 * Real.log n ≤ (logHi n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [logLo, logHi]
    · have hn1 : 1 ≤ n := by omega
      obtain ⟨hl, hu⟩ := ih hn1
      obtain ⟨hil, hiu⟩ := incr_bounds hn1
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog : Real.log (n + 1 : ℕ) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
        rw [← Real.log_mul hnR.ne' (by positivity)]
        congr 1
        push_cast
        field_simp
      simp only [Nat.cast_add, Nat.cast_one] at hlog
      simp only [logLo, logHi, if_neg hn0, Nat.cast_add, Nat.cast_one]
      rw [hlog]
      constructor <;> linarith

/-- The fixed rational interval for pi is reused from Mathlib's proved bound. -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20
def piHi : ℚ := 314159265358979323847 / 10 ^ 20

def angleCheck (n m : ℕ) (q : ℚ) : Bool := decide
  (-(1 / 100000 : ℚ) ≤ 50 * (logLo n : ℚ) / 10 ^ 30 - q - m * piHi / 2 ∧
    50 * (logHi n : ℚ) / 10 ^ 30 - q - m * piLo / 2 ≤ 1 / 100000)

theorem angleCheck_sound {n m : ℕ} {q : ℚ} (hn : 1 ≤ n)
    (hc : angleCheck n m q = true) :
    |50 * Real.log n - ((q : ℝ) + m * Real.pi / 2)| ≤ 1 / 100000 := by
  have hc' : -(1 / 100000 : ℚ) ≤ 50 * (logLo n : ℚ) / 10 ^ 30 - q - m * piHi / 2 ∧
      50 * (logHi n : ℚ) / 10 ^ 30 - q - m * piLo / 2 ≤ 1 / 100000 :=
    of_decide_eq_true hc
  have hlo := Rat.cast_mono (K := ℝ) hc'.1
  have hhi := Rat.cast_mono (K := ℝ) hc'.2
  push_cast at hlo hhi
  obtain ⟨hl, hu⟩ := log_bounds n hn
  have hpiL : (piLo : ℝ) ≤ Real.pi := by
    norm_num [piLo]
    linarith [Real.pi_gt_d20]
  have hpiU : Real.pi ≤ (piHi : ℝ) := by
    norm_num [piHi]
    linarith [Real.pi_lt_d20]
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hml := mul_le_mul_of_nonneg_left hpiL hm0
  have hmu := mul_le_mul_of_nonneg_left hpiU hm0
  rw [abs_le]
  constructor <;> linarith

noncomputable def taylor (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 8, ((x : ℂ) * I) ^ k / k.factorial

def cosPoly (x : ℚ) : ℚ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
def sinPoly (x : ℚ) : ℚ := x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040

theorem taylor_eq (q : ℚ) :
    taylor (q : ℝ) = (cosPoly q : ℂ) + (sinPoly q : ℂ) * I := by
  unfold taylor cosPoly sinPoly
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring_nf
  simp
  ring

theorem exp_taylor_bound {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp ((x : ℂ) * I) - taylor x‖ ≤ 1 / 30000 := by
  have hnorm : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
  have h := Complex.exp_bound hnorm (by norm_num : (0 : ℕ) < 8)
  have hp : |x| ^ 8 ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  norm_num [Nat.factorial] at h
  unfold taylor
  nlinarith

def cosRot (q : ℚ) (m : ℕ) : ℚ :=
  if m % 4 = 0 then cosPoly q else if m % 4 = 1 then -sinPoly q
  else if m % 4 = 2 then -cosPoly q else sinPoly q

def sinRot (q : ℚ) (m : ℕ) : ℚ :=
  if m % 4 = 0 then sinPoly q else if m % 4 = 1 then cosPoly q
  else if m % 4 = 2 then -sinPoly q else -cosPoly q

theorem taylor_mul_I_pow (q : ℚ) (m : ℕ) :
    taylor (q : ℝ) * I ^ m = (cosRot q m : ℂ) + (sinRot q m : ℂ) * I := by
  rw [taylor_eq, Complex.I_pow_eq_pow_mod]
  have hm : m % 4 < 4 := Nat.mod_lt m (by decide)
  interval_cases h : m % 4 <;> simp [cosRot, sinRot, h] <;> ring_nf <;> simp <;> ring

/-- Taylor error after an exact quarter-turn rotation. -/
theorem rotated_taylor_bound {q : ℚ} (hq : |(q : ℝ)| ≤ 1) (m : ℕ) :
    ‖Complex.exp (((q : ℝ) + m * Real.pi / 2 : ℝ) * I) -
      ((cosRot q m : ℂ) + (sinRot q m : ℂ) * I)‖ ≤ 1 / 30000 := by
  rw [← taylor_mul_I_pow]
  have he : Complex.exp (((q : ℝ) + m * Real.pi / 2 : ℝ) * I) =
      Complex.exp ((q : ℂ) * I) * I ^ m := by
    push_cast
    rw [show ((q : ℂ) + m * Real.pi / 2) * I =
      (q : ℂ) * I + (m : ℂ) * (Real.pi / 2 * I) by ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  rw [he, ← sub_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
  exact exp_taylor_bound hq

/-- A rational reduced angle gives simultaneous sine and cosine certificates. -/
theorem trig_approx {n m : ℕ} {q : ℚ} (hn : 1 ≤ n)
    (hc : angleCheck n m q = true) (hq : |(q : ℝ)| ≤ 1) :
    |Real.cos (50 * Real.log n) - (cosRot q m : ℝ)| ≤ 1 / 10000 ∧
      |Real.sin (50 * Real.log n) - (sinRot q m : ℝ)| ≤ 1 / 10000 := by
  have ha := angleCheck_sound hn hc
  have ht := rotated_taylor_bound hq m
  have hr := (Complex.abs_re_le_norm _).trans ht
  have hi := (Complex.abs_im_le_norm _).trans ht
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_I_re, Complex.ratCast_re,
    Complex.ratCast_im, neg_zero, add_zero, Complex.exp_ofReal_mul_I_re] at hr
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_I_im, Complex.ratCast_re,
    Complex.ratCast_im, zero_add, Complex.exp_ofReal_mul_I_im] at hi
  have hcr := (Real.abs_cos_sub_cos_le (50 * Real.log n)
    ((q : ℝ) + m * Real.pi / 2)).trans ha
  have hsi := (Real.abs_sin_sub_sin_le (50 * Real.log n)
    ((q : ℝ) + m * Real.pi / 2)).trans ha
  constructor
  · have h := abs_add_le (Real.cos (50 * Real.log n) -
      Real.cos ((q : ℝ) + m * Real.pi / 2))
      (Real.cos ((q : ℝ) + m * Real.pi / 2) - (cosRot q m : ℝ))
    rw [sub_add_sub_cancel] at h
    linarith
  · have h := abs_add_le (Real.sin (50 * Real.log n) -
      Real.sin ((q : ℝ) + m * Real.pi / 2))
      (Real.sin ((q : ℝ) + m * Real.pi / 2) - (sinRot q m : ℝ))
    rw [sub_add_sub_cancel] at h
    linarith

end TernaryGoldbach.RSBounds.BacklundBottomCertificates
