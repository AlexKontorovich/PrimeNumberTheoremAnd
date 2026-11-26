import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# A trapezoidal error bounded by derivative variation

The positive Peano kernel on a unit interval is at most `1/8`. This form
of the trapezoidal bound telescopes over adjacent intervals, unlike a
uniform bound on the second derivative. The definitions and summation
rules for the trapezoidal rule are reused from Mathlib.
-/

open Set MeasureTheory intervalIntegral
open scoped Interval

namespace TernaryGoldbach.RSBounds.BacklundTrapezoid

noncomputable section

def kernel (a x : ℝ) : ℝ := (x - a) * (a + 1 - x) / 2

theorem kernel_nonneg {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    0 ≤ kernel a x := by
  unfold kernel
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
    (by norm_num)

theorem kernel_le {a x : ℝ} : kernel a x ≤ 1 / 8 := by
  unfold kernel
  nlinarith [sq_nonneg (x - a - 1 / 2)]

theorem hasDerivAt_kernel (a x : ℝ) :
    HasDerivAt (kernel a) (a + 1 / 2 - x) x := by
  change HasDerivAt (fun y : ℝ => (y - a) * (a + 1 - y) / 2) _ x
  convert (((hasDerivAt_id x).sub_const a).mul
    ((hasDerivAt_id x).const_sub (a + 1))).div_const 2 using 1 <;>
    norm_num <;> ring

/-- Exact Peano-kernel identity for one unit trapezoid. -/
theorem error_eq_integral_kernel {f f' f'' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hfi : IntervalIntegrable f'' volume a (a + 1)) :
    trapezoidal_error f 1 a (a + 1) =
      ∫ x in a..(a + 1), kernel a x * f'' x := by
  have hab : a ≤ a + 1 := by linarith
  have hu : [[a, a + 1]] = Icc a (a + 1) := uIcc_of_le hab
  have hf0 : ContinuousOn f [[a, a + 1]] := by
    rw [hu]; exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf1 : ContinuousOn f' [[a, a + 1]] := by
    rw [hu]; exact fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hK : Continuous (kernel a) := by unfold kernel; fun_prop
  have hL : Continuous (fun x : ℝ => a + 1 / 2 - x) := by fun_prop
  have h1 := integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1)
    (fun x _ => hasDerivAt_kernel a x)
    (fun x hx => hf' x (hu ▸ hx)) (hL.intervalIntegrable _ _) hfi
  have h2 := integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a + 1)
    (fun x _ => (hasDerivAt_id x).const_sub (a + 1 / 2))
    (fun x hx => hf x (hu ▸ hx))
    (continuous_const.intervalIntegrable _ _) hf1.intervalIntegrable
  have hneg : (∫ x in a..(a + 1), (-1 : ℝ) * f x) =
      -(∫ x in a..(a + 1), f x) := by simp
  rw [hneg] at h2
  have hKa : kernel a a = 0 := by simp [kernel]
  have hKb : kernel a (a + 1) = 0 := by simp [kernel]
  rw [hKa, hKb, zero_mul, zero_mul, sub_self, zero_sub] at h1
  rw [trapezoidal_error, trapezoidal_integral_one]
  simp only [id_eq] at h2
  ring_nf at h1 h2 ⊢
  linarith

/-- For a nonnegative second derivative, the unit-trapezoid error is bounded
by one eighth of the change of the first derivative. -/
theorem error_bounds {f f' f'' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a (a + 1), HasDerivAt f' (f'' x) x)
    (hfi : IntervalIntegrable f'' volume a (a + 1))
    (hnn : ∀ x ∈ Icc a (a + 1), 0 ≤ f'' x) :
    0 ≤ trapezoidal_error f 1 a (a + 1) ∧
      trapezoidal_error f 1 a (a + 1) ≤ (f' (a + 1) - f' a) / 8 := by
  rw [error_eq_integral_kernel hf hf' hfi]
  have hab : a ≤ a + 1 := by linarith
  have hK : Continuous (kernel a) := by unfold kernel; fun_prop
  have hki : IntervalIntegrable (fun x => kernel a x * f'' x) volume a (a + 1) :=
    hfi.continuousOn_mul hK.continuousOn
  constructor
  · exact integral_nonneg hab (fun x hx => mul_nonneg (kernel_nonneg hx) (hnn x hx))
  · have hbound := integral_mono_on hab hki (hfi.const_mul (1 / 8 : ℝ))
      (fun x hx => mul_le_mul_of_nonneg_right kernel_le (hnn x hx))
    have he := integral_eq_sub_of_hasDerivAt
      (fun x hx => hf' x ((uIcc_of_le hab) ▸ hx)) hfi
    rw [intervalIntegral.integral_const_mul, he] at hbound
    linarith

/-- Finite error sum written with a left-endpoint sum and endpoint correction.
This identity includes the empty sum, so it is convenient for limits in `N`. -/
theorem sum_error_eq {f : ℝ → ℝ} {a : ℝ} (N : ℕ)
    (hi : ∀ k < N, IntervalIntegrable f volume (a + k) (a + k + 1)) :
    (∑ k ∈ Finset.range N, trapezoidal_error f 1 (a + k) (a + k + 1)) =
      (∑ k ∈ Finset.range N, f (a + k)) + (f (a + N) - f a) / 2 -
        ∫ x in a..(a + N), f x := by
  have hi' := sum_integral_adjacent_intervals (a := fun k : ℕ => a + k)
    (f := f) (n := N) (fun k hk => by simpa [Nat.cast_add, add_assoc] using hi k hk)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hi'
  have hs := Finset.sum_range_succ' (fun k : ℕ => f (a + k)) N
  rw [Finset.sum_range_succ] at hs
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hs
  simp_rw [trapezoidal_error, trapezoidal_integral_one,
    show ∀ k : ℕ, (a + k + 1 - (a + k)) / 2 = (1 / 2 : ℝ) by intro k; ring]
  rw [Finset.sum_sub_distrib, hi', ← Finset.mul_sum, Finset.sum_add_distrib]
  linarith

end

end TernaryGoldbach.RSBounds.BacklundTrapezoid
