import TernaryGoldbach.Explicit.XiPartial

/-!
# Logarithmic growth on the left vertical line

The polynomial zeta datum `ldatum_zeta2` and the existing left-line
logarithmic-derivative estimate give an explicit logarithmic envelope on
`Re s = -1/2`. This is the analytic input for bounding the left remainder
after the normalized fourth difference. No finite RH certificate or
quantitative zero-free region is assumed.
-/

open Complex Set
open scoped Real

namespace TernaryGoldbach.RSBounds.PolynomialLeftRemainder

open TernaryGoldbach.Explicit

/-- The polynomial growth datum has logarithmic size in the ordinate. -/
theorem log_BPz2_le_log_max (t : ℝ) :
    Real.log (BPz2 t / 0.355) ≤ 42 + 10 * Real.log (max 1 |t|) := by
  let v : ℝ := max 1 |t|
  have hv1 : 1 ≤ v := le_max_left _ _
  have htv : |t| ≤ v := le_max_right _ _
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv1
  have h32 : Real.log 32 ≤ 4 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have h16 : Real.log 16 ≤ 3 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have h1 : Real.log (|t| + 22) ≤ Real.log 32 + Real.log v := by
    calc
      Real.log (|t| + 22) ≤ Real.log (32 * v) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := Real.log_mul (by norm_num) hv0.ne'
  have h2 : Real.log (1.25 * (|t| + 11)) ≤ Real.log 16 + Real.log v := by
    calc
      Real.log (1.25 * (|t| + 11)) ≤ Real.log (16 * v) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := Real.log_mul (by norm_num) hv0.ne'
  have h := log_BPz2_le' t
  change Real.log (BPz2 t / 0.355) ≤ 42 + 10 * Real.log v
  linarith

/-- The logarithmic derivative of the entire function `(s-1)ζ(s)` has
logarithmic growth on the line `Re s = -1/2`. -/
theorem norm_logDeriv_zetaF_left_log (t : ℝ) :
    ‖logDeriv zetaF (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      336 + 80 * Real.log (max 1 |t|) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 2 / Real.log 2 + 4.8 ≤ 8 := by
    have hdiv : 2 / Real.log 2 ≤ 3.2 := by
      rw [div_le_iff₀ hl2]
      linarith [Real.log_two_gt_d9]
    linarith
  have hlog : 0 ≤ Real.log (BPz2 t / 0.355) := (polyDatum_zeta2.log_pos t).le
  have hleft := norm_logDeriv_leftD ldatum_zeta2 t
  have he : Real.log (BPz2 t / 0.355) / Real.log 2 / (1 / 2) +
      4.8 * Real.log (BPz2 t / 0.355) =
      (2 / Real.log 2 + 4.8) * Real.log (BPz2 t / 0.355) := by ring
  rw [he] at hleft
  refine hleft.trans ?_
  calc
    (2 / Real.log 2 + 4.8) * Real.log (BPz2 t / 0.355)
        ≤ 8 * Real.log (BPz2 t / 0.355) := mul_le_mul_of_nonneg_right hc hlog
    _ ≤ 8 * (42 + 10 * Real.log (max 1 |t|)) := by
      exact mul_le_mul_of_nonneg_left (log_BPz2_le_log_max t) (by norm_num)
    _ = 336 + 80 * Real.log (max 1 |t|) := by ring

/-- An explicit logarithmic envelope for `ζ'/ζ` on the left line. -/
theorem norm_logDeriv_zeta_left_log (t : ℝ) :
    ‖logDeriv riemannZeta (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      340 + 80 * Real.log (max 1 |t|) := by
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  have hsre : s.re = -1 / 2 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsre
    norm_num at hsre
  have hz : riemannZeta s ≠ 0 :=
    zeta_ne_zero_of_zetaF hs1 (zetaF_ne_zero_strip
      (by rw [hsre]; norm_num) (by rw [hsre]; norm_num))
  have hld : logDeriv riemannZeta s = logDeriv zetaF s - 1 / (s - 1) := by
    rw [logDeriv_zetaF_eq hs1 hz]
    ring
  have hinv : ‖1 / (s - 1)‖ ≤ (2 / 3 : ℝ) := by
    rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hs1))]
    have h := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre] at h
    norm_num at h ⊢
    linarith
  have hleft : ‖logDeriv zetaF s‖ ≤ 336 + 80 * Real.log (max 1 |t|) :=
    norm_logDeriv_zetaF_left_log t
  change ‖logDeriv riemannZeta s‖ ≤ 340 + 80 * Real.log (max 1 |t|)
  rw [hld]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- A relaxed envelope convenient for the original remainder constants. -/
theorem norm_logDeriv_zeta_left_log_500 (t : ℝ) :
    ‖logDeriv riemannZeta (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      500 + 80 * Real.log (max 1 |t|) := by
  linarith [norm_logDeriv_zeta_left_log t]

end TernaryGoldbach.RSBounds.PolynomialLeftRemainder
