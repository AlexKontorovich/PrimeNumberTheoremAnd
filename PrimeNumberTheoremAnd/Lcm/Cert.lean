import Architect
import PrimeNumberTheoremAnd.Lcm.Base

namespace Lcm

open ArithmeticFunction hiding log
open Finset Nat Real

/-!
Numeric certification for the LCM chapter.

This file is intended to be the *only* place where the hard-coded numerical
constants (like the 0.000675 bound) appear, so it can be regenerated when X₀ updates.
-/

noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log



-- What was refactored out of theorem exists_p_primes
-- lemma 1
lemma hx₀_pos : (0 : ℝ) < X₀ := by
    unfold X₀; norm_num
@[simp] lemma X₀_pos : (0 : ℝ) < (X₀ : ℝ) := by
  exact hx₀_pos

-- lemma 2
lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


-- lemma 3
lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  dsimp [X₀]
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

-- lemma 4
lemma hlog {n : ℕ} (hn : n ≥ X₀ ^ 2) : log √(n : ℝ) ≥ 11.4 := by
  have hpos : (0 : ℝ) < X₀ := by
    -- try without unfolding first
   unfold X₀
   norm_num
  calc log √(n : ℝ) ≥ log (X₀ : ℝ) :=
        log_le_log hpos (hsqrt_ge hn)
    _ ≥ 11.4 := log_X₀_gt.le


lemma hε_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
  positivity [hlog hn]

lemma log_X₀_pos : 0 < Real.log X₀ := by linear_combination log_X₀_gt




/-- (C1) `x := √n` is above the provider threshold. -/
lemma sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ √(n : ℝ) := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


/-- (C2) positivity of `x := √n`. -/
lemma sqrt_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < √(n : ℝ) := by
  -- can be `lt_of_lt_of_le (show (0:ℝ) < (X₀:ℝ) from ...) (sqrt_ge_X₀ hn)`
  -- or whatever you currently do
  sorry

/-- (C3) nonnegativity of `ε := δ(x)` at `x := √n`. -/
lemma eps_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ gap.δ (√(n : ℝ)) := by
  -- Dusart: follows from `0 < log x` hence `(log x)^3 > 0` hence `1/(...) ≥ 0`.
  -- Other providers: whatever you can prove.
  sorry

/-- (C4) step-1 threshold propagation:
`x*(1+ε)` is still ≥ X₀ so we can apply the provider at that point. -/
lemma step1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) := by
  -- uses sqrt_ge_X₀ + eps_nonneg + le_mul_of_one_le_right etc
  sorry

/-- (C5) step-2 threshold propagation:
`x*(1+ε)^2` is still ≥ X₀. -/
lemma step2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
  -- same pattern; uses `pow_two`/`sq_nonneg` etc
  sorry

/-- (C6) step-1 *upper bound* simplifier:
turn provider’s bound at `y = x*(1+ε)` into a bound by `x*(1+ε)^2`. -/
lemma step1_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ x * (1 + ε) ^ 2 := by
  -- This is exactly where your old `upper` lemma + log monotonicity lives.
  -- For Dusart: δ decreases with x, so δ(x*(1+ε)) ≤ δ(x)=ε, then multiply out.
  sorry

/-- (C7) step-2 upper bound:
turn provider’s bound at `y = x*(1+ε)^2` into ≤ `x*(1+ε)^3`. -/
lemma step2_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2)) ≤ x * (1 + ε) ^ 3 := by
  -- Same style as step1_upper.
  sorry



@[blueprint
  "lem:eps-bounds"
  (title := "Uniform bounds for large \\(n\\)")
  (statement := /--
  For all \(n \ge X_0^2\) we have
  \[
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{X_0}\cdot\frac{1}{n}.
  \]
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/X_0}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
-- theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
--     1 / (log √(n : ℝ)) ^ 3 ≤ eps_log := by
--   dsimp [X₀] at *
--   calc
--     1 / Real.log √n ^ 3 ≤ 1 / Real.log X₀ ^ 3 := by
--       gcongr
--       exact Real.le_sqrt_of_sq_le (mod_cast hn)
--     _ ≤ eps_log := by
--       grw [← log_X₀_gt.le]
--       simpa [eps_log] using (show (1 / (11.4 : ℝ) ^ 3) ≤ (0.000675 : ℝ) by norm_num)



theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ eps_log := by
    sorry

@[blueprint
  "lem:eps-bounds"
  (title := "Uniform bounds for large \\(n\\)")
  (statement := /--
  For all \(n \ge X_0^2\) we have
  \[
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{X_0}\cdot\frac{1}{n}.
  \]
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/X_0}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
-- theorem inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
--     1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / (n : ℝ)) := by
--   have hn_pos : (0 : ℝ) < n := cast_pos.mpr (lt_of_lt_of_le (by grind) hn)
--   rw [one_div_mul_one_div, one_div_le_one_div (rpow_pos_of_pos hn_pos _)
--     (mul_pos (by norm_num) hn_pos), show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
--       rpow_add hn_pos, rpow_one, mul_comm, ← sqrt_eq_rpow]
--   refine mul_le_mul_of_nonneg_left ?_ hn_pos.le
--   have := Real.sqrt_le_sqrt (cast_le.mpr hn)
--   simp_all

theorem inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / (n : ℝ)) := by
  sorry

@[blueprint
  "lem:eps-bounds"
  (title := "Uniform bounds for large \\(n\\)")
  (statement := /--
  For all \(n \ge X_0^2\) we have
  \[
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{X_0}\cdot\frac{1}{n}.
  \]
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/X_0}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")
  (discussion := 511)]
theorem inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  sorry

@[blueprint
  "lem:poly-ineq"
  (title := "Polynomial approximation of the inequality")
  (statement := /--
  For \(0 \le \varepsilon \le 1/X_0^2\), we have
  \[
    \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
    \le
    \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
  \]
  and
  \[
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i}}\frac{1}{1 + 1/X_0}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{X_0}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
  \[
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  \]
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
  -/)
  (latexEnv := "lemma")]
theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith

@[blueprint
  "lem:poly-ineq"
  (title := "Polynomial approximation of the inequality")
  (statement := /--
  For \(0 \le \varepsilon \le 1/X_0^2\), we have
  \[
    \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
    \le
    \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
  \]
  and
  \[
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i} (1 + \frac{1}{X_0})}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{X_0}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
  \[
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  \]
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
  -/)
  (latexEnv := "lemma")]
theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  dsimp [X₀] at *
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]


@[blueprint
  "lem:final-comparison"
  (title := "Final polynomial comparison")
  (statement := /--
  For \(0 \le \varepsilon \le 1/X_0^2\), we have
  \[
    1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  This is equivalent to
  \[
    3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 3.36683\varepsilon - 0.01\varepsilon^2,
  \]
  or
  \[
    0 \le (3.36683 - 3.01)\varepsilon - (3.01+0.01)\varepsilon^2 - 1.01\varepsilon^3.
  \]
  Factor out \(\varepsilon\) and use that \(0<\varepsilon \le 1/X_0^2\) to check that the
  resulting quadratic in \(\varepsilon\) is nonnegative on this interval.  Again, this is a
  finite computation that can be verified mechanically.
  -/)
  (latexEnv := "lemma")]
theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
    dsimp [X₀] at *
    nlinarith



end Lcm
