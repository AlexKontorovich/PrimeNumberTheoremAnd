import Architect
import PrimeNumberTheoremAnd.SecondarySummary
import PrimeNumberTheoremAnd.PrimeGaps.Latest

namespace Lcm

open PrimeGapsLatest
open ArithmeticFunction hiding log
open Finset Nat Real

/-!
Numeric certification for the LCM chapter.

This file is intended to be the *only* place where the hard-coded numerical
constants (like the 0.000675 bound) appear, so it can be regenerated when X₀ updates.
-/

noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log


lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  dsimp [X₀]
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num


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
