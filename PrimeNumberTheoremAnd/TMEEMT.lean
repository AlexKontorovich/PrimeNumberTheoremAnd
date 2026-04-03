import Architect
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.Dusart
import PrimeNumberTheoremAnd.RSPrimeLower
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.LogTables
import PrimeNumberTheoremAnd.PrimeTables

blueprint_comment /--
\section{Results from the TME-EMT wiki}

Here we record the results from https://archimede.pages.math.cnrs.fr/tme-emt-wiki/index.html

Some of these results are already stated elsewhere.  In such cases, we can fill in the sorrys with the already stated results.

-/

open Real Chebyshev
open ArithmeticFunction hiding log


blueprint_comment /--
\subsection{Explicit bounds on primes}

The results below are taken from https://archimede.pages.math.cnrs.fr/tme-emt-wiki/Art01.html -/

namespace Buthe2

blueprint_comment /--
Some results from \cite{Buthe2}-/

@[blueprint
  "thm:buthe-2a"
  (title := "Buthe Theorem 2, part a")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\psi(x) - x| \leq \frac{\sqrt{x}}{8\pi}\log(x)^2 \text{for $x>59$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2a (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 59) :
  |ψ x - x| ≤ (sqrt x) * (log x) ^ 2 / (8 * π) := by sorry

@[blueprint
  "thm:buthe-2b"
  (title := "Buthe Theorem 2, part b")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\vartheta(x) - x| \leq \frac{\sqrt{x}}{8\pi}\log(x)^2 \text{for $x>599$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2b (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 599) :
  |θ x - x| ≤ (sqrt x) * (log x) ^ 2 / (8 * π) := by sorry

@[blueprint
  "thm:buthe-2c"
  (title := "Buthe Theorem 2, part c")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\pi^*(x) - \li(x)| \leq \frac{\sqrt{x}}{8\pi}\log(x) \text{for $x>59$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2c (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 59) :
  |pi_star x - li x| ≤ (sqrt x) * log x / (8 * π) := by sorry

@[blueprint
  "thm:buthe-2d"
  (title := "Buthe Theorem 2, part d")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\pi(x) - \li(x)| \leq \frac{\sqrt{x}}{8\pi}\log(x) \text{for $x>2657$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2d (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 2657) :
  |pi x - li x| ≤ (sqrt x) * log x / (8 * π) := by sorry

end Buthe2

namespace Buthe

blueprint_comment /--
Some results from \cite{Buthe}-/

@[blueprint
  "thm:buthe-a"
  (title := "Buthe Theorem a")
  (statement := /-- We have $|\psi(x) - x| \leq 0.94\sqrt{x}$ when $11 < x \leq 10^{19}$. -/)
  (latexEnv := "theorem")]
theorem theorem_a (x : ℝ) (hx1 : x > 11) (hx2 : x ≤ (10 : ℝ) ^ 19) :
    |ψ x - x| ≤ 0.94 * sqrt x := by sorry

@[blueprint
  "thm:buthe-b"
  (title := "Buthe Theorem b")
  (statement := /-- We have $0 < \mathrm{li}(x) - \pi(x) \leq \frac{\sqrt{x}}{\log x}\left(1.95 + \frac{3.9}{\log x} + \frac{19.5}{\log^2 x}\right)$ when $2 \leq x \leq 10^{19}$. -/)
  (latexEnv := "theorem")]
theorem theorem_b (x : ℝ) (hx1 : x ≥ 2) (hx2 : x ≤ (10 : ℝ) ^ 19) :
    0 < li x - pi x ∧
    li x - pi x ≤ sqrt x / log x * (1.95 + 3.9 / log x + 19.5 / (log x)^2) := by sorry

end Buthe

namespace RS_prime

blueprint_comment /--
Some results from \cite{rs-prime}-/

@[blueprint
  "thm:rs-1962-a"
  (title := "Rosser-Schoenfeld 1962, part a")
  (statement := /-- For $x > 0$, we have $\psi(x) \leq 1.03883\, x$. -/)
  (latexEnv := "theorem")]
theorem theorem_a (x : ℝ) (hx : x > 0) :
    ψ x ≤ 1.03883 * x :=
  le_of_lt (by rw [show (1.03883 : ℝ) = RS_prime.c₀ from rfl]; exact theorem_12 hx)

@[blueprint
  "thm:rs-1962-b"
  (title := "Rosser-Schoenfeld 1962, part b")
  (statement := /-- For $x \geq 17$, we have $\pi(x) > x / \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_b (x : ℝ) (hx : x ≥ 17) :
    pi x > x / log x := by sorry

@[blueprint
  "thm:rs-1962-c"
  (title := "Rosser-Schoenfeld 1962, part c")
  (statement := /-- For $x > 1$, we have $\sum_{p \leq x} \frac{1}{p} > \log \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_c (x : ℝ) (hx : x > 1) :
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 / (p : ℝ)) > log (log x) := by sorry

@[blueprint
  "thm:rs-1962-d"
  (title := "Rosser-Schoenfeld 1962, part d")
  (statement := /-- For $x > 1$, we have $\sum_{p \leq x} \frac{\log p}{p} < \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_d (x : ℝ) (hx : x > 1) :
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (log p / p) < log x := by sorry

end RS_prime

namespace Dusart1999

blueprint_comment /--
Some results from \cite{Dusart1999}-/

@[blueprint
  "thm:dusart1999-pi"
  (title := "Dusart 1999, $\\pi$ inequality")
  (statement := /-- For $x \geq 17$, we have $\pi(x) > \frac{x}{\log x - 1}$. -/)
  (latexEnv := "theorem")]
theorem pi_inequality (x : ℝ) (hx : x ≥ 5393) :
    pi x ≥ x / (log x - 1) :=
  Dusart.corollary_5_3_a hx

private lemma log_ge_22 {x : ℝ} (hx : x ≥ exp 22) : log x ≥ 22 := by
  calc (22 : ℝ) = log (exp 22) := (log_exp 22).symm
    _ ≤ log x := log_le_log (exp_pos _) hx

private lemma theta_err {x : ℝ} (hx : x ≥ exp 22) :
    |θ x - x| ≤ 0.001 * x / (log x) ^ 2 := by
  have hmem : (2, (0.001 : ℝ), (908994923 : ℝ)) ∈ Dusart.Table_4_2 := by simp [Dusart.Table_4_2]
  have hlog2 : (0 : ℝ) < (log x) ^ 2 := pow_pos (log_pos (by linarith [add_one_le_exp (22 : ℝ)])) 2
  have := Dusart.theorem_4_2 hmem (le_trans (le_of_lt (by interval_auto)) hx)
  simp only [Eθ, div_le_div_iff₀ (lt_of_lt_of_le (exp_pos _) hx) hlog2] at this
  grind [le_div_iff₀ hlog2]

private lemma psi_theta_err {x : ℝ} (hx : x > 0) :
    ψ x - θ x ≤ 1.001 * sqrt x + 1.78 * x ^ (1 / 3 : ℝ) := by
  linarith [Dusart.corollary_4_5 hx, sqrt_nonneg x]

private lemma psi_triangle (x : ℝ) :
    |ψ x - x| ≤ |θ x - x| + (ψ x - θ x) := by
  convert abs_add_le (θ x - x) (ψ x - θ x) using 1
  · ring_nf
  · rw [abs_of_nonneg (sub_nonneg_of_le <| Chebyshev.theta_le_psi x)]

private lemma theta_err_simpl {x : ℝ} (hx : x ≥ exp 22) :
    0.001 * x / (log x) ^ 2 ≤ 0.001 / 22 * x / log x := by
  have hlog_pos : (0 : ℝ) < log x := by linarith [log_ge_22 hx]
  rw [div_le_div_iff₀ (pow_pos hlog_pos 2) hlog_pos]
  nlinarith [mul_le_mul_of_nonneg_right (log_ge_22 hx) hlog_pos.le, sq (log x),
    mul_pos (by linarith [exp_pos (22 : ℝ)] : (0:ℝ) < x) hlog_pos]

private lemma sqrt_err {x : ℝ} (hx : x ≥ exp 22) :
    1.001 * sqrt x ≤ 0.005 * x / log x := by
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (exp_pos _) hx
  have hlog_pos : (0 : ℝ) < log x := by linarith [log_ge_22 hx]
  rw [le_div_iff₀ hlog_pos]
  have h_sqrt : sqrt x = exp (log x / 2) := by rw [sqrt_eq_rpow, rpow_def_of_pos hx_pos]; ring_nf
  have h_taylor : exp (log x / 2) ≥ (log x / 2) ^ 8 / 40320 := by
    have h_sum := sum_le_exp_of_nonneg (show log x / 2 ≥ 0 by linarith) 9
    have h_le : (log x / 2) ^ 8 / (Nat.factorial 8) ≤
        ∑ i ∈ Finset.range 9, (log x / 2) ^ i / (Nat.factorial i) :=
      Finset.single_le_sum (f := fun i => (log x / 2) ^ i / (Nat.factorial i))
        (fun i _ => by positivity) (by decide)
    simp only [Nat.factorial] at h_le; linarith
  have h_bound : sqrt x ≥ (log x) ^ 8 / 10321920 := by
    rw [h_sqrt]; linarith [show (log x / 2) ^ 8 / 40320 = (log x) ^ 8 / 10321920 by ring]
  nlinarith [pow_le_pow_left₀ (by linarith) (log_ge_22 hx) 7, sqrt_nonneg x, sq_sqrt hx_pos.le]

private lemma cbrt_err {x : ℝ} (hx : x ≥ exp 22) :
    1.78 * x ^ (1 / 3 : ℝ) ≤ 0.001 * x / log x := by
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx
  have hlog := log_nonneg <| by linarith [add_one_le_exp 22]
  have h_rpow : x ^ (2 / 3 : ℝ) = exp (2 * log x / 3) := by rw [rpow_def_of_pos hx_pos]; ring_nf
  have h_taylor : exp (2 * log x / 3) ≥ (2 * log x / 3) ^ 8 / 40320 := by
    rw [exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] at *
    refine le_trans ?_ (Summable.sum_le_tsum (Finset.range 9)
      (fun _ _ => div_nonneg (pow_nonneg (div_nonneg (mul_nonneg zero_le_two hlog) zero_le_three) _)
      (Nat.cast_nonneg _)) (show Summable _ from summable_pow_div_factorial _))
    norm_num [Finset.sum_range_succ, Nat.factorial]; ring_nf; norm_num
    nlinarith [sq_nonneg (log x ^ 2), sq_nonneg (log x ^ 3), sq_nonneg (log x ^ 4),
      sq_nonneg (log x ^ 5), sq_nonneg (log x ^ 6), hlog]
  have h_bound : x ^ (2 / 3 : ℝ) ≥ 1780 * log x := by
    rw [h_rpow]
    nlinarith [log_exp 22, log_le_log (by positivity) hx,
      pow_nonneg hlog 2, pow_nonneg hlog 3, pow_nonneg hlog 4,
      pow_nonneg hlog 5, pow_nonneg hlog 6, pow_nonneg hlog 7]
  have h_13 : x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by norm_num [← rpow_add hx_pos]
  have h_recombine : x ≥ 1780 * x ^ (1 / 3 : ℝ) * log x := by nlinarith [rpow_pos_of_pos hx_pos (1 / 3 : ℝ)]
  rw [le_div_iff₀ (log_pos <| lt_of_lt_of_le (by norm_num) hx)]
  linarith

@[blueprint
  "thm:dusart1999-a"
  (title := "Dusart 1999, part a")
  (statement := /-- For $x \geq e^{22}$, we have $|\psi(x) - x| \leq \frac{0.006409\, x}{\log x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_a (x : ℝ) (hx : x ≥ exp 22) :
    |ψ x - x| ≤ 0.006409 * x / log x := by
  calc |ψ x - x|
      ≤ |θ x - x| + (ψ x - θ x) := psi_triangle x
    _ ≤ 0.001 * x / (log x) ^ 2 + (1.001 * sqrt x + 1.78 * x ^ (1 / 3 : ℝ)) := by
        linarith [theta_err hx, psi_theta_err <| lt_of_lt_of_le (exp_pos _) hx]
    _ ≤ 0.001 / 22 * x / log x + (0.005 * x / log x + 0.001 * x / log x) := by
        linarith [theta_err_simpl hx, sqrt_err hx, cbrt_err hx]
    _ = (0.001 / 22 + 0.005 + 0.001) * x / log x := by ring
    _ ≤ 0.006409 * x / log x := by
        apply div_le_div_of_nonneg_right _ (le_of_lt <| by linarith [log_ge_22 hx])
        apply mul_le_mul_of_nonneg_right _ (le_of_lt <| lt_of_lt_of_le (exp_pos _) hx)
        norm_num

@[blueprint
  "thm:dusart1999-b"
  (title := "Dusart 1999, part b")
  (statement := /-- For $x \geq 10{,}544{,}111$, we have $|\vartheta(x) - x| \leq \frac{0.006788\, x}{\log x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_b (x : ℝ) (hx : x ≥ 10544111) :
    |θ x - x| ≤ 0.006788 * x / log x := by sorry

@[blueprint
  "thm:dusart1999-c"
  (title := "Dusart 1999, part c")
  (statement := /-- For $x \geq 3{,}594{,}641$, we have $|\vartheta(x) - x| \leq \frac{0.2\, x}{\log^2 x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_c (x : ℝ) (hx : x ≥ 3594641) :
    |θ x - x| ≤ 0.2 * x / (log x) ^ 2 := by sorry

@[blueprint
  "thm:dusart1999-d"
  (title := "Dusart 1999, part d")
  (statement := /-- For $x > 1$, we have $|\vartheta(x) - x| \leq \frac{515\, x}{\log^3 x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_d (x : ℝ) (hx : x > 1) :
    |θ x - x| ≤ 515 * x / (log x) ^ 3 := by
  by_cases h2 : x ≥ 2
  · have hmem : (3, (20.83 : ℝ), (2 : ℝ)) ∈ Dusart.Table_4_2 := by
      unfold Dusart.Table_4_2; simp [List.mem_cons]
    have hEθ := Dusart.theorem_4_2 hmem (show x ≥ 2 from h2)
    unfold Eθ at hEθ
    have hx_pos : (0 : ℝ) < x := by linarith
    have hlog3_pos : (0 : ℝ) < (log x) ^ 3 := pow_pos (log_pos (by linarith)) 3
    rw [div_le_div_iff₀ hx_pos hlog3_pos] at hEθ
    calc |θ x - x| ≤ 20.83 * x / (log x) ^ 3 := by
            rw [le_div_iff₀ hlog3_pos]; linarith
      _ ≤ 515 * x / (log x) ^ 3 := by
          apply div_le_div_of_nonneg_right _ hlog3_pos.le; nlinarith
  · push_neg at h2
    rw [Chebyshev.theta_eq_zero_of_lt_two h2, zero_sub, abs_neg, abs_of_pos (by linarith)]
    have hlog_pos : (0 : ℝ) < log x := log_pos hx
    rw [le_div_iff₀ (pow_pos hlog_pos 3)]
    have : (log x) ^ 3 ≤ 1 := by
      calc (log x) ^ 3 ≤ (log x) ^ 1 :=
              pow_le_pow_of_le_one hlog_pos.le
                ((log_lt_iff_lt_exp (by linarith)).mpr (by nlinarith [exp_one_gt_d9])).le
                (by omega)
        _ = log x := pow_one _
        _ ≤ 1 := ((log_lt_iff_lt_exp (by linarith)).mpr
            (by nlinarith [exp_one_gt_d9])).le
    nlinarith

end Dusart1999

namespace Dusart

blueprint_comment /-- Some results from \cite{Dusart2018}-/

@[blueprint
  "thm:dusart2018-theta-improv-1"
  (title := "Dusart 2018, $\\vartheta$ improvement 1")
  (statement := /-- For $x > 1$, we have $|\vartheta(x) - x| \leq \frac{20.83\, x}{\log^3 x}$. -/)
  (latexEnv := "theorem")]
theorem theta_improv_1 (x : ℝ) (hx : x > 1) :
    |θ x - x| ≤ 20.83 * x / (log x) ^ 3 := by
  have hx_pos : x > 0 := by linarith
  have hlog_pos : log x > 0 := log_pos hx
  by_cases hx2 : x ≥ 2
  · have hEθ := Dusart.theorem_4_2
      (by simp [Dusart.Table_4_2] : ((3 : ℕ), (20.83 : ℝ), (2 : ℝ)) ∈ Dusart.Table_4_2) hx2
    simp only [Eθ] at hEθ
    rw [div_le_div_iff₀ hx_pos (pow_pos hlog_pos 3)] at hEθ
    rwa [le_div_iff₀ (pow_pos hlog_pos 3)]
  · push_neg at hx2
    have hlog2 : log 2 < 1 := by
      linarith [log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)]
    have hlog_lt1 : log x < 1 := lt_trans (log_lt_log hx_pos hx2) hlog2
    have hlog3_lt1 : (log x) ^ 3 < 1 := by
      calc (log x) ^ 3 ≤ log x := by
            nlinarith [sq_nonneg (log x), sq_nonneg (1 - log x)]
        _ < 1 := hlog_lt1
    rw [le_div_iff₀ (pow_pos hlog_pos 3)]
    have habs : |θ x - x| ≤ x := by
      rw [abs_le]; constructor
      · linarith [theta_nonneg x]
      · have : θ x ≤ log 4 * x := theta_le_log4_mul_x hx_pos.le
        have : log 4 = 2 * log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; ring
        nlinarith
    exact le_trans (mul_le_mul habs hlog3_lt1.le (pow_pos hlog_pos 3).le (by linarith))
      (by linarith)

@[blueprint
  "thm:dusart2018-theta-improv-2"
  (title := "Dusart 2018, $\\vartheta$ improvement 2")
  (statement := /-- For $x \geq 89{,}967{,}803$, we have $|\vartheta(x) - x| \leq \frac{x}{\log^3 x}$. -/)
  (latexEnv := "theorem")]
theorem theta_improv_2 (x : ℝ) (hx : x ≥ 89967803) :
    |θ x - x| ≤ x / (log x) ^ 3 := by
  have hx_pos : (0:ℝ) < x := by linarith
  have hlog_pos : (0:ℝ) < log x := log_pos (by linarith)
  have hlog3_pos : (0:ℝ) < (log x) ^ 3 := by positivity
  have hmem : (3, (1:ℝ), (89967803:ℝ)) ∈ Dusart.Table_4_2 := by
    simp [Dusart.Table_4_2]
  have hEθ := Dusart.theorem_4_2 hmem hx
  unfold Eθ at hEθ
  rw [div_le_div_iff₀ hx_pos hlog3_pos, one_mul] at hEθ
  rwa [le_div_iff₀' hlog3_pos, mul_comm]

end Dusart

namespace FaberKadiri

blueprint_comment /-- Some results from \cite{faber-kadiri}, \cite{faber-kadiri-corrigendum}-/

@[blueprint
  "thm:faber-kadiri-psi"
  (title := "Faber-Kadiri $\\psi$ bound")
  (statement := /-- For $x \geq 485{,}165{,}196$, we have $|\psi(x) - x| \leq 0.00053699\, x$. -/)
  (latexEnv := "theorem")]
theorem psi_bound (x : ℝ) (hx : x ≥ 485165196) :
    |ψ x - x| ≤ 0.00053699 * x := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hmem : (4, (59.18 : ℝ)) ∈ Dusart.Table_3_3 := by simp [Dusart.Table_3_3]
  have hEpsi := Dusart.theorem_3_3 hmem (show x ≥ 2 by linarith)
  rw [show Eψ x = |ψ x - x| / x from rfl] at hEpsi
  rw [div_le_iff₀ hx_pos] at hEpsi
  apply hEpsi.trans (mul_le_mul_of_nonneg_right _ hx_pos.le)
  have hlog : (20 : ℝ) ≤ log x := by
    rw [le_log_iff_exp_le hx_pos]
    exact (show exp 20 ≤ 485165196 from by interval_auto).trans hx
  calc (59.18 : ℝ) / (log x) ^ 4
      ≤ 59.18 / 20 ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          (pow_le_pow_left₀ (by linarith) hlog 4)
      _ ≤ 0.00053699 := by norm_num

end FaberKadiri

namespace JY

blueprint_comment /-- Some results from \cite{johnston-yang}-/

@[blueprint
  "thm:jy-psi-1"
  (title := "Johnston-Yang $\\psi$ bound 1")
  (statement := /-- For $x \geq 5000$, we have $|\psi(x) - x| \leq 8.14 \cdot 10^{-20}\, x$. -/)
  (latexEnv := "theorem")]
theorem psi_bound_1 (x : ℝ) (hx : x ≥ 5000) :
    |ψ x - x| ≤ 8.14e-20 * x := by sorry

@[blueprint
  "thm:jy-psi-2"
  (title := "Johnston-Yang $\\psi$ bound 2")
  (statement := /-- For $x \geq 2$, we have $|\psi(x) - x| \leq x \cdot 9.39\, (\log x)^{1.51} \exp(-0.8274\sqrt{\log x})$. -/)
  (latexEnv := "theorem")]
theorem psi_bound_2 (x : ℝ) (hx : x ≥ 2) :
    |ψ x - x| ≤ x * 9.39 * (log x) ^ (1.51 : ℝ) * exp (-0.8274 * sqrt (log x)) := by
  have h_exp : (log x) ^ (0.01 : ℝ) * exp (0.0202836 * sqrt (log x)) ≥ 1 := by
    by_cases h₂ : log x ≤ 1 <;> by_cases h₃ : log x ≥ 1
    · norm_num [show log x = 1 by grind] at *
    · simp_all only [ge_iff_le, not_le, rpow_def_of_pos (log_pos <| show 1 < x by grind)]
      rw [← exp_add]; norm_num; ring_nf; norm_num
      have h_log_log : log (log x) ≥ log (log 2) := log_le_log (log_pos (by norm_num)) (log_le_log (by norm_num) hx)
      have h_log_log_pos : log (log 2) > -1 / 2 := by
        rw [gt_iff_lt, div_lt_iff₀'] <;> norm_num [← log_rpow, log_lt_log]
        rw [← log_rpow, lt_log_iff_exp_lt] <;> norm_num
        · exact lt_of_le_of_lt (exp_neg_one_lt_d9.le) (by norm_num at *; nlinarith [log_two_gt_d9])
        · positivity
        · positivity
      nlinarith [sqrt_nonneg (log x), mul_self_sqrt (log_nonneg (by grind : (1 : ℝ) ≤ x)),
        log_le_sub_one_of_pos (show 0 < log x from log_pos (by grind))]
    · simp_all only [ge_iff_le, not_le, rpow_def_of_pos (log_pos <| show 1 < x by grind)]
      rw [← exp_add]
      exact one_le_exp (by nlinarith [log_pos h₂, sqrt_nonneg (log x), mul_self_sqrt (log_nonneg (by linarith))])
    · grind
  have h_ineq : |ψ x - x| ≤ x * 9.22022 * (log x) ^ (1.5 : ℝ) * exp (-0.8476836 * sqrt (log x)) := by
    have h_ineq : |ψ x - x| / x ≤ 9.22022 * (log x) ^ (3 / 2 : ℝ) * exp (-0.8476836 * sqrt (log x)) := by
      have := FKS.FKS_corollary_1_4
      convert this x hx using 1; norm_num [exp_neg, sqrt_eq_rpow, rpow_neg, div_eq_mul_inv]; ring_nf
      norm_num [admissible_bound, exp_neg, sqrt_eq_rpow, rpow_neg, div_eq_mul_inv]; ring_nf
    rw [div_le_iff₀] at h_ineq <;> ring_nf at * <;> grind
  refine le_trans h_ineq ?_
  norm_num [rpow_def_of_pos (log_pos (by grind : 1 < x))] at *
  norm_num [mul_assoc, ← exp_add] at *; ring_nf at *; norm_num at *
  exact mul_le_mul (mul_le_mul_of_nonneg_left (exp_le_exp.mpr <| by grind) <| by grind)
    (by norm_num) (by positivity) <| by positivity

@[blueprint
  "thm:jy-psi-3"
  (title := "Johnston-Yang $\\psi$ bound 3")
  (statement := /-- For $x \geq 23$, we have $|\psi(x) - x| \leq x \cdot 0.026\, (\log x)^{1.801} \exp\!\left(-0.1853\, \frac{(\log x)^{3/5}}{(\log\log x)^{1/5}}\right)$. -/)
  (latexEnv := "theorem")]
theorem psi_bound_3 (x : ℝ) (hx : x ≥ 23) :
    |ψ x - x| ≤ x * 0.026 * (log x) ^ (1.801 : ℝ) *
      exp (-0.1853 * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5)) := by sorry

end JY

namespace PT

blueprint_comment /-- Some results from \cite{PT2021}-/

@[blueprint
  "thm:pt2021-psi"
  (title := "Platt-Trudgian 2021 $\\psi$ bound")
  (statement := /-- For $x \geq e^{2000}$, we have $|\psi(x) - x| \leq x \cdot 235\, (\log x)^{0.52} \exp\!\left(-\sqrt{\frac{\log x}{5.573412}}\right)$. -/)
  (latexEnv := "theorem")]
theorem psi_bound (x : ℝ) (hx : x ≥ exp 2000) :
    |ψ x - x| ≤ x * 235 * (log x) ^ (0.52 : ℝ) * exp (-sqrt (log x / 5.573412)) := by sorry

end PT

namespace FKS

blueprint_comment /-- Some results from \cite{FKS}-/

@[blueprint
  "thm:fks-psi"
  (title := "Fiori-Kadiri-Swidinsky $\\psi$ bound")
  (statement := /-- For $x \geq 2$, we have $|\psi(x) - x| \leq x \cdot 9.22022\, (\log x)^{1.5} \exp(-0.8476836\sqrt{\log x})$. -/)
  (latexEnv := "theorem")]
theorem psi_bound (x : ℝ) (hx : x ≥ 2) :
    |ψ x - x| ≤ x * 9.22022 * (log x) ^ (1.5 : ℝ) * exp (-0.8476836 * sqrt (log x)) := by
  have h_ineq : |ψ x - x| / x ≤ 9.22022 * (log x) ^ (3 / 2 : ℝ) * exp (-0.8476836 * sqrt (log x)) := by
    have := FKS.FKS_corollary_1_4
    convert this x hx using 1; norm_num [exp_neg, sqrt_eq_rpow, rpow_neg, div_eq_mul_inv]; ring_nf
    norm_num [admissible_bound, exp_neg, sqrt_eq_rpow, rpow_neg, div_eq_mul_inv]; ring_nf
  rw [div_le_iff₀] at h_ineq <;> ring_nf at * <;> grind

end FKS


namespace Ramare2013

blueprint_comment /-- Some results from \cite{ramare2013} -/

@[blueprint
  "thm:ramare2013-vms-1a"
  (title := "Ramare 2013, von Mangoldt sum 1a")
  (statement := /-- For $x > 1$, we have $|\sum_{n \leq x} \Lambda(n)/n - \log x + \gamma| \leq 1.833 / \log^2 x$. -/)
  (latexEnv := "theorem")]
theorem von_mangoldt_sum_1a (x : ℝ) (hx : x > 1) :
    |∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n / n - log x + eulerMascheroniConstant| ≤
      1.833 / (log x) ^ 2 := by sorry

@[blueprint
  "thm:ramare2013-vms-1b"
  (title := "Ramare 2013, von Mangoldt sum 1b")
  (statement := /-- For $x \geq 1520000$, we have $|\sum_{n \leq x} \Lambda(n)/n - \log x + \gamma| \leq 0.0067 / \log x$. -/)
  (latexEnv := "theorem")]
theorem von_mangoldt_sum_1b (x : ℝ) (hx : x ≥ 1520000) :
    |∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n / n - log x + eulerMascheroniConstant| ≤
      0.0067 / log x := by sorry

@[blueprint
  "thm:ramare2013-vms-1c"
  (title := "Ramare 2013, von Mangoldt sum 1c")
  (statement := /-- For $x \geq 468000$, we have $|\sum_{n \leq x} \Lambda(n)/n - \log x + \gamma| \leq 0.01 / \log x$. -/)
  (latexEnv := "theorem")]
theorem von_mangoldt_sum_1c (x : ℝ) (hx : x ≥ 468000) :
    |∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n / n - log x + eulerMascheroniConstant| ≤
      0.01 / log x := by sorry

@[blueprint
  "thm:ramare2013-vms-1d"
  (title := "Ramare 2013, von Mangoldt sum 1d")
  (statement := /-- For $1 \leq x \leq 10^{10}$, we have $|\sum_{n \leq x} \Lambda(n)/n - \log x + \gamma| \leq 1.31 / \sqrt{x}$. -/)
  (latexEnv := "theorem")]
theorem von_mangoldt_sum_1d (x : ℝ) (hx1 : x ≥ 1) (hx2 : x ≤ (10 : ℝ) ^ 10) :
    |∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n / n - log x + eulerMascheroniConstant| ≤
      1.31 / sqrt x := by sorry

@[blueprint
  "thm:ramare2013-vms-2"
  (title := "Ramare 2013, von Mangoldt sum 2")
  (statement := /-- For $x \geq 8950$, there exists $E$ with $\sum_{n \leq x} \Lambda(n)/n = \log x - \gamma + (\psi(x) - x)/x + E$ and $|E| \leq 1/(2\sqrt{x}) + 1.75 \cdot 10^{-12}$. -/)
  (latexEnv := "theorem")]
theorem von_mangoldt_sum_2 (x : ℝ) (hx : x ≥ 8950) :
    ∃ E, ∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n / n =
        log x - eulerMascheroniConstant + (ψ x - x) / x + E ∧
      |E| ≤ 1 / (2 * sqrt x) + 1.75e-12 := by sorry

end Ramare2013

namespace Mawia

blueprint_comment /-- Some results from \cite{mawia} -/

@[blueprint
  "thm:mawia-spi-a"
  (title := "Mawia 2017, prime reciprocal sum a")
  (statement := /-- For $x \geq 2$, we have $|\sum_{p \leq x} 1/p - \log \log x - B| \leq 4 / \log^3 x$, where $B$ is the Meissel-Mertens constant. -/)
  (latexEnv := "theorem")]
theorem sum_p_inv_a (x : ℝ) (hx : x ≥ 2) :
    |∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 / (p : ℝ)) -
        log (log x) - meisselMertensConstant| ≤ 4 / (log x) ^ 3 := by sorry

@[blueprint
  "thm:mawia-spi-b"
  (title := "Mawia 2017, prime reciprocal sum b")
  (statement := /-- For $x \geq 1000$, we have $|\sum_{p \leq x} 1/p - \log \log x - B| \leq 2.3 / \log^3 x$. -/)
  (latexEnv := "theorem")]
theorem sum_p_inv_b (x : ℝ) (hx : x ≥ 1000) :
    |∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 / (p : ℝ)) -
        log (log x) - meisselMertensConstant| ≤ 2.3 / (log x) ^ 3 := by sorry

@[blueprint
  "thm:mawia-spi-c"
  (title := "Mawia 2017, prime reciprocal sum c")
  (statement := /-- For $x \geq 24284$, we have $|\sum_{p \leq x} 1/p - \log \log x - B| \leq 1 / \log^3 x$. -/)
  (latexEnv := "theorem")]
theorem sum_p_inv_c (x : ℝ) (hx : x ≥ 24284) :
    |∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 / (p : ℝ)) -
        log (log x) - meisselMertensConstant| ≤ 1 / (log x) ^ 3 := by sorry

@[blueprint
  "thm:mawia-spi-d"
  (title := "Mawia 2017, prime reciprocal sum d")
  (statement := /-- For $\log x \geq 4635$, we have $|\sum_{p \leq x} 1/p - \log \log x - B| \leq 1.1 \exp(-\sqrt{0.175 \log x}) / (\log x)^{3/4}$. -/)
  (latexEnv := "theorem")]
theorem sum_p_inv_d (x : ℝ) (hx : log x ≥ 4635) :
    |∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (1 / (p : ℝ)) -
        log (log x) - meisselMertensConstant| ≤
      1.1 * exp (-sqrt (0.175 * log x)) / (log x) ^ ((3 : ℝ) / 4) := by sorry

end Mawia

namespace Ramare2016

blueprint_comment /-- Some results from \cite{ramare2016} -/

/-- Predicate for Ramaré 2016 Lemma 3.2: the weighted prime sum bound holds with threshold
    $P_0$, error $\varepsilon$, and last-term constant $c$. For any $P \geq P_0$ and
    $C^1$ non-negative non-increasing $f$ on $[P,\infty)$ with $\lim_{t	\to \infty} tf(t)=0$,
    $\sum_{p \geq P} f(p)\log p \leq (1+\varepsilon)\int_P^\infty f\,dt
    + \varepsilon P f(P) + c P f(P)/\log^2 P$. -/
def lemma_3_2_bound (ε c P₀ : ℝ) : Prop :=
  ∀ (P : ℝ) (f : ℝ → ℝ),
    P₀ ≤ P →
    (∀ t, P ≤ t → 0 ≤ f t) →
    AntitoneOn f (Set.Ici P) →
    ContDiffOn ℝ 1 f (Set.Ici P) →
    Filter.Tendsto (fun t ↦ t * f t) Filter.atTop (nhds 0) →
    ∑' p : ℕ, (if Nat.Prime p ∧ P ≤ (p : ℝ) then f p * log p else 0) ≤
      (1 + ε) * ∫ t in Set.Ici P, f t +
      ε * P * f P +
      c * P * f P / (log P) ^ 2

@[blueprint
  "thm:ramare2016-3-2-a"
  (title := "Ramar\\'e 2016 Lemma 3.2a")
  (statement := /-- For $P \geq 3{,}600{,}000$ with $\varepsilon = 1/914$ and last-term constant $1/5$:
  for any $C^1$ non-negative non-increasing $f$ on $[P,\infty)$ with $\lim_{t	\to \infty} tf(t)=0$,
  $\sum_{p \geq P} f(p)\log p \leq (1+\frac{1}{914})\int_P^\infty f + \frac{Pf(P)}{914} + \frac{Pf(P)}{5\log^2 P}$. -/)
  (latexEnv := "theorem")]
theorem lemma_3_2_a : lemma_3_2_bound (1/914) (1/5) 3600000 := by sorry

@[blueprint
  "thm:ramare2016-3-2-b"
  (title := "Ramar\\'e 2016 Lemma 3.2b")
  (statement := /-- For $P \geq 2$ with $\varepsilon = 1/914$ and last-term constant $4$:
  for any $C^1$ non-negative non-increasing $f$ on $[P,\infty)$ with $\lim_{t	\to \infty} tf(t)=0$,
  $\sum_{p \geq P} f(p)\log p \leq (1+\frac{1}{914})\int_P^\infty f + \frac{Pf(P)}{914} + \frac{4Pf(P)}{\log^2 P}$. -/)
  (latexEnv := "theorem")]
theorem lemma_3_2_b : lemma_3_2_bound (1/914) 4 2 := by sorry

@[blueprint
  "thm:ramare2016-3-2-c"
  (title := "Ramar\\'e 2016 Lemma 3.2c (via Dusart 2016)")
  (statement := /-- For $P \geq 3{,}600{,}000$ using Dusart 2016, with $\varepsilon = 1/36260$ and last-term constant $1/5$:
  for any $C^1$ non-negative non-increasing $f$ on $[P,\infty)$ with $\lim_{t	\to \infty} tf(t)=0$,
  $\sum_{p \geq P} f(p)\log p \leq (1+\frac{1}{36260})\int_P^\infty f + \frac{Pf(P)}{36260} + \frac{Pf(P)}{5\log^2 P}$. -/)
  (latexEnv := "theorem")]
theorem lemma_3_2_c : lemma_3_2_bound (1/36260) (1/5) 3600000 := by sorry

end Ramare2016

namespace Trevino

blueprint_comment /-- Some results from \cite{trevino} -/

/-- Table of threshold $x_0$ and constants $c_1$, $c_2$ for the sum-of-primes bounds. -/
def Table_1 : List (ℝ × ℝ × ℝ) :=
  [ (315437,   0.205448, 0.330479),
    (468577,   0.211359, 0.32593),
    (486377,   0.212904, 0.325537),
    (644123,   0.21429,  0.322609),
    (678407,   0.214931, 0.322326),
    (758231,   0.215541, 0.321504),
    (758711,   0.215939, 0.321489),
    (10544111, 0.239818, 0.29251) ]

@[blueprint
  "thm:trevino-sum-prime"
  (title := "Trevi\\~no 2012, sum of primes")
  (statement := /-- For each row $(x_0, c_1, c_2)$ from Table 1, for all $x \geq x_0$:
  $$\frac{x^2}{2\log x} + \frac{c_1 x^2}{\log^2 x} \leq \sum_{p \leq x} p \leq
    \frac{x^2}{2\log x} + \frac{c_2 x^2}{\log^2 x}.$$ -/)
  (latexEnv := "theorem")]
theorem sum_prime_bound (x₀ c₁ c₂ : ℝ) (hrow : (x₀, c₁, c₂) ∈ Table_1)
    (x : ℝ) (hx : x ≥ x₀) :
    x ^ 2 / (2 * log x) + c₁ * x ^ 2 / (log x) ^ 2 ≤
      ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (p : ℝ) ∧
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (p : ℝ) ≤
      x ^ 2 / (2 * log x) + c₂ * x ^ 2 / (log x) ^ 2 := by sorry

end Trevino

namespace DelegliseNicolas

blueprint_comment /-- Some results from \cite{deleglise-nicolas} -/

/-- The sum of $r$-th powers of primes up to $x$. -/
noncomputable def pi_r (r : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (p : ℝ) ^ r

@[blueprint
  "thm:dn-pi1-lower"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_1$ lower bound")
  (statement := /-- For $x \geq 905{,}238{,}547$,
  $\frac{3x^2}{20\log^4 x} \leq \pi_1(x) - \left(\frac{x^2}{2\log x} + \frac{x^2}{4\log^2 x} + \frac{x^2}{4\log^3 x}\right)$. -/)
  (latexEnv := "theorem")]
theorem theorem_a (x : ℝ) (hx : x ≥ 905238547) :
    3 * x ^ 2 / (20 * (log x) ^ 4) ≤
      pi_r 1 x - (x ^ 2 / (2 * log x) + x ^ 2 / (4 * (log x) ^ 2) +
        x ^ 2 / (4 * (log x) ^ 3)) := by sorry

@[blueprint
  "thm:dn-pi1-upper"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_1$ upper bound")
  (statement := /-- For $x \geq 110{,}117{,}910$,
  $\pi_1(x) - \left(\frac{x^2}{2\log x} + \frac{x^2}{4\log^2 x} + \frac{x^2}{4\log^3 x}\right) \leq \frac{107 x^2}{160\log^4 x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_b (x : ℝ) (hx : x ≥ 110117910) :
    pi_r 1 x - (x ^ 2 / (2 * log x) + x ^ 2 / (4 * (log x) ^ 2) +
        x ^ 2 / (4 * (log x) ^ 3)) ≤
      107 * x ^ 2 / (160 * (log x) ^ 4) := by sorry

@[blueprint
  "thm:dn-pi2-lower"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_2$ lower bound")
  (statement := /-- For $x \geq 1{,}091{,}239$,
  $-\frac{1069\, x^3}{648\log^4 x} \leq \pi_2(x) - \left(\frac{x^3}{3\log x} + \frac{x^3}{9\log^2 x} + \frac{x^3}{27\log^3 x}\right)$. -/)
  (latexEnv := "theorem")]
theorem theorem_c (x : ℝ) (hx : x ≥ 1091239) :
    -(1069 * x ^ 3 / (648 * (log x) ^ 4)) ≤
      pi_r 2 x - (x ^ 3 / (3 * log x) + x ^ 3 / (9 * (log x) ^ 2) +
        x ^ 3 / (27 * (log x) ^ 3)) := by sorry

@[blueprint
  "thm:dn-pi2-upper"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_2$ upper bound")
  (statement := /-- For $x \geq 60{,}173$,
  $\pi_2(x) - \left(\frac{x^3}{3\log x} + \frac{x^3}{9\log^2 x} + \frac{x^3}{27\log^3 x}\right) \leq \frac{11181\, x^3}{648\log^4 x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_d (x : ℝ) (hx : x ≥ 60173) :
    pi_r 2 x - (x ^ 3 / (3 * log x) + x ^ 3 / (9 * (log x) ^ 2) +
        x ^ 3 / (27 * (log x) ^ 3)) ≤
      11181 * x ^ 3 / (648 * (log x) ^ 4) := by sorry

@[blueprint
  "thm:dn-pi3-upper"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_3$ upper bound")
  (statement := /-- For $x \geq 664$, $\pi_3(x) \leq 0.271\, x^4 / \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_e (x : ℝ) (hx : x ≥ 664) :
    pi_r 3 x ≤ 0.271 * x ^ 4 / log x := by sorry

@[blueprint
  "thm:dn-pi4-upper"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_4$ upper bound")
  (statement := /-- For $x \geq 200$, $\pi_4(x) \leq 0.237\, x^5 / \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_f (x : ℝ) (hx : x ≥ 200) :
    pi_r 4 x ≤ 0.237 * x ^ 5 / log x := by sorry

@[blueprint
  "thm:dn-pi5-upper"
  (title := "Del\\'eglise-Nicolas 2019, $\\pi_5$ upper bound")
  (statement := /-- For $x \geq 44$, $\pi_5(x) \leq 0.226\, x^6 / \log x$.
  (Note: the wiki page lists $x^5$ here, but the consistent pattern $x^{r+1}$ and the general bound require $x^6$.) -/)
  (latexEnv := "theorem")]
theorem theorem_g (x : ℝ) (hx : x ≥ 44) :
    pi_r 5 x ≤ 0.226 * x ^ 6 / log x := by sorry

@[blueprint
  "thm:dn-pir-general"
  (title := "Del\\'eglise-Nicolas 2019, general $\\pi_r$ upper bound")
  (statement := /-- For $x \geq 1$ and $r \geq 5$,
  $\pi_r(x) \leq \frac{\log 3}{3} \cdot \left(1 + \left(\frac{2}{3}\right)^r\right) \cdot \frac{x^{r+1}}{\log x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_h (r : ℕ) (hr : r ≥ 5) (x : ℝ) (hx : x ≥ 1) :
    pi_r r x ≤ log 3 / 3 * (1 + (2 / 3 : ℝ) ^ r) * x ^ (r + 1) / log x := by sorry

end DelegliseNicolas

namespace Rosser1938

/- NOTE FOR CLAUDE: use `nth_prime'` rather than `nth_prime` to have the primes indexed from 1 -/

blueprint_comment /-- Some results from \cite{rosser1938} -/

@[blueprint
  "thm:rosser1938-pn-gt-nlogn"
  (title := "Rosser 1938, $p_n > n \\log n$")
  (statement := /-- For $n \geq 2$, we have $p_n > n \log n$. -/)
  (latexEnv := "theorem")]
theorem p_n_gt_1 (n : ℕ) (hn : n ≥ 2) :
    nth_prime' n > n * log n := by
  by_cases h : n ≤ 31
  · have key : ∀ (n₀ m : ℕ), Nat.count Nat.Prime m ≤ n₀ - 1 → (n₀ : ℝ) * log n₀ < m →
        (nth_prime' n₀ : ℝ) > n₀ * log n₀ :=
      fun n₀ m hc hb => hb.trans_le (by exact_mod_cast RS_prime_helper.count_prime_le_imp_le_nth m (n₀ - 1) hc)
    interval_cases n
    · exact key 2 3 count_prime_3_le_1 (by interval_auto)
    · exact key 3 5 count_prime_5_le_2 (by interval_auto)
    · exact key 4 7 count_prime_7_le_3 (by interval_auto)
    · exact key 5 11 count_prime_11_le_4 (by interval_auto)
    · exact key 6 13 count_prime_13_le_5 (by interval_auto)
    · exact key 7 17 count_prime_17_le_6 (by interval_auto)
    · exact key 8 19 count_prime_19_le_7 (by interval_auto)
    · exact key 9 23 count_prime_23_le_8 (by interval_auto)
    · exact key 10 29 count_prime_29_le_9 (by interval_auto)
    · exact key 11 31 count_prime_31_le_10 (by interval_auto)
    · exact key 12 37 count_prime_37_le_11 (by interval_auto)
    · exact key 13 41 count_prime_41_le_12 (by interval_auto)
    · exact key 14 43 count_prime_43_le_13 (by interval_auto)
    · exact key 15 47 count_prime_47_le_14 (by interval_auto)
    · exact key 16 53 count_prime_53_le_15 (by interval_auto)
    · exact key 17 59 count_prime_59_le_16 (by interval_auto)
    · exact key 18 61 count_prime_61_le_17 (by interval_auto)
    · exact key 19 67 count_prime_67_le_18 (by interval_auto)
    · exact key 20 71 count_prime_71_le_19 (by interval_auto)
    · exact key 21 73 count_prime_73_le_20 (by interval_auto)
    · exact key 22 79 count_prime_79_le_21 (by interval_auto)
    · exact key 23 83 count_prime_83_le_22 (by interval_auto)
    · exact key 24 89 count_prime_89_le_23 (by interval_auto)
    · exact key 25 97 count_prime_97_le_24 (by interval_auto)
    · exact key 26 101 count_prime_101_le_25 (by interval_auto)
    · exact key 27 103 count_prime_103_le_26 (by interval_auto)
    · exact key 28 107 count_prime_107_le_27 (by interval_auto)
    · exact key 29 109 count_prime_109_le_28 (by interval_auto)
    · exact key 30 113 count_prime_113_le_29 (by interval_auto)
    · exact key 31 127 count_prime_127_le_30 (by interval_auto)
  · push_neg at h
    have h_pn_ge_succ : nth_prime' n ≥ n + 1 := by
      have : ∀ n ≥ 1, nth_prime' n ≥ n + 1 := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => exact Nat.Prime.two_le (Nat.prime_nth_prime 0) |> Nat.succ_le_of_lt
        | succ n _ ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.pred_lt (by positivity))))
      exact this n (by omega)
    have h_dusart : (nth_prime' n : ℝ) ≥ n * (log (nth_prime' n) - 1.112) := by
      have h_pi_le : (n : ℝ) ≤ (nth_prime' n : ℝ) / (log (nth_prime' n) - 1.112) := by
        have h_pi_le' : pi (nth_prime' n) ≤ (nth_prime' n : ℝ) / (log (nth_prime' n) - 1.112) := by
          convert Dusart.corollary_5_3_b _ using 1
          linarith [show (n : ℝ) ≥ 32 by norm_cast, show exp 1.112 < 3.041 from LogTables.exp_1_112_lt,
            show (nth_prime' n : ℝ) ≥ n + 1 by norm_cast]
        convert h_pi_le' using 1
        exact_mod_cast Eq.symm (RS_prime_helper.pi_nth_prime' n (by omega))
      rwa [le_div_iff₀ (sub_pos.mpr <| by
        contrapose! h_pi_le
        exact lt_of_le_of_lt
          (div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr h_pi_le))
          (by positivity))] at h_pi_le
    have h_pn_ge_n : (nth_prime' n : ℝ) ≥ n := by linarith [show (nth_prime' n : ℝ) ≥ n + 1 by norm_cast]
    have h_log_pn_ge : log (nth_prime' n) ≥ log n :=
      log_le_log (by positivity) h_pn_ge_n
    have h_pn_ge1 : (nth_prime' n : ℝ) ≥ n * (log n - 1.112) :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) h_dusart
    have h_log_diff : log (log n - 1.112) > 0.855 := by
      have : log n ≥ log 32 := log_le_log (by norm_num) (by norm_cast)
      have : log n > 3.465 := by linarith [LogTables.log_32_gt]
      exact lt_of_lt_of_le LogTables.log_2_353_gt (log_le_log (by norm_num) (by linarith))
    have h_log_n_minus_pos : log n - 1.112 > 0 := by
      have : log n ≥ log 32 := log_le_log (by norm_num) (by norm_cast)
      linarith [LogTables.log_32_gt]
    have h_log_pn2 : log (nth_prime' n) ≥ log n + log (log n - 1.112) := by
      rw [← log_mul (ne_of_gt (by positivity : (0 : ℝ) < n)) (ne_of_gt h_log_n_minus_pos)]
      exact log_le_log (by positivity) h_pn_ge1
    have h_pn_ge2 : (nth_prime' n : ℝ) ≥ n * (log n - 0.262) := by
      have : (nth_prime' n : ℝ) ≥ n * (log n + 0.855 - 1.112) :=
        le_trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) h_dusart
      linarith
    have h_pn_ge3 : (nth_prime' n : ℝ) ≥ n * 3.2 := by
      have : log n ≥ log 32 := log_le_log (by norm_num) (by norm_cast)
      nlinarith [LogTables.log_32_gt]
    have h_log_pn3 : log (nth_prime' n) > log n + 1.16 := by
      have : log (nth_prime' n) ≥ log (n * 3.2) :=
        log_le_log (by positivity) h_pn_ge3
      have : log (n * 3.2) = log n + log 3.2 :=
        log_mul (ne_of_gt (by positivity)) (by norm_num)
      linarith [LogTables.log_3_2_gt]
    have : (nth_prime' n : ℝ) ≥ n * (log n + 1.16 - 1.112) :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) h_dusart
    nlinarith [show (n : ℝ) > 0 from by positivity]

@[blueprint
  "thm:rosser1938-pn-lower"
  (title := "Rosser 1938, lower bound on $p_n$")
  (statement := /-- For $n > 1$, we have $p_n > n(\log n + \log\log n - 10)$. -/)
  (latexEnv := "theorem")]
theorem p_n_gt_2 (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 10) := by
  have h_rs : (nth_prime' n : ℝ) > n * (log n + log (log n) - 3 / 2) := by
    by_cases h : n ≤ 31
    · exact RS_prime_helper.p_n_lower_small n hn h
    · exact RS_prime_helper.p_n_lower_large n (by omega)
  nlinarith [show (n : ℝ) > 0 from by positivity]

@[blueprint
  "thm:rosser1938-pn-upper"
  (title := "Rosser 1938, upper bound on $p_n$")
  (statement := /-- For $n > 1$, we have $p_n < n(\log n + \log\log n + 8)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lt_2 (n : ℕ) (hn : n > 1) :
    nth_prime' n < n * (log n + log (log n) + 8) := by sorry

end Rosser1938

namespace Cipolla

blueprint_comment /-- Some results from \cite{cippola} -/

@[blueprint
  "thm:cipolla-pn-asym"
  (title := "Cipolla asymptotic expansion for $p_n$")
  (statement := /-- The $n$-th prime satisfies
  $p_n = n\!\left(\log n + \log\log n - 1 + \frac{\log\log n - 2}{\log n} -
  \frac{(\log\log n)^2 - 6\log\log n + 11}{2\log^2 n} + \cdots\right)$;
  more precisely, the error
  $p_n - n\!\left(\log n + \log\log n - 1 + \frac{\log\log n - 2}{\log n} -
  \frac{(\log\log n)^2 - 6\log\log n + 11}{2\log^2 n}\right)$
  is $o(n / \log^2 n)$. -/)
  (latexEnv := "theorem")]
theorem p_n_asym :
    (fun n : ℕ => (nth_prime' n : ℝ) - n * (log n + log (log n) - 1 +
        (log (log n) - 2) / log n -
        ((log (log n)) ^ 2 - 6 * log (log n) + 11) / (2 * (log n) ^ 2))) =o[Filter.atTop]
    (fun n : ℕ => (n : ℝ) / (log n) ^ 2) := by sorry

end Cipolla

namespace Rosser1941

blueprint_comment /-- Some results from \cite{rosser1941} -/

@[blueprint
  "thm:rosser1941-pn-lower"
  (title := "Rosser 1941, lower bound on $p_n$")
  (statement := /-- For $n \geq 55$, we have $p_n > n(\log n + \log\log n - 4)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n ≥ 55) :
    nth_prime' n > n * (log n + log (log n) - 4) := by
  have h_rs : (nth_prime' n : ℝ) > n * (log n + log (log n) - 3 / 2) := by
    by_cases h : n ≤ 31
    · exact RS_prime_helper.p_n_lower_small n (by omega) h
    · exact RS_prime_helper.p_n_lower_large n (by omega)
  nlinarith [show (n : ℝ) > 0 from by positivity]

@[blueprint
  "thm:rosser1941-pn-upper"
  (title := "Rosser 1941, upper bound on $p_n$")
  (statement := /-- For $n \geq 1$, we have $p_n < n(\log n + \log\log n + 2)$. -/)
  (latexEnv := "theorem")]
theorem p_n_upper (n : ℕ) (hn : n ≥ 55) :
    nth_prime' n < n * (log n + log (log n) + 2) := by sorry

end Rosser1941


namespace RS_prime

blueprint_comment /-- Some results from \cite{rs-prime} -/

@[blueprint
  "thm:rs-1962-pn-lower"
  (title := "Rosser-Schoenfeld 1962, lower bound on $p_n$")
  (statement := /-- For $n > 1$, we have $p_n > n(\log n + \log\log n - 3/2)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 3 / 2) := by
  by_cases h : n ≤ 31
  · exact RS_prime_helper.p_n_lower_small n hn h
  · exact RS_prime_helper.p_n_lower_large n (by omega)

@[blueprint
  "thm:rs-1962-pn-upper"
  (title := "Rosser-Schoenfeld 1962, upper bound on $p_n$")
  (statement := /-- For $n > 19$, we have $p_n < n(\log n + \log\log n - 1/2)$. -/)
  (latexEnv := "theorem")]
theorem p_n_upper (n : ℕ) (hn : n > 19) :
    nth_prime' n < n * (log n + log (log n) - 1 / 2) := by sorry

end RS_prime

namespace Robin

blueprint_comment /-- Some results from \cite{robin} -/

@[blueprint
  "thm:robin1983-pn-lower"
  (title := "Robin 1983, lower bound on $p_n$")
  (statement := /-- For $n > 1$, we have $p_n > n(\log n + \log\log n - 1.0072629)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 1.0072629) := by sorry

@[blueprint
  "thm:robin1983-pn-lower-const1"
  (title := "Robin 1983, lower bound on $p_n$ with constant 1 for small primes")
  (statement := /-- For $p_n \leq 10^{11}$, we have $p_n > n(\log n + \log\log n - 1)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower_const1 (n : ℕ) (hn : (nth_prime' n : ℝ) ≤ (10 : ℝ) ^ 11) :
    nth_prime' n > n * (log n + log (log n) - 1) := by sorry

end Robin

namespace MassiasRobin

blueprint_comment /-- Some results from \cite{massias-robin} -/

@[blueprint
  "thm:massias-robin1996-pn-lower"
  (title := "Massias-Robin 1996, lower bound on $p_n$ with constant 1")
  (statement := /-- If $p_n < e^{598}$ or $p_n > e^{1800}$, then
  $p_n > n(\log n + \log\log n - 1)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ)
    (hn : (nth_prime' n : ℝ) < exp 598 ∨ (nth_prime' n : ℝ) > exp 1800) :
    nth_prime' n > n * (log n + log (log n) - 1) := by sorry

end MassiasRobin

namespace Dusart1999

blueprint_comment /-- Some results from \cite{Dusart1999} -/

@[blueprint
  "thm:dusart1999-pn-lower"
  (title := "Dusart 1999, lower bound on $p_n$")
  (statement := /-- For all $n > 1$, we have $p_n > n(\log n + \log\log n - 1)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 1) := by sorry

@[blueprint
  "thm:dusart1999-pn-upper"
  (title := "Dusart 1999, upper bound on $p_n$")
  (statement := /-- For $n > 39017$ (i.e., $p_n > 467473$), we have
  $p_n < n(\log n + \log\log n - 0.9484)$. -/)
  (latexEnv := "theorem")]
theorem p_n_upper (n : ℕ) (hn : n > 39017) :
    nth_prime' n < n * (log n + log (log n) - 0.9484) := by sorry

end Dusart1999

namespace CMS

blueprint_comment  /-- Some results from \cite{CMS2019} -/

@[blueprint
  "thm:cms2019-prime-gap"
  (title := "Carneiro-Milinovich-Soundararajan 2019, prime gap under RH")
  (statement := /-- Under the Riemann Hypothesis, for all $n \geq 3$, we have
  $p_{n+1} - p_n \leq \frac{22}{25}\sqrt{p_n}\log p_n$. -/)
  (latexEnv := "theorem")]
theorem prime_gap (n : ℕ) (hn : n ≥ 3) (RH : RiemannHypothesis) :
    (nth_prime' (n + 1) : ℝ) - nth_prime' n ≤
      22 / 25 * sqrt (nth_prime' n) * log (nth_prime' n) := by sorry

end CMS


namespace Axler

blueprint_comment /-- Some results from \cite{Axler} -/

@[blueprint
  "thm:axler2019-sum-prime-lower"
  (title := "Axler 2019, lower bound for sum of first k primes")
  (statement := /-- For $k \geq 6{,}309{,}751$, we have
  $\sum_{i \leq k} p_i \geq \frac{k^2}{4} + \frac{k^2}{4\log k} -
  \frac{k^2(\log\log k - 2.9)}{4(\log k)^2}$. -/)
  (latexEnv := "theorem")]
theorem sum_prime_lower (k : ℕ) (hk : k ≥ 6309751) :
    ∑ i ∈ Finset.Icc 1 k, (nth_prime' i : ℝ) ≥
      (k : ℝ) ^ 2 / 4 + (k : ℝ) ^ 2 / (4 * log k) -
      (k : ℝ) ^ 2 * (log (log k) - 2.9) / (4 * (log k) ^ 2) := by sorry

@[blueprint
  "thm:axler2019-sum-prime-upper"
  (title := "Axler 2019, upper bound for sum of first k primes")
  (statement := /-- For $k \geq 256{,}376$, we have
  $\sum_{i \leq k} p_i \leq \frac{k^2}{4} + \frac{k^2}{4\log k} -
  \frac{k^2(\log\log k - 4.42)}{4(\log k)^2}$. -/)
  (latexEnv := "theorem")]
theorem sum_prime_upper (k : ℕ) (hk : k ≥ 256376) :
    ∑ i ∈ Finset.Icc 1 k, (nth_prime' i : ℝ) ≤
      (k : ℝ) ^ 2 / 4 + (k : ℝ) ^ 2 / (4 * log k) -
      (k : ℝ) ^ 2 * (log (log k) - 4.42) / (4 * (log k) ^ 2) := by sorry

end Axler

namespace DeKoninckLetendre

blueprint_comment /-- Some results from \cite{DeKoninckLetendre} -/

@[blueprint
  "thm:dekoninck-letendre2020-sum-log-prime"
  (title := "DeKoninck-Letendre 2020, upper bound for sum of $\\log p_i$")
  (statement := /-- For $k \geq 5$, we have
  $\sum_{i \leq k} \log p_i \leq k(\log k + \log\log k - 1/2)$. -/)
  (latexEnv := "theorem")]
theorem sum_log_prime (k : ℕ) (hk : k ≥ 5) :
    ∑ i ∈ Finset.Icc 1 k, log (nth_prime' i : ℝ) ≤
      k * (log k + log (log k) - 1 / 2) := by sorry

@[blueprint
  "thm:dekoninck-letendre2020-sum-loglog-prime"
  (title := "DeKoninck-Letendre 2020, lower bound for sum of $\\log \\log p_i$")
  (statement := /-- For $k \geq 6$, we have
  $\sum_{i \leq k} \log\log p_i \geq k\!\left(\log\log k +
  \frac{\log\log k - 3/2}{\log k}\right)$. -/)
  (latexEnv := "theorem")]
theorem sum_loglog_prime (k : ℕ) (hk : k ≥ 6) :
    ∑ i ∈ Finset.Icc 1 k, log (log (nth_prime' i : ℝ)) ≥
      k * (log (log k) + (log (log k) - 3 / 2) / log k) := by sorry

end DeKoninckLetendre

blueprint_comment /--
\subsection{Short intervals containing primes}

The results below are taken from https://archimede.pages.math.cnrs.fr/tme-emt-wiki/Art09.html -/
namespace Schoenfeld1976

@[blueprint
  "thm:schoenfeld1976"
  (title := "Schoenfeld 1976")
  (statement := /--
  If $x > 2010760$, then there is a prime in the interval
  \[
  \left( x, x\left(1 + \frac{1}{15697}\right) \right].
  \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > 2010760) :
    HasPrimeInInterval x (x * (1 / 15697)) := by sorry

end Schoenfeld1976

namespace RamareSaouter2003

@[blueprint
  "thm:ramare-saouter2003"
  (title := "Ramar\\'e-Saouter 2003")
  (statement := /--
  If $x > 10,726,905,041$, then there is a prime in the interval $(x(1-1/28314000), x]$.
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > 10726905041) :
    HasPrimeInInterval (x*(1-1/28314000)) (x/28314000) := by sorry

end RamareSaouter2003

namespace GourdonDemichel2004

@[blueprint
  "thm:gourdon-demichel2004"
  (title := "Gourdon-Demichel 2004")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{14500755538}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/14500755538)) (x/14500755538) := by sorry

end GourdonDemichel2004

namespace PrimeGaps2014

@[blueprint
  "thm:prime_gaps_2014"
  (title := "Prime Gaps 2014")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{1966196911}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/1966196911)) (x/1966196911) := by
  obtain ⟨p, hp, hlo, hhi⟩ := GourdonDemichel2004.has_prime_in_interval x hx
  exact ⟨p, hp, by nlinarith [exp_pos 60], by nlinarith⟩

end PrimeGaps2014

namespace PrimeGaps2024

@[blueprint
  "thm:prime_gaps_2024"
  (title := "Prime Gaps 2024")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{76900000000}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/76900000000)) (x/76900000000) := by
  set y := x * (1 - 1 / 76900000000) with hy_def
  have hx_pos : x > 0 := lt_trans (exp_pos 60) hx
  have hx_ge1 : x ≥ 1 := by linarith [one_le_exp (show (0:ℝ) ≤ 60 by norm_num)]
  have hsqrt_bound : √x > exp 30 := by
    rw [sqrt_eq_rpow, show exp 30 = (exp 60) ^ ((1:ℝ)/2) from by rw [← exp_mul]; norm_num]
    exact rpow_lt_rpow (le_of_lt (exp_pos 60)) hx (by norm_num)
  have hexp30 : exp 30 > 230700000000 := by
    rw [show (30:ℝ) = (30:ℕ) * 1 from by norm_num, exp_nat_mul]
    linarith [show (2.718:ℝ) ^ 30 > 230700000000 from by norm_num,
      show (2.718:ℝ) ^ 30 ≤ (exp 1) ^ 30 from by gcongr; linarith [exp_one_gt_d9]]
  have hsqx : √x * √x = x := mul_self_sqrt (le_of_lt hx_pos)
  have h3sqrt : 3 * √x < x / 76900000000 := by nlinarith
  have hcbrt : x ^ (1/3 : ℝ) ≤ √x := by
    rw [sqrt_eq_rpow]; exact rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num)
  have hy_pos : y > 0 := by rw [hy_def]; nlinarith
  have hy_lt_x : y < x := by rw [hy_def]; nlinarith
  have hy_ge5000 : y ≥ 5000 := by
    rw [hy_def]
    have : exp 60 ≥ 5001 := by
      rw [show (60:ℝ) = (60:ℕ) * 1 from by norm_num, exp_nat_mul]
      linarith [show (2.718:ℝ) ^ 60 > 5001 from by norm_num,
        show (2.718:ℝ) ^ 60 ≤ (exp 1) ^ 60 from by gcongr; linarith [exp_one_gt_d9]]
    nlinarith
  have hθy : θ y ≤ y + 8.14e-20 * y := by
    linarith [theta_le_psi y,
      show ψ y ≤ y + 8.14e-20 * y from by
        have h := JY.psi_bound_1 y hy_ge5000; rw [abs_le] at h; linarith]
  have hψx : ψ x ≥ x - 8.14e-20 * x := by
    have h := JY.psi_bound_1 x (by linarith : x ≥ 5000); rw [abs_le] at h; linarith
  have hψθ := Dusart.corollary_4_5 hx_pos
  have key : x / 76900000000 = x - y := by rw [hy_def]; ring
  rw [key]
  exact theta_pos_implies_prime_in_interval hy_lt_x (by nlinarith [show √x > 0 from by positivity])

end PrimeGaps2024

namespace Axler2018

@[blueprint
  "thm:axler2018_1"
  (title := "Axler 2018 Theorem 1.4(1)")
  (statement := /-- If $x ≥ 6034256$, then there
  is a prime in the interval
  \[ \left( x, x\left(1 + \frac{0.087}{\log^3 x}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval_1 (x : ℝ) (hx : x ≥ 6034256) :
    HasPrimeInInterval x (x * (0.087 / (log x) ^ 3)) := by sorry

@[blueprint
  "thm:axler2018_2"
  (title := "Axler 2018 Theorem 1.4(2)")
  (statement := /-- If $x >1$, then there
  is a prime in the interval
  \[ \left( x, x\left(1 + \frac{198.2}{\log^4 x}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval_2 (x : ℝ) (hx : x > 1) :
    HasPrimeInInterval x (x * (198.2 / (log x) ^ 4)) := by sorry

end Axler2018

namespace Dusart

def proposition_5_4_copy : HasPrimeInInterval.log_thm 89693 3 := _root_.Dusart.proposition_5_4

def corollary_5_5_copy {x : ℝ} (hx : x ≥ 468991632) :
    HasPrimeInInterval x (x * (1 + 1 / (5000 * (log x) ^ 2))) :=
  _root_.Dusart.corollary_5_5 hx

end Dusart

namespace Dudek2014

@[blueprint
  "thm:dudek2014"
  (title := "Dudek 2014")
  (statement := /-- If $x > \exp(\exp(34.32))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > exp (exp 34.32)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) := by sorry

end Dudek2014

namespace CullyHugill2021

@[blueprint
  "thm:cully-hugill2021"
  (title := "Cully-Hugill 2021")
  (statement := /-- If $x > \exp(\exp(33.99))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > exp (exp 33.99)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) := by sorry

end CullyHugill2021

namespace RHPrimeInterval2002

@[blueprint
  "thm:rh_prime_interval_2002"
  (title := "RH Prime Interval 2002")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{8}{5}\sqrt{x} \log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (8 / 5) * sqrt x * log x) ((8 / 5) * sqrt x * log x) := by sorry

end RHPrimeInterval2002

namespace Dudek2015RH

@[blueprint
  "thm:dudek2015_rh"
  (title := "Dudek 2015 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{4}{\pi}\sqrt{x} \log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (4 / π) * sqrt x * log x) ((4 / π) * sqrt x * log x) := by sorry

end Dudek2015RH

namespace CarneiroEtAl2019RH

@[blueprint
  "thm:carneiroetal_2019_rh"
  (title := "Carneiro et al. 2019 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 4$, there is a prime in the interval
  \[ \left( x - \frac{22}{25}\sqrt{x}\log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x ≥ 4) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (22 / 25) * sqrt x * log x) ((22 / 25) * sqrt x * log x) := by sorry

end CarneiroEtAl2019RH

namespace KadiriLumley

noncomputable def Table_2 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ) :=
  [(log (4 * 10 ^ 18), 5, 3.580e-8, 272519712, 0.92, 0.2129, 36082898),
   (43, 5, 3.349e-8, 291316980, 0.92, 0.2147, 38753947),
   (44, 6, 2.330e-8, 488509984, 0.92, 0.2324, 61162616),
   (45, 7, 1.628e-8, 797398875, 0.92, 0.2494, 95381241),
   (46, 8, 1.134e-8, 1284120197, 0.92, 0.2651, 148306019),
   (47, 9, 8.080e-9, 1996029891, 0.92, 0.2836, 227619375),
   (48, 11, 6.000e-9, 3204848430, 0.93, 0.3050, 346582570),
   (49, 15, 4.682e-9, 5415123831, 0.93, 0.3275, 518958776),
   (50, 20, 3.889e-9, 8466793105, 0.93, 0.3543,753575355),
   (51 ,28 ,3.625e-9 ,12399463961 ,0.93 ,0.3849 ,1037917449),
   (52 ,39 ,3.803e-9 ,16139006408 ,0.93 ,0.4127 ,1313524036),
   (53 ,48 ,4.088e-9 ,18290358817 ,0.93 ,0.4301 ,1524171138),
   (54 ,54 ,4.311e-9 ,19412056863 ,0.93 ,0.4398 ,1670398039),
   (55 ,56 ,4.386e-9 ,19757119193 ,0.93 ,0.4445 ,1770251249),
   (56 ,59 ,4.508e-9 ,20210075547 ,0.93 ,0.4481 ,1838818070),
   (57 ,59 ,4.506e-9 ,20219045843 ,0.93 ,0.4496 ,1886389443),
   (58 ,61 ,4.590e-9 ,20495459359 ,0.93 ,0.4514 ,1920768795),
   (59 ,61 ,4.589e-9 ,20499925573 ,0.93 ,0.4522 ,1946282821),
   (60 ,61 ,4.588e-9 ,20504393735 ,0.93 ,0.4527 ,1966196911),
   (150, 64, 4.685e-9, 21029543983, 0.96, 0.4641, 2442159714)]

@[blueprint
  "thm:prime_gaps_KL"
  (title := "Kadiri-Lumley Prime Gaps")
  (statement := /-- \cite[Theorem 1.1]{kadiri-lumley} If $(\log x_0, m, \delta, T_1, \sigma_0, a, \Delta)$ is a row \cite[Table 2]{kadiri-lumley}, then for all $x \geq x_0$, there is a prime between $x(1-\Delta^{-1})$ and $x$.
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x₀ x m δ T₁ σ₀ a Δ : ℝ) (hx : x ≥ x₀) (hrow : (log x₀, m, δ, T₁, σ₀, a, Δ) ∈ Table_2) :
    HasPrimeInInterval (x*(1- 1 / Δ)) (x/Δ) := by sorry

end KadiriLumley

namespace RamareSaouter2003

@[blueprint
  "thm:ramare_saouter2003-2"
  (title := "Ramar\\'e-Saouter 2003 (2)")
  (statement := /-- If $x > \exp(53)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{204879661}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval_2 (x : ℝ) (hx : x > exp 53) :
    HasPrimeInInterval (x*(1-1/204879661)) (x/204879661) := by
  have hrow : (log (exp 53), (48:ℝ), (4.088e-9:ℝ), (18290358817:ℝ), (0.93:ℝ),
      (0.4301:ℝ), (1524171138:ℝ)) ∈ KadiriLumley.Table_2 := by
    rw [log_exp]; simp only [KadiriLumley.Table_2, List.mem_cons, Prod.mk.injEq,
      List.mem_nil_iff, or_false]; norm_num
  obtain ⟨p, hp, hlo, hhi⟩ := KadiriLumley.has_prime_in_interval (exp 53) x 48 4.088e-9
    18290358817 0.93 0.4301 1524171138 hx.le hrow
  exact ⟨p, hp, by nlinarith [exp_pos (53 : ℝ)],
    by linarith [show x * (1 - 1 / 1524171138) + x / 1524171138 =
      x * (1 - 1 / 204879661) + x / 204879661 from by ring]⟩

end RamareSaouter2003
