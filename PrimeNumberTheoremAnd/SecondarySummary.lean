import Architect
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.NumberTheory.Bertrand
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FKS2
import PrimeNumberTheoremAnd.Dusart

blueprint_comment /--
\section{Summary of results}
-/

blueprint_comment /--
Here we list some papers that we plan to incorporate into this section in the future, and list
some results that have not yet been moved into dedicated paper sections.

References to add:

Dusart \cite{Dusart2018}

PT: D. J. Platt and T. S. Trudgian, The error term in the prime number theorem,
Math. Comp. 90 (2021), no. 328, 871–881.

JY: D. R. Johnston, A. Yang, Some explicit estimates for the error term in the prime number
theorem, arXiv:2204.01980.
-/

open Finset Nat Real Chebyshev


@[blueprint "thm:pt_2"
  (title := "PT Corollary 2")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 235 x (\log x)^{0.52} \exp(-0.8 \sqrt{\log x})
  \]
  for all $x \geq \exp(2000)$.
  -/)
  (latexEnv := "theorem")]
theorem PT.corollary_2 : Eπ.classicalBound 235 1.52 0.8 1 (exp 2000) := by
  have := FKS2.corollary_22
  intro x hx
  have hx2 : x ≥ 2 := by grind [add_one_le_exp 2000]
  refine (this x hx2).trans ?_
  simp only [admissible_bound]; norm_num
  suffices h_div : 92211 / 10000 * log x ^ (3 / 2 : ℝ) *
    exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ)) ≤ 235 * log x ^ (38 / 25 : ℝ) by
    convert mul_le_mul_of_nonneg_right h_div (exp_nonneg (-4 / 5 * log x^(1 / 2 : ℝ))) using 1
    · rw [exp_add (-2119 / 2500 * log x^(1 / 2 : ℝ)) (4 / 5 * log x^(1 / 2 : ℝ))]; ring_nf
      norm_num [mul_assoc, ← exp_add]
    simp only [one_div, mul_eq_mul_left_iff, exp_eq_exp, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    left
    linarith
  suffices h_div : 92211 / 10000 * exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ)) ≤
      235 * log x ^ (38 / 25 - 3 / 2 : ℝ) by
    convert mul_le_mul_of_nonneg_right h_div (rpow_nonneg (log_nonneg
      (show x ≥ 1 by linarith)) (3 / 2 : ℝ)) using 1 <;> ring_nf
    rw [← rpow_add (log_pos (by linarith : x > 1))]
    norm_num
  have hsqrtlogpos: 0 < log x ^ (1/2:ℝ) := by exact rpow_pos_of_pos (log_pos (by linarith: x > 1)) (1/2:ℝ)
  have hneg: -(2119 / 2500) * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ) < 0 := by linarith
  have hexpone: exp (-(2119 / 2500) * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ)) < 1 := by exact exp_lt_one_iff.mpr hneg
  have hcompare: 0 ≤ (38 / 25 - 3 / 2 : ℝ) := by linarith
  have hlogone: log x ≥ 1 := by nlinarith [log_exp 2000, log_le_log (by positivity) hx]
  have hlogone2:  (log x)^(0:ℝ) ≤ (log x)^(38 / 25 - 3 / 2 : ℝ) := by exact rpow_le_rpow_of_exponent_le hlogone hcompare
  rw [rpow_zero (log x)] at hlogone2
  linarith

@[blueprint
  "thm:jy_13"
  (title := "JY Corollary 1.3")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 9.59 x (\log x)^{0.515} \exp(-0.8274 \sqrt{\log x})
  \]
  for all $x \geq 2$.
  -/)
  (latexEnv := "theorem")]
theorem JY.corollary_1_3 : Eπ.classicalBound 9.59 1.515 0.8274 1 2 := by
  have := FKS2.corollary_22
  intro x hx
  have hx2 : x ≥ 2 := by grind [add_one_le_exp 2000]
  refine (this x hx2).trans ?_
  simp only [admissible_bound]; norm_num
  suffices h_div : 92211 / 10000 * log x ^ (3 / 2 : ℝ) *
    exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ)) ≤ 959 / 100 * log x ^ (303 / 200 : ℝ) by
    convert mul_le_mul_of_nonneg_right h_div (exp_nonneg (-4137 / 5000 * log x^(1 / 2 : ℝ))) using 1
    · rw [exp_add (-2119 / 2500 * log x^(1 / 2 : ℝ)) (4137 / 5000 * log x^(1 / 2 : ℝ))]
      ring_nf
      norm_num [mul_assoc, ← exp_add]
    simp only [one_div, mul_eq_mul_left_iff, exp_eq_exp, _root_.mul_eq_zero]
    left
    linarith
  suffices h_div : 92211 / 10000 * exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ)) ≤
    959 / 100 * log x ^ (303 / 200 - 3 / 2 : ℝ) by
    convert mul_le_mul_of_nonneg_right h_div (rpow_nonneg (log_nonneg
      (show x ≥ 1 by linarith)) (3 / 2 : ℝ)) using 1 <;> ring_nf
    rw [← rpow_add (log_pos (by linarith : x > 1))]
    norm_num
  have hsqrtlogpos: 0 < log x ^ (1/2:ℝ) := by exact rpow_pos_of_pos (log_pos (by linarith: x > 1)) (1/2:ℝ)
  have hneg: -(2119 / 2500) * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ) < 0 := by linarith
  have hexpone: exp (-(2119 / 2500) * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ)) < 1 := by exact exp_lt_one_iff.mpr hneg

  suffices h_calc: 92211/10000 ≤ 959/100 * log x ^(303 / 200 - 3/2 : ℝ) by linarith
  refine le_trans ?_ <| mul_le_mul_of_nonneg_left (rpow_le_rpow (by grind)
  (log_two_gt_d9.le.trans (log_le_log (by grind) hx)) (by grind)) (by grind)
  norm_num
  rw [← log_le_log_iff (by positivity) (by positivity),
  log_mul (by positivity) (by positivity), log_rpow (by positivity),
  div_mul_eq_mul_div, add_div', le_div_iff₀] <;>
  norm_num [← log_rpow, mul_comm, ← log_mul, log_le_log_iff]


@[blueprint
  "thm:jy_14"
  (title := "JY Theorem 1.4")
  (statement := /--
  One has
  \[
  |\pi(x) - \mathrm{Li}(x)| \leq 0.028 x (\log x)^{0.801}
    \exp(-0.1853 \log^{3/5} x / (\log \log x)^{1/5}))
  \]
  for all $x \geq 2$.
  -/)
  (latexEnv := "theorem")]
theorem JY.theorem_1_4 : Eπ.vinogradovBound 0.028 0.801 0.1853 23 := sorry

blueprint_comment /-- TODO: input other results from JY -/

blueprint_comment /-- The results below are taken from https://tme-emt-wiki-gitlab-io-9d3436.gitlab.io/Art09.html -/

@[blueprint
  "thm:schoenfeld1976"
  (title := "Schoenfeld 1976")
  (statement := /--
  If $x > 2010760$, then there is a prime in the interval
  \[
  \left( x\left(1 - \frac{1}{15697}\right), x \right].
  \]
  -/)
  (latexEnv := "theorem")]
theorem Schoenfeld1976.has_prime_in_interval (x : ℝ) (hx : x > 2010760) :
    HasPrimeInInterval (x*(1-1/15697)) (x/15697) := by sorry

@[blueprint
  "thm:ramare-saouter2003"
  (title := "Ramaré-Saouter 2003")
  (statement := /--
  If $x > 10,726,905,041$, then there is a prime in the interval $(x(1-1/28314000), x]$.
  -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval (x : ℝ) (hx : x > 10726905041) :
    HasPrimeInInterval (x*(1-1/28314000)) (x/28314000) := by sorry

@[blueprint
  "thm:ramare_saouter2003-2"
  (title := "Ramaré-Saouter 2003 (2)")
  (statement := /-- If $x > \exp(53)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{204879661}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval_2 (x : ℝ) (hx : x > exp 53) :
    HasPrimeInInterval (x*(1-1/204879661)) (x/204879661) := by sorry

@[blueprint
  "thm:gourdon-demichel2004"
  (title := "Gourdon-Demichel 2004")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{14500755538}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem GourdonDemichel2004.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/14500755538)) (x/14500755538) := by sorry


@[blueprint
  "thm:prime_gaps_2014"
  (title := "Prime Gaps 2014")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{1966196911}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem PrimeGaps2014.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/1966196911)) (x/1966196911) := by sorry

@[blueprint
  "thm:prime_gaps_2024"
  (title := "Prime Gaps 2024")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{76900000000}\right), x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem PrimeGaps2024.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/76900000000)) (x/76900000000) := by sorry

@[blueprint
  "thm:trudgian2016"
  (title := "Trudgian 2016")
  (statement := /-- If $x > 2,898,242$, then there
  is a prime in the interval
  \[ \left[ x, x\left(1 + \frac{1}{111(\log x)^2}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Trudgian2016.has_prime_in_interval (x : ℝ) (hx : x > 2898242) :
    HasPrimeInInterval x (x / (111 * (log x) ^ 2)) := by sorry

@[blueprint
  "thm:dudek2014"
  (title := "Dudek 2014")
  (statement := /-- If $x > \exp(\exp(34.32))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Dudek2014.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 34.32)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) := by sorry

@[blueprint
  "thm:cully-hugill2021"
  (title := "Cully-Hugill 2021")
  (statement := /-- If $x > \exp(\exp(33.99))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem CullyHugill2021.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 33.99)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) := by sorry

@[blueprint
  "thm:rh_prime_interval_2002"
  (title := "RH Prime Interval 2002")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{8}{5}\sqrt{x} \log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem RHPrimeInterval2002.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (8 / 5) * sqrt x * log x) ((8 / 5) * sqrt x * log x) := by sorry
@[blueprint
  "thm:dudek2015_rh"
  (title := "Dudek 2015 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{4}{\pi}\sqrt{x} \log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Dudek2015RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (4 / π) * sqrt x * log x) ((4 / π) * sqrt x * log x) := by sorry

@[blueprint
  "thm:carneiroetal_2019_rh"
  (title := "Carneiro et al. 2019 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 4$, there is a prime in the interval
  \[ \left( x - \frac{22}{25}\sqrt{x}\log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem CarneiroEtAl2019RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 4) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (22 / 25) * sqrt x * log x) ((22 / 25) * sqrt x * log x) := by sorry
