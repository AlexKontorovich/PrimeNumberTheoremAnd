import Architect
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.NumberTheory.Bertrand
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FKS2
import PrimeNumberTheoremAnd.Dusart
import PrimeNumberTheoremAnd.TMEEMT

blueprint_comment /--
\section{Summary of results}
-/

blueprint_comment /--
Here we list some papers that we plan to incorporate into this section in the future, and list
some results that have not yet been moved into dedicated paper sections.

References to add:

Dusart \cite{Dusart2018}

JY: D. R. Johnston, A. Yang, Some explicit estimates for the error term in the prime number
theorem, arXiv:2204.01980.
-/
open Nat hiding log
open Finset Real Chebyshev

namespace PT

blueprint_comment /-- results from \cite{PT2021}-/

def Table_1 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
 [ (1000, 0.98, 461.9, 1.52, 1.89, 1.20e-5),
   (2000, 0.98, 411.4, 1.52, 1.89, 8.35e-10),
   (3000, 0.98, 379.6, 1.52, 1.89, 4.51e-13),
   (4000, 0.98, 356.3, 1.52, 1.89, 7.33e-16),
   (5000, 0.99, 713.0, 1.51, 1.94, 9.77e-19),
   (6000, 0.99, 611.6, 1.51, 1.94, 4.23e-21),
   (7000, 0.99, 590.1, 1.51, 1.94, 3.09e-23),
   (8000, 0.99, 570.5, 1.51, 1.94, 3.12e-25),
   (9000, 0.99, 552.3, 1.51, 1.94, 4.11e-27),
   (10000,0.99,535.4 ,1.51 ,1.94 ,6.78e-29)]


@[blueprint "pt_thm_1"
  (title := "PT Theorem 1")
  (statement := /--
Let $R = 5.573412$. For each row $\{X, \sigma, A, B, C, \epsilon_0\}$ from \cite[Table 1]{PT2021}
we have
\begin{equation}\label{marcellina}
\left|\frac{\psi(x) - x}{x}\right| \leq A \left(\frac{\log x}{R}\right)^B
  \exp\left(-C\sqrt{\frac{\log x}{R}}\right)
\end{equation}
and
\begin{equation*}
\left|\psi(x)-x\right|\leq \epsilon_0 x
\end{equation*}
for all $\log x \geq X$.
  -/)
  (latexEnv := "theorem")]
theorem theorem_1 (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
    Eψ.classicalBound A B C 5.573412 (exp X) ∧
      Eψ.numericalBound (exp X) (fun _ ↦ ε₀) := by sorry

lemma admissible_bound_weaken {A B C x : ℝ}
    (hB : 3 / 2 ≤ B) (hB2 : B ≤ 2)
    (_hC : 0 ≤ C) (hCR : C ^ 2 * 5.5666305 ≤ 4 * 5.573412)
    (hA : 122 ≤ A)
    (hlogx : 5.5666305 ≤ log x) :
    admissible_bound 121.0961 (3 / 2) 2 5.5666305 x ≤ admissible_bound A B C 5.573412 x := by
  refine mul_le_mul ?_ ?_ ?_ ?_ <;> try positivity
  · have h_exp : (log x / 5.5666305) ^ (3 / 2 : ℝ) ≤
        (log x / 5.573412) ^ B * ((5.573412 / 5.5666305) ^ B) := by
      rw [← Real.mul_rpow (div_nonneg (by linarith) (by norm_num)) (by norm_num)]
      ring_nf at *; norm_num at *
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h_div : 121.0961 * ((5.573412 / 5.5666305) ^ B) ≤ A :=
      le_trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hB2) (by norm_num))
        (by norm_num; linarith)
    nlinarith [Real.rpow_pos_of_pos
      (show 0 < log x / 5.573412 from div_pos (lt_of_lt_of_le (by norm_num) hlogx) (by norm_num)) B]
  · norm_num at *
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at *
    nlinarith [Real.sqrt_nonneg (log x / (11133261 / 2000000)),
      Real.mul_self_sqrt (by linarith : 0 ≤ log x / (11133261 / 2000000)),
      Real.sqrt_nonneg (log x / (1393353 / 250000)),
      Real.mul_self_sqrt (by linarith : 0 ≤ log x / (1393353 / 250000))]

lemma table_1_bounds (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
    1000 ≤ X ∧ 3 / 2 ≤ B ∧ B ≤ 2 ∧ 0 ≤ C ∧ C ^ 2 * 5.5666305 ≤ 4 * 5.573412 ∧
    122 ≤ A + 0.1 := by
  simp only [Table_1, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  constructor <;> norm_num

@[blueprint "pt_cor_1"
  (title := "PT Corollary 1")
  (statement := /--
Let $R = 5.573412$. For each row $\{X, \sigma, A, B, C, \epsilon_0\}$ from \cite[Table 1]{PT2021}
we have
$$
\left|\frac{\theta(x) - x}{x}\right| \leq A_1 \left(\frac{\log x}{R}\right)^B
  \exp\left(-C\sqrt{\frac{\log x}{R}}\right)
$$
where $A_1 = A + 0.1$.
  -/)
  (proof := /-- This follows trivially (and wastefully) from the work of Dusart
  \cite[Cor.\ 4.5]{Dusart} or the authors \cite[Cor.\ 2]{PT2021}. It should also follow from
  the results of \cite{FKS2}. -/)
  (latexEnv := "corollary")]
theorem corollary_1 (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
  Eθ.classicalBound (A + 0.1) B C 5.573412 (exp X) := by
  obtain ⟨hX, hB, hB2, hC, hCR, hA⟩ := table_1_bounds X σ A B C ε₀ h
  intro x hx
  have hx2 : x ≥ 2 := by
    have : (2 : ℝ) < exp 1 := lt_trans (by norm_num : (2:ℝ) < 2.7182818283) exp_one_gt_d9
    linarith [exp_le_exp.mpr (show (1:ℝ) ≤ X by linarith)]
  have hlogx : 5.5666305 ≤ log x := by
    have : X ≤ log x := le_trans (le_of_eq (log_exp X).symm) (log_le_log (exp_pos X) hx)
    linarith
  exact le_trans (FKS2.corollary_14 x hx2) (admissible_bound_weaken hB hB2 hC hCR hA hlogx)

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
theorem corollary_2 : Eπ.classicalBound 235 1.52 0.8 1 (exp 2000) := by
  have := FKS2.corollary_22
  intro x hx
  have hx2 : x ≥ 2 := by grind [add_one_le_exp 2000]
  refine (this x hx2).trans ?_
  simp only [admissible_bound]; norm_num
  suffices h_div :
      92211 / 10000 * log x ^ (3 / 2 : ℝ) *
        exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ)) ≤
        235 * log x ^ (38 / 25 : ℝ)
    by
    convert mul_le_mul_of_nonneg_right h_div (exp_nonneg (-4 / 5 * log x^(1 / 2 : ℝ))) using 1
    · rw [exp_add (-2119 / 2500 * log x^(1 / 2 : ℝ)) (4 / 5 * log x^(1 / 2 : ℝ))]; ring_nf
      norm_num [mul_assoc, ← exp_add]
    simp only [one_div, mul_eq_mul_left_iff, exp_eq_exp, _root_.mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or]
    left
    linarith
  suffices h_div :
      92211 / 10000 * exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ)) ≤
        235 * log x ^ (38 / 25 - 3 / 2 : ℝ)
    by
    convert mul_le_mul_of_nonneg_right h_div
        (rpow_nonneg (log_nonneg (show x ≥ 1 by linarith)) (3 / 2 : ℝ)) using 1 <;> ring_nf
    rw [← rpow_add (log_pos (by linarith : x > 1))]
    norm_num
  have hsqrtlogpos : 0 < log x ^ (1/2:ℝ) :=
    by exact rpow_pos_of_pos (log_pos (by linarith : x > 1)) (1/2:ℝ)
  have hneg : -(2119 / 2500) * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ) < 0 := by linarith
  have hexpone :
      exp (-(2119 / 2500) * log x^(1 / 2 : ℝ) + 4 / 5 * log x^(1 / 2 : ℝ)) < 1 := by
    exact exp_lt_one_iff.mpr hneg
  have hcompare : 0 ≤ (38 / 25 - 3 / 2 : ℝ) := by linarith
  have hlogone : log x ≥ 1 := by nlinarith [log_exp 2000, log_le_log (by positivity) hx]
  have hlogone2 : (log x)^(0:ℝ) ≤ (log x)^(38 / 25 - 3 / 2 : ℝ) :=
    by exact rpow_le_rpow_of_exponent_le hlogone hcompare
  rw [rpow_zero (log x)] at hlogone2
  linarith

end PT

namespace Trudgian2016

blueprint_comment /-- Here we record some results from \cite{trudgian}. TODO: add the Section 3.3
  material on the conjecture of Pomerance --/

@[blueprint
  "trudgian:eps_0-def"
  (title := "Trudgian definition of eps0")
  (statement := /--
  One has
  \[
\epsilon_{0}(x) = \sqrt{\frac{8}{17 \pi}} X^{1/2}e^{-X}, \quad X = \sqrt{(\log x)/R},
  \quad R = 6.455.
  \]
  for all $x \geq 2$.
  -/)]
noncomputable def eps_0 (x : ℝ) : ℝ :=
  sqrt (8 / (17 * π)) * sqrt (sqrt (log x / 6.455)) * exp (-sqrt (log x / 6.455))

@[blueprint
  "trudgian:theorem 1-theta"
  (title := "Trudgian Theorem 1 for theta")
  (statement := /--
  For $x \geq 149$ one has $|\theta(x) - x| \leq x \epsilon_{0}(x)$.-/)
  (latexEnv := "theorem")]
theorem theorem_1_theta (x : ℝ) (hx : x ≥ 149) :
    Eθ.numericalBound x eps_0 := by sorry

@[blueprint
  "trudgian:theorem 1-psi"
  (title := "Trudgian Theorem 1 for psi")
  (statement := /--
  For $x \geq 23$ one has $|\psi(x) - x| \leq x \epsilon_0(x)$.
  -/)
  (latexEnv := "theorem")]
theorem theorem_1_psi (x : ℝ) (hx : x ≥ 23) :
    Eψ.numericalBound x eps_0 := by sorry


@[blueprint
  "trudgian:lemma 1"
  (title := "Trudgian Lemma 1")
  (statement := /--
  For $x \geq \exp(35)$ we have
  \[
  |\theta(x) - x| \leq \frac{0.0045x}{\log^2 x}.
  \]
  -/)
  (latexEnv := "lemma")]
theorem lemma_1 (x : ℝ) (hx : x ≥ exp 35) :
    Eθ.numericalBound x (fun x ↦ 0.0045 / log x ^ 2) := by sorry


@[blueprint
  "trudgian:theorem 2"
  (title := "Trudgian Theorem 2")
  (statement := /--
  For $x \geq 229$ one has
  \[
  |\pi(x) - \mathrm{li}(x)| \leq 0.2795 \frac{x}{(\log x)^{3/4}}
    \exp\left(-\sqrt{\frac{\log x}{6.455}}\right).
  \]
  -/)
  (latexEnv := "theorem")]
theorem theorem_2 (x : ℝ) (hx : x ≥ 229) :
    Eπ.numericalBound x (fun x ↦ 0.2795 * (log x)^(1/4) * exp (-sqrt (log x / 6.455))) := by
  sorry


@[blueprint
  "thm:trudgian2016"
  (title := "Trudgian Corollary 2")
  (statement := /-- If $x > 2,898,242$, then there
  is a prime in the interval
  \[ \left[ x, x\left(1 + \frac{1}{111(\log x)^2}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem has_prime_in_interval (x : ℝ) (hx : x > 2898242) :
    HasPrimeInInterval x (x / (111 * (log x) ^ 2)) := by sorry



end Trudgian2016

namespace JY

blueprint_comment /-- results from \cite{johnston-yang}-/

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
theorem corollary_1_3 : Eπ.classicalBound 9.59 1.515 0.8274 1 2 := by
  have := FKS2.corollary_22
  intro x hx
  have hx2 : x ≥ 2 := by grind [add_one_le_exp 2000]
  refine (this x hx2).trans ?_
  simp only [admissible_bound]; norm_num
  suffices h_div :
      92211 / 10000 * log x ^ (3 / 2 : ℝ) *
        exp (-2119 / 2500 * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ)) ≤
        959 / 100 * log x ^ (303 / 200 : ℝ)
    by
    convert mul_le_mul_of_nonneg_right h_div
        (exp_nonneg (-4137 / 5000 * log x^(1 / 2 : ℝ))) using 1
    · rw [exp_add (-2119 / 2500 * log x^(1 / 2 : ℝ)) (4137 / 5000 * log x^(1 / 2 : ℝ))]
      ring_nf
      norm_num [mul_assoc, ← exp_add]
    simp only [one_div, mul_eq_mul_left_iff, exp_eq_exp, _root_.mul_eq_zero]
    left
    linarith
  suffices h_div :
      92211 / 10000 * exp (-2119 / 2500 * log x^(1 / 2 : ℝ) +
        4137 / 5000 * log x^(1 / 2 : ℝ)) ≤
        959 / 100 * log x ^ (303 / 200 - 3 / 2 : ℝ)
    by
    convert mul_le_mul_of_nonneg_right h_div
        (rpow_nonneg (log_nonneg (show x ≥ 1 by linarith)) (3 / 2 : ℝ)) using 1 <;>
      ring_nf
    rw [← rpow_add (log_pos (by linarith : x > 1))]
    norm_num
  have hsqrtlogpos : 0 < log x ^ (1/2:ℝ) :=
    by exact rpow_pos_of_pos (log_pos (by linarith : x > 1)) (1/2:ℝ)
  have hneg :
      -(2119 / 2500) * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ) < 0 :=
    by linarith
  have hexpone :
      exp (-(2119 / 2500) * log x^(1 / 2 : ℝ) + 4137 / 5000 * log x^(1 / 2 : ℝ)) < 1 := by
    exact exp_lt_one_iff.mpr hneg

  suffices h_calc : 92211/10000 ≤ 959/100 * log x ^(303 / 200 - 3/2 : ℝ) by linarith
  refine le_trans ?_ <| mul_le_mul_of_nonneg_left
    (rpow_le_rpow (by grind) (log_two_gt_d9.le.trans (log_le_log (by grind) hx)) (by grind))
    (by grind)
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
theorem theorem_1_4 : Eπ.vinogradovBound 0.028 0.801 0.1853 23 := sorry

blueprint_comment /-- TODO: input other results from JY -/

end JY



