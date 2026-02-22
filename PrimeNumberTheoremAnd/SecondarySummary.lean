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
open Nat hiding log
open Finset Real Chebyshev

namespace PT


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
Let $R = 5.573412$. For each row $\{X, \sigma, A, B, C, \epsilon_0\}$ from \cite[Table 1]{PT2021} we have
\begin{equation}\label{marcellina}
\left|\frac{\psi(x) - x}{x}\right| \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C\sqrt{\frac{\log x}{R}}\right)
\end{equation}
and
\begin{equation*}
\left|\psi(x)-x\right|\leq \epsilon_0 x
\end{equation*}
for all $\log x \geq X$.
  -/)
  (latexEnv := "theorem")]
theorem theorem_1 (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
  Eψ.classicalBound A B C 5.573412 (exp X) ∧ Eψ.numericalBound (exp X) (fun _ ↦ ε₀) := by sorry

@[blueprint "pt_cor_1"
  (title := "PT Corollary 1")
  (statement := /--
Let $R = 5.573412$. For each row $\{X, \sigma, A, B, C, \epsilon_0\}$ from \cite[Table 1]{PT2021} we have
\begin{equation}\label{marcellina}
\left|\frac{\psi(x) - x}{x}\right| \leq A_1 \left(\frac{\log x}{R}\right)^B \exp\left(-C\sqrt{\frac{\log x}{R}}\right)
\end{equation}
where $A_1 = A + 0.1$.
  -/)
  (proof := /-- This follows trivially (and wastefully) from the work of Dusart  \cite[Cor.\ 4.5]{Dusart} or the authors \cite[Cor.\ 2]{PT2021}.  It should also follow from the results of \cite{FKS2}. -/)
  (latexEnv := "corollary")]
theorem corollary_1 (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
  Eθ.classicalBound (A + 0.1) B C 5.573412 (exp X) := by sorry

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

end PT

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

/-! ### Kadiri-Lumley Prime Gaps

We place the Kadiri-Lumley table and theorem here so that later results
(Ramaré-Saouter 2003 (2), PrimeGaps2014, etc.) can be derived from it. -/

namespace KadiriLumley

noncomputable def Table_2 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  [(log (4 * 10 ^ 18), 5, 3.580e-8, 272519712, 0.92, 0.2129, 36082898),
   (43, 5, 3.349e-8, 291316980, 0.92, 0.2147, 38753947),
   (44, 6, 2.330e-8, 488509984, 0.92, 0.2324, 61162616),
   (45, 7, 1.628e-8, 797398875, 0.92, 0.2494, 95381241),
   (46, 8, 1.134e-8, 1284120197, 0.92, 0.2651, 148306019),
   (47, 9, 8.080e-9, 1996029891, 0.92, 0.2836, 227619375),
   (48, 11, 6.000e-9, 3204848430, 0.93, 0.3050, 346582570),
   (49, 15, 4.682e-9, 5415123831, 0.93, 0.3275, 518958776),
   (50, 20, 3.889e-9, 8466793105, 0.93, 0.3543, 753575355),
   (51, 28, 3.625e-9, 12399463961, 0.93, 0.3849, 1037917449),
   (52, 39, 3.803e-9, 16139006408, 0.93, 0.4127, 1313524036),
   (53, 48, 4.088e-9, 18290358817, 0.93, 0.4301, 1524171138),
   (54, 54, 4.311e-9, 19412056863, 0.93, 0.4398, 1670398039),
   (55, 56, 4.386e-9, 19757119193, 0.93, 0.4445, 1770251249),
   (56, 59, 4.508e-9, 20210075547, 0.93, 0.4481, 1838818070),
   (57, 59, 4.506e-9, 20219045843, 0.93, 0.4496, 1886389443),
   (58, 61, 4.590e-9, 20495459359, 0.93, 0.4514, 1920768795),
   (59, 61, 4.589e-9, 20499925573, 0.93, 0.4522, 1946282821),
   (60, 61, 4.588e-9, 20504393735, 0.93, 0.4527, 1966196911),
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

/-- Helper: if there is a prime in a narrower backward interval `(x*(1-1/Δ₁), x]` with `Δ₁ ≥ Δ₂`,
    then there is also one in the wider interval `(x*(1-1/Δ₂), x]`. -/
private lemma HasPrimeInInterval_of_larger_delta {x Δ₁ Δ₂ : ℝ} (hΔ : Δ₁ ≥ Δ₂) (hΔ₂ : Δ₂ > 0) (hx : x > 0)
    (hp : HasPrimeInInterval (x * (1 - 1 / Δ₁)) (x / Δ₁)) :
    HasPrimeInInterval (x * (1 - 1 / Δ₂)) (x / Δ₂) := by
  obtain ⟨p, hpp, hlo, hhi⟩ := hp
  refine ⟨p, hpp, lt_of_le_of_lt ?_ hlo, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hx.le
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left (by linarith) hΔ₂ hΔ
  · have h1 : x * (1 - 1 / Δ₁) + x / Δ₁ = x := by ring
    have h2 : x * (1 - 1 / Δ₂) + x / Δ₂ = x := by ring
    linarith

@[blueprint
  "thm:ramare_saouter2003-2"
  (title := "Ramaré-Saouter 2003 (2)")
  (statement := /-- If $x > \exp(53)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{204879661}\right), x \right]. \]
  -/)
  (proof := /-- Apply Kadiri-Lumley with the row at $\log x_0 = 53$, which gives
  $\Delta = 1524171138 \geq 204879661$, then use monotonicity of the backward interval. -/)
  (latexEnv := "theorem")]
theorem RamareSaouter2003.has_prime_in_interval_2 (x : ℝ) (hx : x > exp 53) :
    HasPrimeInInterval (x*(1-1/204879661)) (x/204879661) := by
  have hx_pos : x > 0 := lt_trans (exp_pos 53) hx
  have hKL := KadiriLumley.has_prime_in_interval (exp 53) x 48 (4.088e-9) 18290358817 0.93 0.4301 1524171138
    hx.le (by rw [log_exp]; simp [KadiriLumley.Table_2])
  exact HasPrimeInInterval_of_larger_delta (by norm_num : (1524171138 : ℝ) ≥ 204879661)
    (by norm_num) hx_pos hKL

@[blueprint
  "thm:prime_gaps_2014"
  (title := "Prime Gaps 2014")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{1966196911}\right), x \right]. \]
  -/)
  (proof := /-- Apply Kadiri-Lumley with the row at $\log x_0 = 60$, which gives exactly
  $\Delta = 1966196911$. -/)
  (latexEnv := "theorem")]
theorem PrimeGaps2014.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/1966196911)) (x/1966196911) := by
  exact KadiriLumley.has_prime_in_interval (exp 60) x 61 (4.588e-9) 20504393735 0.93 0.4527 1966196911
    hx.le (by rw [log_exp]; simp [KadiriLumley.Table_2])

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
  "thm:gourdon-demichel2004"
  (title := "Gourdon-Demichel 2004")
  (statement := /-- If $x > \exp(60)$, then there is a prime in the interval
  \[ \left( x\left(1 - \frac{1}{14500755538}\right), x \right]. \]
  -/)
  (proof := /-- This follows from PrimeGaps2024 since $76900000000 \geq 14500755538$,
  so the PrimeGaps2024 interval is contained in the Gourdon-Demichel interval. -/)
  (latexEnv := "theorem")]
theorem GourdonDemichel2004.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/14500755538)) (x/14500755538) :=
  HasPrimeInInterval_of_larger_delta (by norm_num : (76900000000 : ℝ) ≥ 14500755538)
    (by norm_num) (lt_trans (exp_pos 60) hx) (PrimeGaps2024.has_prime_in_interval x hx)

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
  "thm:axler2018_1"
  (title := "Axler 2018 Theorem 1.4(1)")
  (statement := /-- If $x ≥ 6034256$, then there
  is a prime in the interval
  \[ \left( x, x\left(1 + \frac{0.087}{\log^3 x}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Axler2018.has_prime_in_interval_1 (x : ℝ) (hx : x ≥ 6034256) :
    HasPrimeInInterval x (x * (0.087 / (log x) ^ 3)) := by sorry

@[blueprint
  "thm:axler2018_2"
  (title := "Axler 2018 Theorem 1.4(2)")
  (statement := /-- If $x >1$, then there
  is a prime in the interval
  \[ \left( x, x\left(1 + \frac{198.2}{\log^4 x}\right) \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem Axler2018.has_prime_in_interval_2 (x : ℝ) (hx : x > 1) :
    HasPrimeInInterval x (x * (198.2 / (log x) ^ 4)) := by sorry

def Dusart.proposition_5_4_copy : HasPrimeInInterval.log_thm 89693 3 := Dusart.proposition_5_4

def Dusart.corollary_5_5_copy {x : ℝ} (hx : x ≥ 468991632) : HasPrimeInInterval x (x * (1 + 1 / (5000 * (log x) ^ 2))) := Dusart.corollary_5_5 hx


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
  "thm:dudek2014"
  (title := "Dudek 2014")
  (statement := /-- If $x > \exp(\exp(34.32))$, then there is a prime in the interval
  \[ \left( x, x + 3x^{2/3} \right]. \]
  -/)
  (proof := /-- This follows from Cully-Hugill 2021 since $\exp(\exp(34.32)) > \exp(\exp(33.99))$. -/)
  (latexEnv := "theorem")]
theorem Dudek2014.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 34.32)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) :=
  CullyHugill2021.has_prime_in_interval x
    (lt_trans (exp_lt_exp.mpr (exp_lt_exp.mpr (by norm_num))) hx)

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
  "thm:rh_prime_interval_2002"
  (title := "RH Prime Interval 2002")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  \[ \left( x - \frac{8}{5}\sqrt{x} \log x, x \right]. \]
  -/)
  (proof := /-- This follows from Dudek 2015 since $4/\pi < 8/5$, so the Dudek interval is
  contained in the wider interval. -/)
  (latexEnv := "theorem")]
theorem RHPrimeInterval2002.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (8 / 5) * sqrt x * log x) ((8 / 5) * sqrt x * log x) := by
  obtain ⟨p, hp, hlo, hhi⟩ := Dudek2015RH.has_prime_in_interval x hx RH
  refine ⟨p, hp, lt_of_le_of_lt ?_ hlo, ?_⟩
  · have h_coeff : (4 : ℝ) / π ≤ 8 / 5 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (5 : ℝ) > 0)]
      linarith [Real.pi_gt_three]
    have h_nn : 0 ≤ sqrt x * log x :=
      mul_nonneg (sqrt_nonneg x) (log_nonneg (by linarith))
    nlinarith [mul_le_mul_of_nonneg_right h_coeff h_nn]
  · linarith

@[blueprint
  "thm:carneiroetal_2019_rh"
  (title := "Carneiro et al. 2019 under RH")
  (statement := /-- Assuming the Riemann Hypothesis, for $x \geq 4$, there is a prime in the interval
  \[ \left( x - \frac{22}{25}\sqrt{x}\log x, x \right]. \]
  -/)
  (latexEnv := "theorem")]
theorem CarneiroEtAl2019RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 4) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (22 / 25) * sqrt x * log x) ((22 / 25) * sqrt x * log x) := by sorry
