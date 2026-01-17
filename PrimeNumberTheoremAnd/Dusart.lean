import Architect
import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{Dusart's explicit estimates for primes}

In this section we record the estimates of Dusart \cite{Dusart2018} on explicit estimates for sums over primes.
-/

namespace Dusart

open Nat Real

def Table1 : List (ℝ × ℝ × ℕ × ℝ × ℝ × ℝ) := [
  (20, 0.86, 5, 1.595e-5, 1132492, 1.067e-3),
  (21, 0.86, 5, 1.468e-5, 1132492, 6.498e-4),
  (22, 0.86, 4, 1.282e-5, 1132492, 3.968e-4),
  (23, 0.86, 4, 1.160e-5, 1132492, 2.431e-4),
  (24, 0.85, 3, 9.778e-6, 1132492, 1.496e-4),
  (25, 0.86, 3, 8.629e-6, 1132492, 9.250e-5),
  (30, 0.86, 2, 2.554e-6, 1882244, 9.647e-6),
  (35, 0.86, 2, 2.458e-7, 19612863, 1.078e-6),
  (40, 0.87, 2, 2.756e-8, 161338534, 1.161e-7),
  (45, 0.87, 3, 2.721e-9, 2228096512, 1.225e-8),
  (50, 0.88, 5, 2.572e-10, 37754757543, 1.275e-9),
  (55, 0.89, 15, 4.374e-11, 568871547031, 1.388e-10),
  (60, 0.90, 23, 3.812e-11, 973812914637, 2.978e-11),
  (65, 0.90, 23, 3.751e-11, 989645080596, 2.039e-11),
  (70, 0.90, 22, 3.697e-11, 963148272814, 1.940e-11),
  (75, 0.90, 22, 3.658e-11, 973564683528, 1.913e-11),
  (80, 0.91, 22, 3.621e-11, 987265077216, 1.893e-11),
  (85, 0.91, 22, 3.573e-11, 996465239887, 1.868e-11),
  (90, 0.91, 22, 3.533e-11, 1007775601523, 1.847e-11),
  (95, 0.91, 21, 3.492e-11, 976821063390, 1.830e-11),
  (100, 0.91, 21, 3.464e-11, 987265077216, 1.815e-11),
  (200, 0.94, 18, 2.951e-11, 1003417649160, 1.557e-11),
  (300, 0.95, 16, 2.642e-11, 1006421703556, 1.404e-11),
  (400, 0.96, 14, 2.403e-11, 980285487059, 1.288e-11),
  (500, 0.96, 13, 2.255e-11, 977429125922, 1.215e-11),
  (600, 0.97, 12, 2.058e-11, 997132955137, 1.115e-11),
  (700, 0.97, 11, 1.904e-11, 998061945822, 1.039e-11),
  (800, 0.97, 11, 1.801e-11, 1019509030546, 9.826e-12),
  (900, 0.97, 10, 1.688e-11, 1019509030546, 9.281e-12),
  (1000, 0.97, 9, 1.574e-11, 1012519261279, 8.743e-12),
  (1500, 0.98, 5, 8.852e-12, 1019509030546, 5.311e-12),
  (2000, 0.98, 2, 3.381e-12, 1364832983117, 2.536e-12),
  (2500, 0.98, 2, 1.193e-12, 2445999556029, 8.941e-13),
  (3000, 0.98, 2, 4.209e-13, 2445999556030, 3.156e-13),
  (3500, 0.98, 2, 1.487e-13, 2445999556030, 1.116e-13),
  (4000, 0.98, 2, 5.262e-14, 2445999556030, 3.946e-14),
  (4500, 0.99, 2, 1.699e-14, 2445999556030, 1.274e-14),
  (5000, 0.99, 2, 5.274e-15, 2445999556030, 3.956e-15),
  (6000, 0.99, 2, 6.524e-16, 2445999556030, 4.893e-16),
  (7000, 0.99, 2, 8.524e-17, 2445999556030, 6.393e-17),
  (8000, 0.99, 2, 1.196e-17, 2445999556030, 8.969e-18),
  (9000, 0.99, 2, 3.236e-18, 2445999556030, 2.427e-18),
  (10000, 0.99, 3, 1.222e-17, 2445999556030, 8.144e-18),
  (13900, 0.99, 2, 3.144e-20, 2445999556030, 2.358e-20)
]

@[blueprint "Dusart_prop_3_2"
  (title := "Dusart Proposition 3.2")
  (statement := /--
  For $x \geq e^{b}$ we have $\psi(x) - x| \leq \varepsilon$, where $b, \varepsilon$ are given by \cite[Table 1]{Dusart2018}.-/)
  (latexEnv := "proposition")]
theorem proposition_3_2 {b σ₀ : ℝ} {m : ℕ} {δ T₁ ε : ℝ} (h : (b, σ₀, m, δ, T₁, ε) ∈ Table1)
{x : ℝ} (hx : x ≥ exp b) : Eψ x ≤ ε := by sorry

def Table_3_3 : List (ℕ × ℝ) := [
   (0, 0.77),
   (1, 0.85),
   (2, 1.66),
   (3, 8.16),
   (4, 59.18)
]

@[blueprint "Dusart_thm_3_3"
  (title := "Dusart Theorem 3.3")
  (statement := /--
  We have $|\psi(x) - x| < \eta_k x / \log^k x$ for $x \geq 2$ with $(k,\eta)$ given by the table in \cite[Theorem 3.3]{Dusart2018}.-/)
  (latexEnv := "theorem")]
theorem theorem_3_3 {k : ℕ} {η : ℝ} (h : (k, η) ∈ Table_3_3) {x : ℝ} (hx : x ≥ 2) :
  Eψ x ≤ η / (log x) ^ k := by sorry

/- x ϑ(x) ψ(x)−ϑ(x) 1E+10 9999939830.657757 102289.175716 2E+10 19999821762.768212 144339.622582 3E+10 29999772119.815419 176300.955450 4E+10 39999808348.775748 203538.541084 5E+10 49999728380.731899 227474.729168 6E+10 59999772577.550769 249003.320704 7E+10 69999769944.203933 268660.720820 8E+10 79999718357.195652 287365.266118 9E+10 89999644656.090911 304250.688854 1E+11 99999737653.107445 320803.322857 2E+11 199999695484.246439 453289.609568 3E+11 299999423179.995211 554528.646163 4E+11 399999101196.308601 640000.361434 5E+11 499999105742.583455 715211.001138 6E+11 599999250571.436655 783167.715577 7E+11 699998999499.845475 845911.916175 8E+11 799999133776.084743 904203.190001 9E+11 899998818628.952024 958602.924046 1E+12 999999030333.096225 1009803.669232 2E+12 1999998755521.470649 1427105.865316 3E+12 2999997819758.987859 1746299.820370 4E+12 3999998370195.717561 2016279.693623 5E+12 4999998073643.711478 2253672.042145 6E+12 5999997276726.877147 2467566.593710 7E+12 6999996936360.165729 2665065.541181 8E+12 7999997864671.383505 2848858.049155 9E+12 8999996425300.244577 3021079.319393 1E+13 9999996988293.034200 3183704.089025 2E+13 19999995126082.228688 4499685.436490 3E+13 29999995531389.845427 5509328.368277 4E+13 39999993533724.316829 6359550.652121 5E+13 49999992543194.263655 7109130.001413 6E+13 59999990297033.626198 7785491.725387 7E+13 69999994316409.871731 8407960.376833 8E+13 79999990160858.304239 8988688.375101 9E+13 89999989501395.073897 9531798.550749 1E+14 99999990573246.978538 10045400.569463 2E+14 199999983475767.543204 14201359.711421 3E+14 299999986702246.281944 17388356.540338 4E+14 399999982296901.085038 20074942.600622 123Explicitestimatesofsomefunctionsoverprimes 237 Table2 continued x ϑ(x) ψ(x)−ϑ(x) 5E+14 499999974019856.236519 22439658.012185 6E+14 599999983610646.997632 24580138.242324 7E+14 699999971887332.157455 26545816.027402 8E+14 799999964680836.091645 28378339.693784 9E+14 899999961386694.231242 30098146.961102 1E+15 999999965752660.939840 31724269.567843
-/

def Table2 : List ( ℝ × ℝ × ℝ ) := [
  (1e10, 9999939830.657757, 102289.175716),
  (2e10, 19999821762.768212, 144339.622582),
  (3e10, 29999772119.815419, 176300.955450),
  (4e10, 39999808348.775748, 203538.541084),
  (5e10, 49999728380.731899, 227474.729168),
  (6e10, 59999772577.550769, 249003.320704),
  (7e10, 69999769944.203933, 268660.720820),
  (8e10, 79999718357.195652, 287365.266118),
  (9e10, 89999644656.090911, 304250.688854),
  (1e11, 99999737653.107445, 320803.322857),
  (2e11, 199999695484.246439, 453289.609568),
  (3e11, 299999423179.995211, 554528.646163),
  (4e11, 399999101196.308601, 640000.361434),
  (5e11, 499999105742.583455, 715211.001138),
  (6e11, 599999250571.436655, 783167.715577),
  (7e11, 699998999499.845475, 845911.916175),
  (8e11, 799999133776.084743, 904203.190001),
  (9e11, 899998818628.952024, 958602.924046),
  (1e12, 999999030333.096225, 1009803.669232),
  (2e12, 1999998755521.470649,1427105.865316),
  (3e12,2999997819758.987859,1746299.820370),
  (4e12,3999998370195.717561,2016279.693623),
  (5e12,4999998073643.711478,2253672.042145),
  (6e12,5999997276726.877147,2467566.593710),
  (7e12,6999996936360.165729,2665065.541181),
  (8e12,7999997864671.383505,2848858.049155),
  (9e12,8999996425300.244577,3021079.319393),
  (1e13,9999996988293.034200,3183704.089025),
  (2e13,19999995126082.228688,4499685.436490),
  (3e13,29999995531389.845427,5509328.368277),
  (4e13,39999993533724.316829,6359550.652121),
  (5e13,49999992543194.263655,7109130.001413),
  (6e13,59999990297033.626198,7785491.725387),
  (7e13,69999994316409.871731,8407960.376833),
  (8e13,79999990160858.304239,8988688.375101),
  (9e13,89999989501395.073897,9531798.550749),
  (1e14,99999990573246.978538,10045400.569463),
  (2e14,199999983475767.543204,14201359.711421),
  (3e14,299999986702246.281944,17388356.540338),
  (4e14,399999982296901.085038,20074942.600622),
  (5e14,499999974019856.236519,22439658.012185),
  (6e14,599999983610646.997632,24580138.242324),
  (7e14,699999971887332.157455,26545816.027402),
  (8e14,799999964680836.091645,28378339.693784),
  (9e14,899999961386694.231242,30098146.961102),
  (1e15,999999965752660.939840,31724269.567843)
]

@[blueprint "Dusart_lemma_4_1"
  (title := "Dusart Lemma 4.1")
  (statement := /--
  We have $\vartheta(x)$ and $\psi(x)-\vartheta(x)$ for various $x$ given by \cite[Table 2]{Dusart2018}, in particular
  $10^{15} = 999999965752660.939839805291048\dots$-/)
  (latexEnv := "lemma")]
theorem lemma_4_1 {x ϑx ψϑx : ℝ} (h : (x, ϑx, ψϑx) ∈ Table2) : θ x ∈ Set.Icc ϑx (ϑx + 1e-6) ∧ ψ x - θ x ∈ Set.Icc ψϑx (ψϑx + 1e-6) := by sorry

def Table_4_2 : List (ℕ × ℝ × ℝ) := [
  (0, 1, 1),
  (1, 1.2323, 2),
  (2, 0.001, 908994923),
  (2, 3.965, 3594641),
  (2, 0.2, 122568683),
  (2, 0.05, 7713133853),
  (3, 20.83, 2),
  (3, 10, 32321),
  (3, 1, 89967803),
  (3, 0.78, 158822621),
  (3, 0.5, 767135587),
  (4, 151.3, 2)
]

@[blueprint "Dusart_thm_4_2"
  (title := "Dusart Theorem 4.2")
  (statement := /--
  We have $|\vartheta(x) - x| < \eta_k x / \log^k x$ for $x \geq x_k$ with $(k,\eta_k,x_k)$ given by the table in \cite[Theorem 4.2]{Dusart2018}.-/)
  (latexEnv := "theorem")]
theorem theorem_4_2 {k : ℕ} {ηk xk : ℝ} (h : (k, ηk, xk) ∈ Table_4_2) {x : ℝ} (hx : x ≥ xk) :
  Eθ x ≤ ηk / (log x) ^ k := by sorry

@[blueprint "Dusart_prop_4_3"
  (title := "Dusart Proposition 4.3")
  (statement := /--
  For $x \geq 121$, we have
  \[
  1 - \frac{4 \log 2}{\log x} \sqrt{x} < \psi(x) - \vartheta(x),
  \quad \sqrt{\frac{\log^3 x}{x}} \, \vartheta(x^{1/2}).
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_4_3 {x : ℝ} (hx : x ≥ 121) :
  ψ x - θ x ≥ 1 - (4 * Real.log 2) / (log x) * sqrt x ∧
  ψ x - θ x ≥ sqrt (log x ^ 3 / x) * θ (x ^ (1 / 2 : ℝ)) := by sorry

@[blueprint "Dusart_prop_4_4"
  (title := "Dusart Proposition 4.4")
  (statement := /--
  For $x > 0$, we have
  \[
  \psi(x) - \vartheta(x) - \vartheta(\sqrt{x}) < 1.777745 x^{1/3}.
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_4_4 {x : ℝ} (hx : x > 0) :
  ψ x - θ x - θ (sqrt x) < 1.777745 * x ^ (1 / 3 : ℝ) := by sorry

@[blueprint "Dusart_corollary_4_5"
  (title := "Dusart Corollary 4.5")
  (statement := /--
  For $x > 0$, we have
  \[
  \psi(x) - \vartheta(x) < \Bigl(1 + 1.47 \times 10^{-7}\Bigr) \sqrt{x} + 1.78 x^{1/3}.
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_4_5 {x : ℝ} (hx : x > 0) :
  ψ x - θ x < (1 + 1.47e-7) * sqrt x + 1.78 * x ^ (1 / 3 : ℝ) := by sorry

/- Theorem5.1Forx⩾4·109, π(x)= x lnx 1+ 1 lnx + 2 ln2x+O∗ 7.32 ln3x . -/

@[blueprint "Dusart_thm_5_1"
  (title := "Dusart Theorem 5.1")
  (statement := /--
  For $x \geq 4 \times 10^9$, we have
  \[
  \pi(x) = \frac{x}{\log x} \Biggl(1 + \frac{1}{\log x} + \frac{2 \log \log x}{\log^2 x} + O^*\Bigl(\frac{7.32}{\log^3 x}\Bigr)\Biggr).
  \]
  -/)
  (latexEnv := "theorem")]
theorem theorem_5_1 {x : ℝ} (hx : x ≥ 4e9) : ∃ E,
  (pi x = x / log x * (1 + 1 / log x + 2 * log (log x) / (log x) ^ 2 + E) ∧ |E| ≤ 7.32 / (log x) ^ 3) := by sorry

@[blueprint "Dusart_cor_5_2_a"
  (title := "Dusart Corollary 5.2 (a)")
  (statement := /--
  For $x \geq 17$, we have
  \[
  \frac{x}{\log x} \leq \pi(x).
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_2_a {x : ℝ} (hx : x ≥ 17) : pi x ≥ x / log x := by sorry

@[blueprint "Dusart_cor_5_2_b"
  (title := "Dusart Corollary 5.2 (b)")
  (statement := /--
  For $x > 1$, we have
  \[
  \pi(x) \leq 1.2551 \frac{x}{\log x}.
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_2_b {x : ℝ} (hx : x > 1) : pi x ≤ 1.2551 * (x / log x) := by sorry

@[blueprint "Dusart_cor_5_2_c"
  (title := "Dusart Corollary 5.2 (c)")
  (statement := /--
  For $x \geq 599$, we have
  \[
  \pi(x) \geq \frac{x}{\log x} \Bigl(1 + \frac{1}{\log x}\Bigr).
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_2_c {x : ℝ} (hx : x ≥ 599) : pi x ≥ x / log x * (1 + 1 / log x) := by sorry

@[blueprint "Dusart_cor_5_2_d"
  (title := "Dusart Corollary 5.2 (d)")
  (statement := /--
  For $x > 1$, we have
  \[
  \pi(x) \leq \frac{x}{\log x} \Bigl(1 + \frac{1.2762}{\log x}\Bigr).
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_2_d {x : ℝ} (hx : x > 1) : pi x ≤ x / log x * (1 + 1.2762 / log x) := by sorry

@[blueprint "Dusart_cor_5_2_e"
  (title := "Dusart Corollary 5.2 (e)")
  (statement := /--
  For $x \geq 88789$, we have
  \[
  \pi(x) \geq \frac{x}{\log x} \Bigl(1 + \frac{1}{\log x} + \frac{2}{\log^2 x}\Bigr).
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_2_e {x : ℝ} (hx : x ≥ 88789) : pi x ≥ x / log x * (1 + 1 / log x + 2 / (log x) ^ 2) := by sorry

@[blueprint "Dusart_cor_5_2_f"
  (title := "Dusart Corollary 5.2 (f)")
  (statement := /--
  For $x > 1$, we have
  \[
  \pi(x) \leq \frac{x}{\log x} \Bigl(1 + \frac{1}{\log x} + \frac{2.53816}{\log^2 x}\Bigr).
  \]
  -/)
  (latexEnv := "corollary")]

theorem corollary_5_2_f {x : ℝ} (hx : x > 1) : pi x ≤ x / log x * (1 + 1 / log x + 2.53816 / (log x) ^ 2) := by sorry

@[blueprint "Dusart_cor_5_3_a"
  (title := "Dusart Corollary 5.3 (a)")
  (statement := /--
  For $x \geq 5393$, we have
  \[
  \frac{x}{\log x - 1} \leq \pi(x)
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_3_a {x : ℝ} (hx : x ≥ 5393) : pi x ≥ x / (log x - 1) := by sorry

@[blueprint "Dusart_cor_5_3_b"
  (title := "Dusart Corollary 5.3 (b)")
  (statement := /--
  For $x > e^{1.112}, we have
  \[
  \pi(x) \leq \frac{x}{\log x - 1.112}.
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_3_b {x : ℝ} (hx : x > exp 1.112) : pi x ≤ x / (log x - 1.112) := by sorry

@[blueprint "Dusart_cor_5_3_c"
  (title := "Dusart Corollary 5.3 (c)")
  (statement := /--
  For $x \geq 468049$, we have
  \[
  \frac{x}{\log x - 1 - \frac{1}{\log x}} \leq \pi(x).
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_3_c {x : ℝ} (hx : x ≥ 468049) : pi x ≥ x / (log x - 1 - 1 / log x) := by sorry

@[blueprint "Dusart_cor_5_3_d"
  (title := "Dusart Corollary 5.3 (d)")
  (statement := /--
  For $x > 5.6$, we have
  \[
  \pi(x) \leq \frac{x}{\log x - 1 - \frac{1.2311}{\log x}}.
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_3_d {x : ℝ} (hx : x > 5.6) : pi x ≤ x / (log x - 1 - 1.2311 / log x) := by sorry

@[blueprint "Dusart_prop_5_4"
  (title := "Dusart Proposition 5.4")
  (statement := /--
  There exists a constant $X_0$ (one may take $X_0 = 89693$) with the following property:
  for every real $x \geq X_0$, there exists a prime $p$ with
  \[
  x < p \le x\Bigl(1 + \frac{1}{\log^3 x}\Bigr).
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_5_4 : HasPrimeInInterval.log_thm 89693 3 := sorry

@[blueprint "Dusart_cor_5_5"
  (title := "Dusart Corollary 5.5")
  (statement := /--
  For all $x \geq 468991632$, there exists a prime $p$ such that
  \[
  x < p \leq x\Bigl(1 + \frac{1}{5000 \log^2 x}\Bigr).
  \]
  -/)
  (latexEnv := "corollary")]
theorem corollary_5_5 {x : ℝ} (hx : x ≥ 468991632) : HasPrimeInInterval x (x * (1 + 1 / (5000 * (log x) ^ 2))) := by sorry

@[blueprint "Dusart_thm_5_6"
  (title := "Dusart Theorem 5.6")
  (statement := /--
  We have for $x \geq 2278383$,
  \[
  \sum_{p \leq x} \frac{1}{p} = \log \log x + M + O^*\Bigl(\frac{0.2}{\log^3 x}\Bigr).
  \]
  -/)
  (latexEnv := "theorem")]
theorem theorem_5_6 {x : ℝ} (hx : x ≥ 2278383) : ∃ E,
  ( (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), 1 / p) = log (log x) + meisselMertensConstant + E ∧ |E| ≤ 0.2 / (log x) ^ 3 ) := by sorry

@[blueprint "Dusart_thm_5_7"
  (title := "Dusart Theorem 5.7")
  (statement := /--
  We have for $x \geq 912560$,
  \[
  \sum_{p \leq x} \frac{\log p}{p} = \log x + E + O^*\Bigl(\frac{0.3}{\log^2 x}\Bigr).
  \]
  -/)
  (latexEnv := "theorem")]
theorem theorem_5_7 {x : ℝ} (hx : x ≥ 912560) : ∃ E,
  ( (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), Real.log p / p) = log x
  + mertensConstant + E ∧ |E| ≤ 0.3 / (log x) ^ 2 ) := by sorry

@[blueprint "Dusart_thm_5_9a"
  (title := "Dusart Theorem 5.9 (a)")
  (statement := /--
  We have for $x \geq 2278382$,
  \[
  \prod_{p \leq x} \Bigl(1 - \frac{1}{p}\Bigr) = \frac{e^{-\gamma}}{\log x} \Bigl(1 + O^*\Bigl(\frac{0.2}{\log^3 x}\Bigr)\Bigr).
  \]
  -/)
  (latexEnv := "theorem")]
theorem theorem_5_9a {x : ℝ} (hx : x ≥ 2278382) : ∃ E,
  ( (∏ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), (1 - 1 / p)) = exp (-eulerMascheroniConstant) / log x * (1 + E) ∧ |E| ≤ 0.2 / (log x) ^ 3 ) := by sorry

@[blueprint "Dusart_thm_5_9b"
  (title := "Dusart Theorem 5.9 (b)")
  (statement := /--
  We have for $x \geq 2278382$,
  \[
  \prod_{p \leq x} \frac{p}{p-1} = e^{\gamma} \log x \Bigl(1 + O^*\Bigl(\frac{0.2}{\log^3 x}\Bigr)\Bigr).
  \] -/)
  (latexEnv := "theorem")]
theorem theorem_5_9b {x : ℝ} (hx : x ≥ 2278382) : ∃ E,
  ( (∏ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), p / (p - 1)) = exp eulerMascheroniConstant * log x * (1 + E) ∧ |E| ≤ 0.2 / (log x) ^ 3 ) := by sorry

/- Lemma5.10 pk ⩽ kln pk for k ⩾ 4, ln pk ⩽ lnk +lnlnk +1 for k ⩾ 2. (5.8) (5.9) -/

@[blueprint "Dusart_lemma_5_10a"
  (title := "Dusart Lemma 5.10")
  (statement := /--
  We have for $k \geq 4$, $p_k \leq k \log p_k$.
  -/)
  (latexEnv := "lemma")]
theorem lemma_5_10a {k : ℕ} (hk : k ≥ 4) : nth Nat.Prime k ≤ k * Real.log (nth Nat.Prime k) := by sorry

@[blueprint "Dusart_lemma_5_10b"
  (title := "Dusart Lemma 5.10")
  (statement := /--
  We have for $k \geq 2$, $\log p_k \leq \log k + \log \log k + 1$.
  -/)
  (latexEnv := "lemma")]
theorem lemma_5_10b {k : ℕ} (hk : k ≥ 2) : Real.log (nth Nat.Prime k) ≤ Real.log k + Real.log (Real.log k) + 1 := by sorry

@[blueprint "Massias_Robin_thm_Bv"
  (title := "Massias and Robin Theorem B (v)")
  (statement := /--
  We have for $k \geq 198$,
  \[
  \vartheta(p_k) \leq k \log k + \log \log k - 1 + \frac{\log \log k - 2}{\log k}.
  \]
  -/)
  (latexEnv := "theorem")]
theorem massias_robin_thm_Bv {k : ℕ} (hk : k ≥ 198) :
  θ (nth Nat.Prime k) ≤ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 2) / (Real.log k) := by sorry

@[blueprint "Dusart_prop_5_11a"
  (title := "Dusart Proposition 5.11")
  (statement := /--
  We have for $p_k \geq 10^{11}$,
  \[
  \vartheta(p_k) \geq k \log k + \log \log k - 1 + \frac{\log \log k - 2.050735}{\log k}.
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_5_11a {k : ℕ} (hk : nth Nat.Prime k ≥ 10 ^ 11) :
  θ (nth Nat.Prime k) ≥ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 2.050735) / (Real.log k) := by sorry

@[blueprint "Dusart_prop_5_11b"
  (title := "Dusart Proposition 5.11")
  (statement := /--
  We have for $p_k \geq 10^{15}$,
  \[
  \vartheta(p_k) \geq k \log k + \log \log k - 1 + \frac{\log \log k - 2.04}{\log k}.
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_5_11b {k : ℕ} (hk : nth Nat.Prime k ≥ 10 ^ 15) :
  θ (nth Nat.Prime k) ≥ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 2.04) / (Real.log k) := by sorry

@[blueprint "Dusart_prop_5_12"
  (title := "Dusart Proposition 5.12")
  (statement := /--
  We have for $k \geq 781$,
  \[
  \vartheta(p_k) \leq k \log k + \log \log k - 1 + \frac{\log \log k - 2}{\log k} - \frac{0.782}{\log^2 k}.
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_5_12 {k : ℕ} (hk : k ≥ 781) :
  θ (nth Nat.Prime k) ≤ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 2) / (Real.log k) - 0.782 / (Real.log k) ^ 2 := by sorry

@[blueprint "Dusart_lemma_5_14"
  (title := "Dusart Lemma 5.14")
  (statement := /--
  We have for $k \geq 178974$,
  \[
  p_k \leq k \log k + \log \log k - 1 + \frac{\log \log k - 1.95}{\log k}.
  \]
  -/)
  (latexEnv := "lemma")]
theorem lemma_5_14 {k : ℕ} (hk : k ≥ 178974) :
  nth Nat.Prime k ≤ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 1.95) / (Real.log k) := by sorry

@[blueprint "Dusart_prop_5_15"
  (title := "Dusart Proposition 5.15")
  (statement := /--
  We have for $k \geq 688383$,
  \[
  p_k \leq k \log k + \log \log k - 1 + \frac{\log \log k - 2}{\log k}.
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_5_15 {k : ℕ} (hk : k ≥ 688383) :
  nth Nat.Prime k ≤ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 2) / (Real.log k) := by sorry

@[blueprint "Dusart_prop_5_16"
  (title := "Dusart Proposition 5.16")
  (statement := /--
  We have for $k \geq 3$,
  \[
  p_k \geq k \log k + \log \log k - 1 + \frac{\log \log k - 2.1}{\log k}.
  \]
  -/)
  (latexEnv := "proposition")]
theorem proposition_5_16 {k : ℕ} (hk : k ≥ 3) :
  nth Nat.Prime k ≥ k * Real.log k + Real.log (Real.log k) - 1 + (Real.log (Real.log k) - 2.1) / (Real.log k) := by sorry

end Dusart
