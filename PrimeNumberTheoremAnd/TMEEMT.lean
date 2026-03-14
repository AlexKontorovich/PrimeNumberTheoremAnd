import Architect
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.Dusart

blueprint_comment /--
\section{Results from the TME-EMT wiki}

Here we record the results from https://tme-emt-wiki-gitlab-io-9d3436.gitlab.io/index.html

Some of these results are already stated elsewhere.  In such cases, we can fill in the sorrys with the already stated results.

-/

open Real Chebyshev
open ArithmeticFunction hiding log


blueprint_comment /--
\subsection{Explicit bounds on primes}

The results below are taken from https://tme-emt-wiki-gitlab-io-9d3436.gitlab.io/Art01.html -/

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
  |ψ x - x| ≤ (sqrt x) / ((8 * π) * log x ^ 2) := by sorry

@[blueprint
  "thm:buthe-2b"
  (title := "Buthe Theorem 2, part b")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\vartheta(x) - x| \leq \frac{\sqrt{x}}{8\pi}\log(x)^2 \text{for $x>599$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2b (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 599) :
  |θ x - x| ≤ (sqrt x) / ((8 * π) * log x ^ 2) := by sorry

@[blueprint
  "thm:buthe-2c"
  (title := "Buthe Theorem 2, part c")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\pi^*(x) - \li(x)| \leq \frac{\sqrt{x}}{8\pi}\log(x) \text{for $x>59$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2c (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 59) :
  |pi_star x - li x| ≤ (sqrt x) / ((8 * π) * log x) := by sorry

@[blueprint
  "thm:buthe-2d"
  (title := "Buthe Theorem 2, part d")
  (statement := /-- Let $T>0$ such that the Riemann hypothesis holds for $0<\Im(\rho)\leq T$. Then, under the condition $4.92 \sqrt{\frac{x}{\log x}} \leq T$, one has
  $$|\pi(x) - \li(x)| \leq \frac{\sqrt{x}}{8\pi}\log(x) \text{for $x>2657$}.$$
  -/)
  (latexEnv := "theorem")]
theorem theorem_2d (x T : ℝ) (hRH : riemannZeta.RH_up_to T)
  (hT : 4.92 * sqrt (x / log x) ≤ T) (hx : x > 2657) :
  |pi x - li x| ≤ (sqrt x) / ((8 * π) * log x) := by sorry

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
    ψ x ≤ 1.03883 * x := by sorry

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
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), (Real.log p / p) < log x := by sorry

end RS_prime

namespace Dusart1999

blueprint_comment /--
Some results from \cite{Dusart1999}-/

@[blueprint
  "thm:dusart1999-pi"
  (title := "Dusart 1999, π inequality")
  (statement := /-- For $x \geq 17$, we have $\pi(x) > \frac{x}{\log x - 1}$. -/)
  (latexEnv := "theorem")]
theorem pi_inequality (x : ℝ) (hx : x ≥ 17) :
    pi x > x / (log x - 1) := by sorry

@[blueprint
  "thm:dusart1999-a"
  (title := "Dusart 1999, part a")
  (statement := /-- For $x \geq e^{22}$, we have $|\psi(x) - x| \leq \frac{0.006409\, x}{\log x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_a (x : ℝ) (hx : x ≥ exp 22) :
    |ψ x - x| ≤ 0.006409 * x / log x := by sorry

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
    |θ x - x| ≤ 515 * x / (log x) ^ 3 := by sorry

end Dusart1999

namespace Dusart

blueprint_comment /-- Some results from \cite{Dusart2018}-/

@[blueprint
  "thm:dusart2018-theta-improv-1"
  (title := "Dusart 2018, θ improvement 1")
  (statement := /-- For $x > 1$, we have $|\vartheta(x) - x| \leq \frac{20.83\, x}{\log^3 x}$. -/)
  (latexEnv := "theorem")]
theorem theta_improv_1 (x : ℝ) (hx : x > 1) :
    |θ x - x| ≤ 20.83 * x / (log x) ^ 3 := by sorry

@[blueprint
  "thm:dusart2018-theta-improv-2"
  (title := "Dusart 2018, θ improvement 2")
  (statement := /-- For $x \geq 89{,}967{,}803$, we have $|\vartheta(x) - x| \leq \frac{x}{\log^3 x}$. -/)
  (latexEnv := "theorem")]
theorem theta_improv_2 (x : ℝ) (hx : x ≥ 89967803) :
    |θ x - x| ≤ x / (log x) ^ 3 := by sorry

end Dusart

namespace FaberKadiri

blueprint_comment /-- Some results from \cite{faber-kadiri}, \cite{faber-kadiri-corrigendum}-/

@[blueprint
  "thm:faber-kadiri-psi"
  (title := "Faber-Kadiri ψ bound")
  (statement := /-- For $x \geq 485{,}165{,}196$, we have $|\psi(x) - x| \leq 0.00053699\, x$. -/)
  (latexEnv := "theorem")]
theorem psi_bound (x : ℝ) (hx : x ≥ 485165196) :
    |ψ x - x| ≤ 0.00053699 * x := by sorry

end FaberKadiri

namespace JY

blueprint_comment /-- Some results from \cite{johnston-yang}-/

@[blueprint
  "thm:jy-psi-1"
  (title := "Johnston-Yang ψ bound 1")
  (statement := /-- For $x \geq 5000$, we have $|\psi(x) - x| \leq 8.14 \cdot 10^{-20}\, x$. -/)
  (latexEnv := "theorem")]
theorem psi_bound_1 (x : ℝ) (hx : x ≥ 5000) :
    |ψ x - x| ≤ 8.14e-20 * x := by sorry

@[blueprint
  "thm:jy-psi-2"
  (title := "Johnston-Yang ψ bound 2")
  (statement := /-- For $x \geq 2$, we have $|\psi(x) - x| \leq x \cdot 9.39\, (\log x)^{1.51} \exp(-0.8274\sqrt{\log x})$. -/)
  (latexEnv := "theorem")]
theorem psi_bound_2 (x : ℝ) (hx : x ≥ 2) :
    |ψ x - x| ≤ x * 9.39 * (log x) ^ (1.51 : ℝ) * exp (-0.8274 * sqrt (log x)) := by sorry

@[blueprint
  "thm:jy-psi-3"
  (title := "Johnston-Yang ψ bound 3")
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
  (title := "Platt-Trudgian 2021 ψ bound")
  (statement := /-- For $x \geq e^{2000}$, we have $|\psi(x) - x| \leq x \cdot 235\, (\log x)^{0.52} \exp\!\left(-\sqrt{\frac{\log x}{5.573412}}\right)$. -/)
  (latexEnv := "theorem")]
theorem psi_bound (x : ℝ) (hx : x ≥ exp 2000) :
    |ψ x - x| ≤ x * 235 * (log x) ^ (0.52 : ℝ) * exp (-sqrt (log x / 5.573412)) := by sorry

end PT

namespace FKS

blueprint_comment /-- Some results from \cite{FKS}-/

@[blueprint
  "thm:fks-psi"
  (title := "Fiori-Kadiri-Swidinsky ψ bound")
  (statement := /-- For $x \geq 2$, we have $|\psi(x) - x| \leq x \cdot 9.22022\, (\log x)^{1.5} \exp(-0.8476836\sqrt{\log x})$. -/)
  (latexEnv := "theorem")]
theorem psi_bound (x : ℝ) (hx : x ≥ 2) :
    |ψ x - x| ≤ x * 9.22022 * (log x) ^ (1.5 : ℝ) * exp (-0.8476836 * sqrt (log x)) := by sorry

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
    ∑' p : ℕ, (if Nat.Prime p ∧ P ≤ (p : ℝ) then f p * Real.log p else 0) ≤
      (1 + ε) * ∫ t in Set.Ici P, f t +
      ε * P * f P +
      c * P * f P / (Real.log P) ^ 2

@[blueprint
  "thm:ramare2016-3-2-a"
  (title := "Ramaré 2016 Lemma 3.2a")
  (statement := /-- For $P \geq 3{,}600{,}000$ with $\varepsilon = 1/914$ and last-term constant $1/5$:
  for any $C^1$ non-negative non-increasing $f$ on $[P,\infty)$ with $\lim_{t	\to \infty} tf(t)=0$,
  $\sum_{p \geq P} f(p)\log p \leq (1+\frac{1}{914})\int_P^\infty f + \frac{Pf(P)}{914} + \frac{Pf(P)}{5\log^2 P}$. -/)
  (latexEnv := "theorem")]
theorem lemma_3_2_a : lemma_3_2_bound (1/914) (1/5) 3600000 := by sorry

@[blueprint
  "thm:ramare2016-3-2-b"
  (title := "Ramaré 2016 Lemma 3.2b")
  (statement := /-- For $P \geq 2$ with $\varepsilon = 1/914$ and last-term constant $4$:
  for any $C^1$ non-negative non-increasing $f$ on $[P,\infty)$ with $\lim_{t	\to \infty} tf(t)=0$,
  $\sum_{p \geq P} f(p)\log p \leq (1+\frac{1}{914})\int_P^\infty f + \frac{Pf(P)}{914} + \frac{4Pf(P)}{\log^2 P}$. -/)
  (latexEnv := "theorem")]
theorem lemma_3_2_b : lemma_3_2_bound (1/914) 4 2 := by sorry

@[blueprint
  "thm:ramare2016-3-2-c"
  (title := "Ramaré 2016 Lemma 3.2c (via Dusart 2016)")
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
  (title := "Treviño 2012, sum of primes")
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
  (title := "Deléglise-Nicolas 2019, π₁ lower bound")
  (statement := /-- For $x \geq 905{,}238{,}547$,
  $\frac{3x^2}{20\log^4 x} \leq \pi_1(x) - \left(\frac{x^2}{2\log x} + \frac{x^2}{4\log^2 x} + \frac{x^2}{4\log^3 x}\right)$. -/)
  (latexEnv := "theorem")]
theorem theorem_a (x : ℝ) (hx : x ≥ 905238547) :
    3 * x ^ 2 / (20 * (log x) ^ 4) ≤
      pi_r 1 x - (x ^ 2 / (2 * log x) + x ^ 2 / (4 * (log x) ^ 2) +
        x ^ 2 / (4 * (log x) ^ 3)) := by sorry

@[blueprint
  "thm:dn-pi1-upper"
  (title := "Deléglise-Nicolas 2019, π₁ upper bound")
  (statement := /-- For $x \geq 110{,}117{,}910$,
  $\pi_1(x) - \left(\frac{x^2}{2\log x} + \frac{x^2}{4\log^2 x} + \frac{x^2}{4\log^3 x}\right) \leq \frac{107 x^2}{160\log^4 x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_b (x : ℝ) (hx : x ≥ 110117910) :
    pi_r 1 x - (x ^ 2 / (2 * log x) + x ^ 2 / (4 * (log x) ^ 2) +
        x ^ 2 / (4 * (log x) ^ 3)) ≤
      107 * x ^ 2 / (160 * (log x) ^ 4) := by sorry

@[blueprint
  "thm:dn-pi2-lower"
  (title := "Deléglise-Nicolas 2019, π₂ lower bound")
  (statement := /-- For $x \geq 1{,}091{,}239$,
  $-\frac{1069\, x^3}{648\log^4 x} \leq \pi_2(x) - \left(\frac{x^3}{3\log x} + \frac{x^3}{9\log^2 x} + \frac{x^3}{27\log^3 x}\right)$. -/)
  (latexEnv := "theorem")]
theorem theorem_c (x : ℝ) (hx : x ≥ 1091239) :
    -(1069 * x ^ 3 / (648 * (log x) ^ 4)) ≤
      pi_r 2 x - (x ^ 3 / (3 * log x) + x ^ 3 / (9 * (log x) ^ 2) +
        x ^ 3 / (27 * (log x) ^ 3)) := by sorry

@[blueprint
  "thm:dn-pi2-upper"
  (title := "Deléglise-Nicolas 2019, π₂ upper bound")
  (statement := /-- For $x \geq 60{,}173$,
  $\pi_2(x) - \left(\frac{x^3}{3\log x} + \frac{x^3}{9\log^2 x} + \frac{x^3}{27\log^3 x}\right) \leq \frac{11181\, x^3}{648\log^4 x}$. -/)
  (latexEnv := "theorem")]
theorem theorem_d (x : ℝ) (hx : x ≥ 60173) :
    pi_r 2 x - (x ^ 3 / (3 * log x) + x ^ 3 / (9 * (log x) ^ 2) +
        x ^ 3 / (27 * (log x) ^ 3)) ≤
      11181 * x ^ 3 / (648 * (log x) ^ 4) := by sorry

@[blueprint
  "thm:dn-pi3-upper"
  (title := "Deléglise-Nicolas 2019, π₃ upper bound")
  (statement := /-- For $x \geq 664$, $\pi_3(x) \leq 0.271\, x^4 / \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_e (x : ℝ) (hx : x ≥ 664) :
    pi_r 3 x ≤ 0.271 * x ^ 4 / log x := by sorry

@[blueprint
  "thm:dn-pi4-upper"
  (title := "Deléglise-Nicolas 2019, π₄ upper bound")
  (statement := /-- For $x \geq 200$, $\pi_4(x) \leq 0.237\, x^5 / \log x$. -/)
  (latexEnv := "theorem")]
theorem theorem_f (x : ℝ) (hx : x ≥ 200) :
    pi_r 4 x ≤ 0.237 * x ^ 5 / log x := by sorry

@[blueprint
  "thm:dn-pi5-upper"
  (title := "Deléglise-Nicolas 2019, π₅ upper bound")
  (statement := /-- For $x \geq 44$, $\pi_5(x) \leq 0.226\, x^6 / \log x$.
  (Note: the wiki page lists $x^5$ here, but the consistent pattern $x^{r+1}$ and the general bound require $x^6$.) -/)
  (latexEnv := "theorem")]
theorem theorem_g (x : ℝ) (hx : x ≥ 44) :
    pi_r 5 x ≤ 0.226 * x ^ 6 / log x := by sorry

@[blueprint
  "thm:dn-pir-general"
  (title := "Deléglise-Nicolas 2019, general π_r upper bound")
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
  (title := "Rosser 1938, p_n > n log n")
  (statement := /-- For $n \geq 2$, we have $p_n > n \log n$. -/)
  (latexEnv := "theorem")]
theorem p_n_gt_1 (n : ℕ) (hn : n ≥ 2) :
    nth_prime' n > n * log n := by sorry

@[blueprint
  "thm:rosser1938-pn-lower"
  (title := "Rosser 1938, lower bound on p_n")
  (statement := /-- For $n > 1$, we have $p_n > n(\log n + \log\log n - 10)$. -/)
  (latexEnv := "theorem")]
theorem p_n_gt_2 (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 10) := by sorry

@[blueprint
  "thm:rosser1938-pn-upper"
  (title := "Rosser 1938, upper bound on p_n")
  (statement := /-- For $n > 1$, we have $p_n < n(\log n + \log\log n + 8)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lt_2 (n : ℕ) (hn : n > 1) :
    nth_prime' n < n * (log n + log (log n) + 8) := by sorry

end Rosser1938

namespace Cipolla

blueprint_comment /-- Some results from \cite{cippola} -/

@[blueprint
  "thm:cipolla-pn-asym"
  (title := "Cipolla asymptotic expansion for p_n")
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
  (title := "Rosser 1941, lower bound on p_n")
  (statement := /-- For $n \geq 1$, we have $p_n > n(\log n + \log\log n - 4)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n ≥ 1) :
    nth_prime' n > n * (log n + log (log n) - 4) := by sorry

@[blueprint
  "thm:rosser1941-pn-upper"
  (title := "Rosser 1941, upper bound on p_n")
  (statement := /-- For $n \geq 1$, we have $p_n < n(\log n + \log\log n + 2)$. -/)
  (latexEnv := "theorem")]
theorem p_n_upper (n : ℕ) (hn : n ≥ 1) :
    nth_prime' n < n * (log n + log (log n) + 2) := by sorry

end Rosser1941


namespace RS_prime

blueprint_comment /-- Some results from \cite{rs-prime} -/

@[blueprint
  "thm:rs-1962-pn-lower"
  (title := "Rosser-Schoenfeld 1962, lower bound on p_n")
  (statement := /-- For $n > 1$, we have $p_n > n(\log n + \log\log n - 3/2)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 3 / 2) := by sorry

@[blueprint
  "thm:rs-1962-pn-upper"
  (title := "Rosser-Schoenfeld 1962, upper bound on p_n")
  (statement := /-- For $n > 19$, we have $p_n < n(\log n + \log\log n - 1/2)$. -/)
  (latexEnv := "theorem")]
theorem p_n_upper (n : ℕ) (hn : n > 19) :
    nth_prime' n < n * (log n + log (log n) - 1 / 2) := by sorry

end RS_prime

namespace Robin

blueprint_comment /-- Some results from \cite{robin} -/

@[blueprint
  "thm:robin1983-pn-lower"
  (title := "Robin 1983, lower bound on p_n")
  (statement := /-- For $n > 1$, we have $p_n > n(\log n + \log\log n - 1.0072629)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 1.0072629) := by sorry

@[blueprint
  "thm:robin1983-pn-lower-const1"
  (title := "Robin 1983, lower bound on p_n with constant 1 for small primes")
  (statement := /-- For $p_n \leq 10^{11}$, we have $p_n > n(\log n + \log\log n - 1)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower_const1 (n : ℕ) (hn : (nth_prime' n : ℝ) ≤ (10 : ℝ) ^ 11) :
    nth_prime' n > n * (log n + log (log n) - 1) := by sorry

end Robin

namespace MassiasRobin

blueprint_comment /-- Some results from \cite{massias-robin} -/

@[blueprint
  "thm:massias-robin1996-pn-lower"
  (title := "Massias-Robin 1996, lower bound on p_n with constant 1")
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
  (title := "Dusart 1999, lower bound on p_n")
  (statement := /-- For all $n > 1$, we have $p_n > n(\log n + \log\log n - 1)$. -/)
  (latexEnv := "theorem")]
theorem p_n_lower (n : ℕ) (hn : n > 1) :
    nth_prime' n > n * (log n + log (log n) - 1) := by sorry

@[blueprint
  "thm:dusart1999-pn-upper"
  (title := "Dusart 1999, upper bound on p_n")
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
  (title := "DeKoninck-Letendre 2020, upper bound for sum of log p_i")
  (statement := /-- For $k \geq 5$, we have
  $\sum_{i \leq k} \log p_i \leq k(\log k + \log\log k - 1/2)$. -/)
  (latexEnv := "theorem")]
theorem sum_log_prime (k : ℕ) (hk : k ≥ 5) :
    ∑ i ∈ Finset.Icc 1 k, log (nth_prime' i : ℝ) ≤
      k * (log k + log (log k) - 1 / 2) := by sorry

@[blueprint
  "thm:dekoninck-letendre2020-sum-loglog-prime"
  (title := "DeKoninck-Letendre 2020, lower bound for sum of log log p_i")
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

The results below are taken from https://tme-emt-wiki-gitlab-io-9d3436.gitlab.io/Art09.html -/
namespace Schoenfeld1976

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
theorem has_prime_in_interval (x : ℝ) (hx : x > 2010760) :
    HasPrimeInInterval (x*(1-1/15697)) (x/15697) := by sorry

end Schoenfeld1976

namespace RamareSaouter2003

@[blueprint
  "thm:ramare-saouter2003"
  (title := "Ramaré-Saouter 2003")
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
    HasPrimeInInterval (x*(1-1/76900000000)) (x/76900000000) := by sorry

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
  (title := "Ramaré-Saouter 2003 (2)")
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
