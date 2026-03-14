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

/-NOTE: Here one should make a predicate for this sort of estimate holding for specific thresholds of P and specific choices of epsilon, and then have different versions of `lemma_3_2` for the different numerical choices involved.

Let 𝑓 be a 𝐶1 non-negative, non-increasing function over [𝑃,∞), where 𝑃 ≥3 600 000 is a real number and such that lim𝑡→∞⁡𝑡⁢𝑓⁡(𝑡) =0. We have

∑𝑝≥𝑃𝑓⁡(𝑝)⁢log⁡𝑝 ≤(1 +𝜖)⁢∫∞
𝑃𝑓⁡(𝑡)𝑑𝑡 +𝜖⁢𝑃⁢𝑓⁡(𝑃) +𝑃⁢𝑓⁡(𝑃)/(5⁢log2⁡𝑃)

with 𝜖 =1/914. When we can only ensure 𝑃 ≥2, then a similar inequality holds, simply replacing the last 1/5 by 4.

The above result relies on (5.1*) of [Schoenfeld, 1976] because it is easily accessible. However on using Proposition 5.1 of [Dusart, 2016], one has access to 𝜖 =1/36260.
-/


end Ramare2016

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
