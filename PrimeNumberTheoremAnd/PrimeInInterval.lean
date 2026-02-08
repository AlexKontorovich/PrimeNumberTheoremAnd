import PrimeNumberTheoremAnd.SecondaryDefinitions


blueprint_comment /--
\section{Converting prime number theorems to prime in short interval theorems}\label{short-sec}

In this section, bounds on $E_\theta$ are used to deduce the existence of primes in short intervals. (One could also proceed using $E_\pi$, but the bounds are messier and the results slightly weaker.)
-/

open Real

@[blueprint
  "pi-inc"
  (title := "Increase in pi iff prime in short interval")
  (statement := /--
  There is a prime in $(x, x+h]$ iff $\pi(x+h) > \pi(x)$.
  -/)
  (proof := /-- Both are equivalent to $\sum_{x < p \leq x+h} 1 > 0$.-/)
  (latexEnv := "lemma")]
lemma HasPrimeInInterval.iff_pi_ge (x h : ℝ) : HasPrimeInInterval x h ↔ pi (x + h) > pi x := by
  sorry

@[blueprint
  "theta-inc"
  (title := "Increase in theta iff prime in short interval")
  (statement := /--
  There is a prime in $(x, x+h]$ iff $\theta(x+h) > \theta(x)$.
  -/)
  (proof := /-- Both are equivalent to $\sum_{x < p \leq x+h} \log p > 0$.-/)
  (latexEnv := "lemma")]
lemma HasPrimeInInterval.iff_theta_ge (x h : ℝ) : HasPrimeInInterval x h ↔ θ (x + h) > θ x := by
  sorry

@[blueprint
  "etheta-pi"
  (title := "Upper bound on Etheta implies prime in short interval")
  (statement := /--
  There is a prime in $(x, x+h]$ if $x E_\theta(x) + (x+h) E_\theta(x+h) < h$. -/)
  (proof := /-- Lower bound $\theta(x+h) - \theta(x)$ using $\theta(x+h) \geq x+h (1 - E_\theta(x+h))$ and $\theta(x) \leq x (1 + E_\theta(x))$ and apply Lemma \ref{theta-inc}. -/)
  (latexEnv := "lemma")]
lemma Eθ.hasPrimeInInterval (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    x * Eθ x + (x + h) * Eθ (x + h) < h → HasPrimeInInterval x h := by
  sorry


@[blueprint
  "etheta-num-pi"
  (title := "Numerical bound on Etheta implies prime in short interval")
  (statement := /--
  If $E_\theta(x) \leq \varepsilon(x_0)$ for all $x \geq x_0$, and $(2x+h) \varepsilon(x_0)  < h$, then there is a prime in $(x, x+h]$. -/)
  (proof := /-- Apply Lemma \ref{etheta-pi}. -/)
  (latexEnv := "lemma")]
lemma Eθ.numericalBound.hasPrimeInInterval {x₀ x h : ℝ} {ε : ℝ → ℝ} (hEθ : Eθ.numericalBound x₀ ε) (hh : 0 < h) (hx : x₀ ≤ x) (hε : (2 * x + h) * ε x₀ < h) :
    HasPrimeInInterval x h := by
  sorry

@[blueprint
  "etheta-classical-pi"
  (title := "Classical bound on Etheta implies prime in short interval")
  (statement := /--
  If $E_\theta(x)$ enjoys a classical bound for all $x \geq x_0$, $x \geq \exp( R (2B/C)^2 )$ and $(2x+h) A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right) < h$, then there is a prime in $(x, x+h]$. -/)
  (proof := /-- Apply Lemma \ref{etheta-num-pi} and Lemma \ref{classical-to-numeric}. -/)
  (latexEnv := "lemma")]
lemma Eθ.classicalBound.hasPrimeInInterval {x₀ x h A B C R : ℝ} (hEθ : Eθ.classicalBound x₀ A B C R)
  (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hR : 0 < R) (hh : 0 < h) (hx : x₀ ≤ x) (hx' : x ≥ exp (R * (2 * B / C) ^ 2))
  (hb : (2 * x + h) * (admissible_bound A B C R x) < h) :
    HasPrimeInInterval x h := by
  sorry
