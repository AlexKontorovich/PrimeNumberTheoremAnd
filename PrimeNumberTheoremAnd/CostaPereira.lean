import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{An inequality of Costa-Pereira}

We record here an inequality relating the Chebyshev functions $\psi(x)$ and $\theta(x)$ due to
Costa Pereira \cite{costa-pereira}, namely
$$ \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7}) \leq \psi(x) - \theta(x) \leq \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) . $$
-/

namespace CostaPereira

@[blueprint
  "costa-pereira-sublemma-1-1"
  (title := "Costa-Pereira Sublemma 1.1")
  (statement := /-- For every $x > 0$ we have $\psi(x) = \sum_{k \geqslant 1} \theta(x^{1/k})$. -/)
  (proof := /-- This follows directly from the definitions of $\psi$ and $\theta$. -/)
  (latexEnv := "sublemma")
  (discussion := 676)]
theorem sublemma_1_1 {x : ℝ} (hx : 0 < x) : ψ x = ∑' k, θ (x ^ (1 / (k:ℝ))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-2"
  (title := "Costa-Pereira Sublemma 1.2")
  (statement := /-- For every $x > 0$ and $n$ we have $\psi(x^{1/n}) = \sum_{k \geqslant 1} \theta(x^{1/nk})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and substitution.-/)
  (latexEnv := "sublemma")
  (discussion := 677)]
theorem sublemma_1_2 {x : ℝ} (hx : 0 < x) (n : ℝ) : ψ (x ^ (1 / n:ℝ)) = ∑' k, θ (x ^ (1 / (n * (k:ℝ)))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-3"
  (title := "Costa-Pereira Sublemma 1.3")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) = \theta(x) + \psi(x^{1/2}) + \sum_{k \geqslant 1} \theta(x^{1/(2k+1)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "sublemma")
  (discussion := 678)]
theorem sublemma_1_3 {x : ℝ} (hx : 0 < x) :
    ψ x = θ x + ψ (x ^ (1 / 2:ℝ)) + ∑' k, θ (x ^ (1 / (2 * (k:ℝ) + 1))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-4"
  (title := "Costa-Pereira Sublemma 1.4")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) = \psi(x^{1/2}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-3)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-1)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k+1)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-3} and rearranging the sum. -/)
  (latexEnv := "sublemma")
  (discussion := 679)]
theorem sublemma_1_4 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x =
      ψ (x ^ (1 / 2:ℝ)) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 3))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 1))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) + 1))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-5"
  (title := "Costa-Pereira Sublemma 1.5")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x^{1/3}) = \sum_{k \geqslant 1} \theta(x^{1/(6k-3)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-2} and substitution. -/)
  (latexEnv := "sublemma")
  (discussion := 680)]
theorem sublemma_1_5 {x : ℝ} (hx : 0 < x) :
    ψ (x ^ (1 / 3:ℝ)) =
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 3))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ)))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-6"
  (title := "Costa-Pereira Sublemma 1.6")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) = \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-1)}) - \sum_{k \geqslant 1} \theta(x^{1/(6k)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k+1)}).
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-4} and Sublemma \ref{costa-pereira-sublemma-1-5}. -/)
  (latexEnv := "sublemma")
  (discussion := 681)]
theorem sublemma_1_6 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x =
      ψ (x ^ (1 / 2:ℝ)) +
      ψ (x ^ (1 / 3:ℝ)) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) - 1))) -
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ)))) +
      ∑' k, θ (x ^ (1 / (6 * (k:ℝ) + 1))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-7"
  (title := "Costa-Pereira Sublemma 1.7")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/5k}
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$ is an increasing function. -/)
  (latexEnv := "sublemma")
  (discussion := 682)]
theorem sublemma_1_7 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤
      ψ (x ^ (1 / 2:ℝ)) +
      ψ (x ^ (1 / 3:ℝ)) +
      ∑' (k : ℕ), θ (x ^ (1 / (5 * (k:ℝ)))) := by sorry

@[blueprint
  "costa-pereira-sublemma-1-8"
  (title := "Costa-Pereira Sublemma 1.8")
  (statement := /-- For every $x > 0$ we have
  \[
  \psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/7k}
  \]
  -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$ is an increasing function. -/)
  (latexEnv := "sublemma")
  (discussion := 683)]
theorem sublemma_1_8 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥
      ψ (x ^ (1 / 2:ℝ)) +
      ψ (x ^ (1 / 3:ℝ)) +
      ∑' k, θ (x ^ (1 / (7 * (k:ℝ)))) := by sorry

@[blueprint
  "costa-pereira-theorem-1a"
  (title := "Costa-Pereira Theorem 1a")
  (statement := /-- For every $x > 0$ we have
  $\psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-7} and Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "theorem")
  (discussion := 684)]
theorem theorem_1a {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2:ℝ)) + ψ (x ^ (1 / 3:ℝ)) + ψ (x ^ (1 / 5:ℝ)) := by
  simpa only [sublemma_1_2 hx 5] using sublemma_1_7 hx

@[blueprint
  "costa-pereira-theorem-1b"
  (title := "Costa-Pereira Theorem 1b")
  (statement := /-- For every $x > 0$ we have
  $\psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7})$. -/)
  (proof := /-- Follows from Sublemma \ref{costa-pereira-sublemma-1-8} and Sublemma \ref{costa-pereira-sublemma-1-2}. -/)
  (latexEnv := "theorem")
  (discussion := 685)]
theorem theorem_1b {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥ ψ (x ^ (1 / 2:ℝ)) + ψ (x ^ (1 / 3:ℝ)) + ψ (x ^ (1 / 7:ℝ)) := by sorry

end CostaPereira
