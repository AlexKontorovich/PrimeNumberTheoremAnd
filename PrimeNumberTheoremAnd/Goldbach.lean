import PrimeNumberTheoremAnd.SecondarySummary

blueprint_comment /--
\section{Numerical verification of Goldbach}\label{goldbach-sec}

We record here a simple way to convert prime in short interval theorems, together with numerical verification of even Goldbach, to numerical verification of odd Goldbach.

-/

namespace Goldbach

@[blueprint
  "even-goldbach"
  (title := "Even Goldbach conjecture up to a given height")
  (statement := /--
  We say that the even Goldbach conjecture is verified up to height $H$ if every even integer between $4$ and $H$ is the sum of two primes. -/)]
def even_conjecture (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 4 H, ∃ p q : ℕ, Prime p ∧ Prime q ∧ n = p + q

lemma even_conjecture_mono (H H' : ℕ) (h : even_conjecture H) (hh : H' ≤ H) : even_conjecture H' := by
  intro n hn; apply h; grind

@[blueprint
  "even-goldbach-test"
  (title := "Even Goldbach conjecture - unit test")
  (statement := /--
  The even Goldbach conjecture is verified up to height 30. -/)
  (proof := /-- This is a simple unit test, which can be verified by hand. -/)
  (latexEnv := "proposition")
  (discussion := 959)]
theorem even_goldbach_test : even_conjecture 30 := by
  sorry

@[blueprint
  "odd-goldbach"
  (title := "Odd Goldbach conjecture up to a given height")
  (statement := /--
  We say that the odd Goldbach conjecture is verified up to height $H$ if every odd integer between $5$ and $H$ is the sum of three primes. -/)]
def odd_conjecture (H : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 5 H, ∃ p q r : ℕ, Prime p ∧ Prime q ∧ Prime r ∧ n = p + q + r

lemma odd_conjecture_mono (H H' : ℕ) (h : odd_conjecture H) (hh : H' ≤ H) : odd_conjecture H' := by
  intro n hn; apply h; grind

@[blueprint
  "even-to-odd-goldbach-triv"
  (title := "Even Goldbach implies odd Goldbach")
  (statement := /--
  If the even Goldbach conjecture is verified up to height $H$, then the odd Goldbach conjecture is verified up to height $H+3$. -/)
  (proof := /-- If $n$ is an odd integer between $5$ and $H+3$, then $n-3$ is an even integer between $4$ and $H$, so we can write $n-3 = p + q$ for some primes $p$ and $q$, and hence $n = p + q + 3$. -/)
  (latexEnv := "proposition")
  (discussion := 960)]
theorem even_to_odd_goldbach_triv (H : ℕ) (h : even_conjecture H) : odd_conjecture (H + 3) := by sorry

theorem odd_goldbach_test : odd_conjecture 33 := even_to_odd_goldbach_triv 30 even_goldbach_test

@[blueprint
  "even-to-odd-goldbach"
  (title := "Even Goldbach plus PNT in short interval implies odd Goldbach")
  (statement := /--
  If every interval $(x(1-1/\Delta), x]$ contains a prime for $x \geq x_0$, the even Goldbach conjecture is verified up to height $H$, and the odd Goldbach conjecture is verified up to height $x_0+4$, then the odd Goldbach conjecture is verified up to height $(H-4)\Delta + 4$. -/)
  (proof := /-- If $x \leq x_0+4$ then we are done by hypothesis, so assume $x_0+4 < x \leq H\Delta$.  By hypothesis, there is a prime $p$ with $(x-4)(1-1/\Delta) < p \leq x-4$.  Then $x-p$ is even, at least $4$, and at most $(x-4)/\Delta + 4 \leq H$, so is the sum of two primes, giving the claim. -/)
  (latexEnv := "proposition")
  (discussion := 961)]
theorem even_to_odd_goldbach (x₀ H Δ : ℕ) -- may need some lower bounds on these parameters
  (hprime : ∀ x ≥ x₀, HasPrimeInInterval (x * (1 - 1 / Δ)) (x / Δ))
  (heven : even_conjecture H)
  (hodd : odd_conjecture (x₀ + 4)) :
  odd_conjecture ((H - 4) * Δ + 4) := by sorry

@[blueprint
  "richstein-even-goldbach"
  (title := "Richstein's verification of even Goldbach")
  (statement := /-- \cite{richstein}
  The even Goldbach conjecture is verified up to $4 \times 10^{14}$. -/)
  (proof := /-- Numerical verification. -/)
  (latexEnv := "proposition")]
theorem richstein_goldbach : even_conjecture (4 * 10 ^ 14) := by sorry

@[blueprint
  "ramare-saouter-odd-goldbach"
  (title := "Ramaré and Saouter's verification of odd Goldbach")
  (statement := /-- \cite[Corollary 1]{ramare-saouter}
  The odd Goldbach conjecture is verified up to $1.13256 \times 10^{22}$. -/)
  (proof := /-- Combine Proposition \ref{richstein-even-goldbach}, Proposition \ref{even-to-odd-goldbach-triv}, and Theorem \ref{thm:ramare-saouter2003}. -/)
  (latexEnv := "proposition")
  (discussion := 962)]
theorem ramare_saouter_odd_goldbach : odd_conjecture (113256 * 10 ^ 17) := by sorry

@[blueprint
  "e-silva-herzog-piranian-even-goldbach"
  (title := "e Silva--Herzog--Piranian verification of even Goldbach")
  (statement := /-- \cite{eSHP}
  The even Goldbach conjecture is verified up to $4 \times 10^{18}$. -/)
  (proof := /-- Numerical verification. -/)
  (latexEnv := "proposition")]
theorem e_silva_herzog_piranian_goldbach : even_conjecture (4 * 10 ^ 18) := by sorry

@[blueprint
  "helfgott-odd-goldbach-finite"
  (title := "Helfgott's verification of odd Goldbach for small $n$")
  (statement := /-- \cite[Appendix C]{helfgott-goldbach-arxiv}
  The odd Goldbach conjecture is verified up to $1.1325 \times 10^{26}$. -/)
  (proof := /-- Combine Proposition \ref{e-silva-herzog-piranian-even-goldbach}, Proposition \ref{even-to-odd-goldbach-triv}, and Theorem \ref{thm:ramare-saouter2003}. -/)
  (latexEnv := "proposition")
  (discussion := 969)]
theorem helfgott_odd_goldbach_finite : odd_conjecture (11325 * 10 ^ 22) := by sorry

blueprint_comment /-- The arguments in \cite[Appendix C]{helfgott-goldbach-arxiv} push the bound further than this, but require unpublished estimates of Ramare. However, similar arguments were established in \cite{kadiri-lumley}, and we present them here. -/

@[blueprint
  "e-silva-herzog-piranian-even-goldbach-ext"
  (title := "e Silva--Herzog--Piranian verification of even Goldbach (extended)")
  (statement := /-- \cite{eSHP}
  The even Goldbach conjecture is verified up to $4 \times 10^{18} + 4$. -/)
  (proof := /-- If $N = 4 \times 10^{18}$, use the fact that $211, 313, N-209, N-309$ are all prime. -/)
  (latexEnv := "proposition")]
theorem e_silva_herzog_piranian_goldbach_ext : even_conjecture (4 * 10 ^ 18 + 4) := by sorry

@[blueprint
  "kl-odd-goldbach-finite"
  (title := "Kadiri--Lumley's verification of odd Goldbach for small $n$")
  (statement := /-- \cite[Corollary 1.2]{kadiri-lumley}
  The odd Goldbach conjecture is verified up to $1966196911 \times 4 \times 10^{18}$. -/)
  (proof := /-- Combine Proposition \ref{e-silva-herzog-piranian-even-goldbach-ext}, Proposition \ref{even-to-odd-goldbach-triv}, and Theorem \ref{thm:prime_gaps_KL} with $x_0 = e^{60}$ and $\Delta = 1966090061$. -/)
  (latexEnv := "proposition")
  (discussion := 970)]
theorem kadiri_lumley_odd_goldbach_finite : odd_conjecture (1966196911 * 4 * 10 ^ 18) := by sorry




end Goldbach
