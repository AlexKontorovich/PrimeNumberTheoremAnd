import Mathlib.NumberTheory.Chebyshev
import Architect


namespace Mertens

blueprint_comment /--
\section{Mertens' theorem}

In this section we give explicit versions of Mertens' theorems, with an aim to upstreaming these results to Mathlib.  In particular, the arguments here should be self-contained and written for efficiency, coherency, and clarity.  As such, extensive use of AI tools is \emph{strongly discouraged} in this section.

The arguments here are drawn from Leo Goldmakher's ``A quick proof of Mertens' theorem'' from https://web.williams.edu/Mathematics/lg5/mertens.pdf

-/

open Real
open ArithmeticFunction hiding log
open Finset

@[blueprint
  "Mertens-sum-log"
  (title := "Partial sum of logarithm identity")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n = x \log x - \{ x \} \log x - x + 1 + \int_1^x \{ t \} \frac{dt}{t} $$
 -/)
  (proof := /-- We have
\begin{align*}
\sum_{n \leq x} \log n &= \int_1^x \log t \, d\lfloor t \rfloor \\
&= \log x \cdot \lfloor x \rfloor - \int_1^x \frac{\lfloor t \rfloor}{t} dt \\
&= x \log x - \{ x \} \log x - \int_1^x \frac{t}{t} dt + \int_1^x \{ t \} \frac{dt}{t}.
 -/)
  (latexEnv := "lemma")]
theorem sum_log_eq (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - Nat.floor x) * log x - x + 1 + ∫ t in 1..x, (t - Nat.floor t) / t := by
  sorry

@[blueprint
  "Mertens-sum-log-le"
  (title := "Partial sum of logarithm upper bound")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n \leq x \log x.$$
 -/)
  (proof := /-- Trivial since $\log n \leq \log x$.
 -/)
  (latexEnv := "lemma")]
theorem sum_log_le (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x - x + 1 + log x := by
  sorry

#check Real.log_le_self

@[blueprint
  "Mertens-sum-log-ge"
  (title := "Partial sum of logarithm lower bound")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n \geq x \log x - 2 * x.$$
 -/)
  (proof := /-- Follows from the previous lemma and a crude bound $\log x \leq x$.
 -/)
  (latexEnv := "corollary")]
theorem sum_log_ge (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  sorry

@[blueprint
  "Mertens-sum-log-eq-sum-mangoldt"
  (title := "Partial sum of logarithm as sum of $\\Lambda(d)/d$")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n = \sum_{d \leq x} \Lambda(d) \lfloor \frac{x}{d} \rfloor.$$
-/)
  (proof := /-- We have
\begin{align*}
\sum_{n \leq x} \log n
&= \sum_{n \leq x} \sum_{d \mid n} \Lambda(d)
= \sum_{d \leq x} \Lambda(d) \sum_{n \leq x, d \mid n} 1
= \sum_{d \leq x} \Lambda(d) \left\lfloor \frac{x}{d} \right\rfloor.
\end{align*}
 -/)
  (latexEnv := "lemma")]
theorem sum_log_eq_sum_mangoldt (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) * (Nat.floor (x / d)) := by
    sorry

@[blueprint
  "Mertens-first-error-mangoldt"
  (title := "The remainder term in Mertens first theorem (von Mangoldt form)")
  (statement := /-- We define $E_{1,\Lambda}(x) := \sum_{d \leq x} \frac{\Lambda(d)}{d} - \log x$.
-/)]
noncomputable def E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

@[blueprint
  "Mertens-first-error-mangoldt-ge"
  (title := "Partial sum of $\\Lambda(d)/d$ lower bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,\Lambda}(x) \geq - 2.$$
-/)
  (proof := /-- Insert Lemma \ref{Mertens-sum-log-eq-sum-mangoldt} into Lemma \ref{Mertens-sum-log-ge} and lower bound $x/d$ by $\lfloor x/d \rfloor$.
  -/)
  (latexEnv := "corollary")]
theorem E₁Λ.ge (x : ℝ) (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
    sorry

#check Chebyshev.psi_le_const_mul_self

@[blueprint
  "Mertens-first-error-mangoldt-le"
  (title := "Partial sum of $\\Lambda(d)/d$ upper bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,\Lambda}(x) \leq \log 4 + 4.$$
-/)
  (proof := /-- Insert Lemma \ref{Mertens-sum-log-eq-sum-mangoldt} into Lemma \ref{Mertens-sum-log-le} and upper bound $x/d$ by $\lfloor x/d \rfloor + 1$, and use the Mathlib bound $\psi(x) \leq (\log 4 + 4) x$.
  -/)
  (latexEnv := "corollary")]
theorem E₁Λ.le (x : ℝ) (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
    sorry

@[blueprint
  "Mertens-first-error-prime"
  (title := "The remainder term in Mertens first theorem (prime form)")
  (statement := /-- We define $E_{1,p}(x) := \sum_{p \leq x} \frac{\log p}{p} - \log x$.
-/)]
noncomputable def E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

@[blueprint
  "Mertens-first-error-prime-le"
  (title := "Partial sum of $\\frac{\\log p}{p}$ upper bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,p}(x) \leq \log 4 + 4.$$
-/)
  (proof := /-- Drop all terms in Lemma \ref{Mertens-sum-mangoldt-div-le} arising from prime powers.
  -/)
  (latexEnv := "corollary")]
theorem E₁p.le (x : ℝ) (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    sorry

noncomputable def E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

@[blueprint
  "Mertens-first-error-prime-ge"
  (title := "Partial sum of $\\frac{\\log p}{p}$ lower bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,p}(x) \geq -2 - E_1$$
where
$$ E_1 := \sum_{p} \frac{\log p}{p(p-1)}. $$
-/)
  (proof := /-- Use the triangle inequality and the geometric series formula to estimate in Lemma \ref{Mertens-sum-mangoldt-div-le} arising from prime powers.
  -/)
  (latexEnv := "corollary")]
theorem E₁p.ge (x : ℝ) (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    sorry

blueprint_comment /-- TODO: find some explicit bound on $E_1$ that is easy to prove -/

@[blueprint
  "Mertens-second-constant-mangoldt"
  (title := "The constant term in Mertens second theorem (von Mangoldt form)")
  (statement := /-- We define $M_\Lambda := \int_2^\infty \frac{E_{1,\Lambda}(t)}{t \log^2 t} \, dt + 1 - \log \log 2$.
-/)]
noncomputable def MΛ : ℝ := ∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2) + 1 - log (log 2)

@[blueprint
  "Mertens-second-constant-mangoldt-ge"
  (title := "Upper bound for $M_\\Lambda$")
  (statement := /-- One has $M_\Lambda \leq \frac{\log 4 + 4}{\log 2} + 1 - \log \log 2$.
-/)
  (proof := /-- Insert Lemma \ref{Mertens-first-error-mangoldt-le} into the definition of $M_\Lambda$ and use the fact that $\int_2^\infty \frac{dt}{t \log^2 t} = 1/\log 2$.
  -/)
  (latexEnv := "corollary")]
theorem MΛ.ge : MΛ ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := by
    sorry

@[blueprint
  "Mertens-second-constant-mangoldt-le"
  (title := "Lower bound for $M_\\Lambda$")
  (statement := /-- One has $M_\Lambda \geq -\frac{2}{\log 2} + 1 - \log \log 2$.
-/)
  (proof := /-- Insert Lemma \ref{Mertens-first-error-mangoldt-ge} into the definition of $M_\Lambda$ and use the fact that $\int_2^\infty \frac{dt}{t \log^2 t} = 1/\log 2$.
  -/)
  (latexEnv := "corollary")]
theorem MΛ.le : MΛ ≥ -2 / log 2 + 1 - log (log 2) := by
    sorry

blueprint_comment /-- TODO: Show that $M_\Lambda = \gamma$ -/

@[blueprint
  "Mertens-second-error-mangoldt"
  (title := "The remainder term in Mertens second theorem (von Mangoldt form)")
  (statement := /-- We define $E_{2,\Lambda}(x) := \sum_{d \leq x} \frac{\Lambda(d)}{d \log d} - \log \log x - M_\Lambda$.
-/)]
noncomputable def E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - MΛ


@[blueprint
  "Mertens-second-error-mangoldt-eq"
  (title := "Integral form for second error (von Mangoldt form)")
  (statement := /-- For any $x \geq 2$, one has
$$ E_{2,\Lambda}(x) = \frac{E_{1,\Lambda}(x)}{\log x} - \int_x^\infty \frac{E_{1,\Lambda}(t)}{t \log^2 t}\ dt$$
-/)
  (proof := /--
\begin{align*}
\sum_{d \leq x} \frac{\Lambda(d)}{d \log d}
&= \int_{2^{-}}^{x} \frac{1}{\log t}\, d\bigl(\log t + E_{1,\Lambda}(t)\bigr) \\
&= \frac{\log x + E_{1,\Lambda}(x)}{\log x}
 + \int_{2}^{x} \frac{dt}{t\log t}
 + \int_{2}^{x} \frac{E_{1,\Lambda}(t)}{t\log^{2} t}\, dt \\
&= C + \frac{E_{1,\Lambda}(x)}{\log x} + \log \log x - \int_x^\infty \frac{E_{1,\Lambda}(t)}{t \log^2 t}\ dt.
\end{align*}
  -/)
  (latexEnv := "corollary")]
theorem E₂Λ.eq (x : ℝ) (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
    sorry

@[blueprint
  "Mertens-second-error-mangoldt-eq"
  (title := "Integral form for second error (von Mangoldt form)")
  (statement := /-- For any $x \geq 2$, one has
$$ |E_{2,\Lambda}(x)| \leq \frac{\log 4 + 6}{\log x}.$$
-/)
  (proof := /--
  Insert Lemma \ref{mertens-first-error-mangoldt-le} and Lemma \ref{mertens-first-error-mangoldt-ge} into Lemma \ref{Mertens-second-error-mangoldt-eq} and use the triangle inequality to obtain the required upper and lower bounds.
  -/)
  (latexEnv := "corollary")]
theorem E₂Λ.abs_le (x : ℝ) (hx : 2 ≤ x) :
    abs (E₂Λ x) ≤ (log 4 + 6) / log x := by
    sorry

@[blueprint
  "Mertens-second-constant-prime"
  (title := "The constant term in Mertens second theorem (prime form)")
  (statement := /-- We define $M_p := \int_2^\infty \frac{E_{1,p}(t)}{t \log^2 t} \, dt + 1 - \log \log 2$.  This constant is also known as the Meissel-Mertens constant. -/)]
noncomputable def M_p : ℝ := ∫ t in Set.Ioi 2, E₁p t / (t * log t^2) + 1 - log (log 2)

@[blueprint
  "Mertens-second-constant-prime-ge"
  (title := "Upper bound for $M_p$")
  (statement := /-- One has $M_p \leq \frac{\log 4 + 4}{\log 2} + 1 - \log \log 2$.
-/)
  (proof := /-- Insert Lemma \ref{Mertens-first-error-prime-le} into the definition of $M_p$ and use the fact that $\int_2^\infty \frac{dt}{t \log^2 t} = 1/\log 2$.
  -/)
  (latexEnv := "corollary")]
theorem M_p.ge : M_p ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := by
    sorry

@[blueprint
  "Mertens-second-constant-prime-le"
  (title := "Lower bound for $M_p$")
  (statement := /-- One has $M_p \geq -\frac{2 + E_1}{\log 2} + 1 - \log \log 2$.
-/)
  (proof := /-- Insert Lemma \ref{Mertens-first-error-prime-ge} into the definition of $M_p$ and use the fact that $\int_2^\infty \frac{dt}{t \log^2 t} = 1/\log 2$.
  -/)
  (latexEnv := "corollary")]
theorem M_p.le : M_p ≥ -(2 + E₁) / log 2 + 1 - log (log 2) := by
    sorry

@[blueprint
  "Mertens-second-error-mangoldt"
  (title := "The remainder term in Mertens second theorem (von Mangoldt form)")
  (statement := /-- We define $E_{2,p}(x) := \sum_{p \leq x} \frac{1}{p} - \log \log x - M_p$.
-/)]
noncomputable def E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, 1 / p - log (log x) - M_p


@[blueprint
  "Mertens-second-error-prime-eq"
  (title := "Integral form for second error (prime form)")
  (statement := /-- For any $x \geq 2$, one has
$$ E_{2,p}(x) = \frac{E_{1,p}(x)}{\log x} - \int_x^\infty \frac{E_{1,p}(t)}{t \log^2 t}\ dt$$
-/)
  (proof := /--
  Similar to Lemma \ref{Mertens-second-error-mangoldt-eq}.  (One may wish to unify these using some abstract lemma.)
  -/)
  (latexEnv := "corollary")]
theorem E₂p.eq (x : ℝ) (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
    sorry

@[blueprint
  "Mertens-second-error-prime-eq"
  (title := "Integral form for second error (prime form)")
  (statement := /-- For any $x \geq 2$, one has
$$ |E_{2,p}(x)| \leq \frac{\log 4 + 6 + E_1}{\log x}.$$
-/)
  (proof := /-- Similar to Lemma \ref{Mertens-second-error-prime-eq}.
  -/)
  (latexEnv := "corollary")]
theorem E₂p.abs_le (x : ℝ) (hx : 2 ≤ x) :
    abs (E₂p x) ≤ (log 4 + 6 + E₁) / log x := by
    sorry


blueprint_comment /-- TODO: Mertens' third theorem -/

end Mertens
