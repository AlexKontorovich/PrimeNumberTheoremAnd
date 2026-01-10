import Architect
import PrimeNumberTheoremAnd.PrimaryDefinitions
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

blueprint_comment /--
\section{A Lemma involving the M\"obius Function}
-/

blueprint_comment /--
In this section we establish a lemma involving sums of the M\"obius function.
-/

namespace MobiusLemma

open ArithmeticFunction

@[blueprint
  "Q-def"
  (title := "Q")
  (statement := /--  $Q(x)$ is the number of squarefree integers $\leq x$. -/)]
noncomputable def Q (x : ℝ) : ℕ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if Squarefree n then 1 else 0

@[blueprint
  "R-def"
  (title := "R")
  (statement := /--  $R(x) = Q(x) - x / \zeta(2)$. -/)]
noncomputable def R (x : ℝ) : ℝ := Q x - x / (riemannZeta 2).re

@[blueprint
  "M-def"
  (title := "M")
  (statement := /--  $M(x)$ is the summatory function of the M\"obius function. -/)]
noncomputable def M (x : ℝ) : ℤ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, moebius n

@[blueprint
  "mobius-lemma-1-sub"
  (title := "Mobius Lemma 1, initial step")
  (statement := /-- For any $x>0$,
$$Q(x) = \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right)$$
.-/)
 (proof := /--
We compute
$$Q(x) = \sum_{n\leq x} \sum_{d: d^2|n} \mu(d) = \sum_{k, d: k d^2\leq x} \mu(d)$$
giving the claim.-/)
  (latexEnv := "sublemma")]
theorem mobius_lemma_1_sub (x : ℝ) (hx : x > 0) :
  Q x = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, M (Real.sqrt (x / k)) := by sorry

@[blueprint
  "mobius-lemma-1"
  (title := "Mobius Lemma 1")
  (statement := /-- For any $x>0$,
\begin{equation}\label{eq:antenor}
R(x) = \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right) - \int_0^x M\left(\sqrt{\frac{x}{u}}\right) du.
\end{equation}
.-/)
 (proof := /--
The equality is immediate from Theorem \ref{mobius-lemma-1-sub} and exchanging the order of $\sum$ and $\int$, as is justified by
$\sum_n |\mu(n)|\int_0^{x/n^2} du \leq \sum_n x/n^2 < \infty$)
$$\int_0^x M\left(\sqrt{\frac{x}{u}}\right) du = \int_0^x \sum_{n\leq \sqrt{\frac{x}{u}}} \mu(n) du
=\sum_n \mu(n) \int_0^{\frac{x}{n^2}} du = x \sum_n \frac{\mu(n)}{n^2} = \frac{x}{\zeta(2)}.$$
  -/)
  (latexEnv := "lemma")]
theorem mobius_lemma_1 (x : ℝ) (hx : x > 0) :
  R x = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, M (Real.sqrt (x / k)) -
        ∫ u in 0..x, (M (Real.sqrt (x / u)) : ℝ) := by sorry

blueprint_comment /--
Since our sums start from $1$, the sum $\sum_{k\leq K}$ is empty for $K=0$.
-/

@[blueprint
  "mobius-lemma-2-sub-1"
  (title := "Mobius Lemma 2 - first step")
  (statement := /-- For any $K \leq x$,
$$
\sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right) = \sum_{k\leq K} M\left(\sqrt{\frac{x}{k}}\right)
+ \sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}} M\left(\sqrt{\frac{x}{k}}\right) du.
$$
.-/)
  (proof := /-- This is just splitting the sum at $K$. -/)
    (latexEnv := "sublemma")]
theorem mobius_lemma_2_sub_1 (x : ℝ) (hx : x > 0) (K : ℕ) (hK : (K : ℝ) ≤ x) :
  ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, M (Real.sqrt (x / k)) =
    ∑ k ∈ Finset.range (K + 1), M (Real.sqrt (x / k)) +
    ∑ k ∈ Finset.Ico (K + 1) (⌊x⌋₊ + 2),
      ∫ u in (k - 0.5)..(k + 0.5), (M (Real.sqrt (x / k)) : ℝ) := by sorry

@[blueprint
  "mobius-lemma-2-sub-2"
  (title := "Mobius Lemma 2 - second step")
  (statement := /-- For any $K \leq x$, for $f(u) = M(\sqrt{x/u})$,
\[\sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}} f(u) du = \int_{K+\frac{1}{2}}^{\lfloor x\rfloor + \frac{3}{2}} f(u) du
= \int_{K+\frac{1}{2}}^x f(u) du,\].-/)
  (proof := /-- This is just splitting the integral at $K$, since $f(u) = M(\sqrt{x/u}) = 0$ for $x>u$. -/)
    (latexEnv := "sublemma")]
theorem mobius_lemma_2_sub_2 (x : ℝ) (hx : x > 0) (K : ℕ) (hK : (K : ℝ) ≤ x) :
  let f : ℝ → ℝ := fun u ↦ (M (Real.sqrt (x / u)) : ℝ)
  ∑ k ∈ Finset.Ico (K + 1) (⌊x⌋₊ + 2),
    ∫ u in (k - 0.5)..(k + 0.5), f u = ∫ u in (K + 0.5)..(⌊x⌋₊ + 1.5), f u := by sorry

@[blueprint
  "mobius-lemma-2"
  (title := "Mobius Lemma 2")
  (statement := /-- For any $x>0$ and any integer $K\geq 0$,
\begin{equation}\label{eq:singdot}
\begin{aligned}
R(x) &= \sum_{k\leq K} M\left(\sqrt{\frac{x}{k}}\right)  -
\int_0^{K+\frac{1}{2}} M\left(\sqrt{\frac{x}{u}}\right) du \\
&-\sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}} \left(M\left(\sqrt{\frac{x}{u}}\right) -M\left(\sqrt{\frac{x}{k}}\right)\right) du
\end{aligned}
\end{equation}
.-/)
 (proof := /-- We split into two cases.
If $K>x$, the second line of \eqref{eq:singdot}
is empty, and the first one equals \eqref{eq:antenor}, by
$M(t)=0$ for $t<1$, so \eqref{eq:singdot} holds.

Now suppose that $K \leq x$. Then we combine Sublemma \ref{mobius-lemma-2-sub-1} and Sublemma \ref{mobius-lemma-2-sub-2} with Lemma \ref{mobius-lemma-1} to give the claim.
  -/)
    (latexEnv := "lemma")]
theorem mobius_lemma_2 (x : ℝ) (hx : x > 0) (K : ℕ) : R x =
  ∑ k ∈ Finset.range (K + 1), M (Real.sqrt (x / k)) -
  ∫ u in 0..(K + 0.5), (M (Real.sqrt (x / u)) : ℝ) -
  ∑ k ∈ Finset.Ico (K + 1) (⌊x⌋₊ + 2),
    ∫ u in (k - 0.5)..(k + 0.5), (M (Real.sqrt (x / u)) - M (Real.sqrt (x / k)) : ℝ) -
  2 * x *
    ∑ k ∈ Finset.Ico (K + 1) (⌊x⌋₊ + 1),
      ∫ t in Real.sqrt (x / (k + 0.5))..Real.sqrt (x / (k - 0.5)),
        ((M t - M (Real.sqrt (x / k))) : ℝ) / t ^ 3 := by sorry


end MobiusLemma
