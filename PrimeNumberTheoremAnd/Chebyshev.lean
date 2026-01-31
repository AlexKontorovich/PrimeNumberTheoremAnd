import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{Chebyshev's estimates}\label{chebyshev-estimates-sec}

We record Chebyshev's estimates on $\psi$. The material here is adapted from the presentation of Diamond -/

namespace Chebyshev

open Real
open ArithmeticFunction hiding log

@[blueprint
  "cheby-def-T"
  (title := "The function $T$")
  (statement := /-- $T(x) := \sum_{n \leq x} \log n$. -/)]
noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

@[blueprint
  "cheby-T-upper"
  (title := "Upper bound on $T$")
  (statement := /-- For $x \geq 1$, we have $T(x) \leq x \log x - x + 1 + \log x$. -/)
  (proof := /-- Upper bound $\log n$ by $\int_n^{n+1} \log t\ dt$ for $n < x-1$ and by $\log x$ for $x-1 < n \leq x$ to bound
  $$T(x) \leq \int_1^x \log t\ dt + \log x$$
  giving the claim. -/)
  (latexEnv := "lemma")]
theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  sorry

@[blueprint
  "cheby-T-lower"
  (title := "Lower bound on $T$")
  (statement := /-- For $x \geq 1$, we have $T(x) \leq x \log x - x + 1 - \log x$. -/)
  (proof := /-- Drop the $n=1$ term. Lower bound $\log n$ by $\int_{n-1}^{n} \log t\ dt$ for $2 \leq n < x$ to bound
  $$T(x) \geq \int_1^{\lfloor x \rfloor} \log t\ dt \geq \int_1^x \log t\ dt - \log x $$
  giving the claim. -/)
  (latexEnv := "lemma")]
theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  sorry

@[blueprint
  "cheby-T-Lambda"
  (title := "Relating $T$ and von Mangoldt")
  (statement := /-- For $x \geq 0$, we have $T(x) = \sum_{n \leq x} \Lambda(n) \lfloor x/n \rfloor$. -/)
  (proof := /-- This follows from the identity $\log n = \sum_{d|n} \Lambda(d)$ and rearranging sums. -/)
  (latexEnv := "lemma")]
theorem T.eq_sum_Lambda (x : ℝ) (hx : 0 ≤ x) : T x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  sorry

@[blueprint
  "cheby-E"
  (title := "$E$ function")
  (statement := /-- If $\nu : \N \to \R$, let $E: \R \to \R$ denote the function $E(x):= \sum_m \nu(m) \lfloor x / m \rfloor$. -/)]
noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

@[blueprint
  "cheby-T-E"
  (title := "Relating a weighted sum of $T$ to an $E$-weighted sum of von Mangoldt")
  (statement := /-- If $\nu : \N \to \R$ is finitely supported, then
$$ \sum_m \nu(m) T(x/m) = \sum_{n \leq x} E(x/n) \Lambda(n).$$ -/)
  (latexEnv := "lemma")]
theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by sorry

open Finsupp in
@[blueprint
  "cheby-nu"
  (title := "Chebyshev's weight $\nu$")
  (statement := /-- $\nu = e_1 - e_2 - e_3 - e_5 + e_{30}$, where $e_n$ is the Kronecker delta at $n$. -/)
]
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

@[blueprint
  "cheby-nu-cancel"
  (title := "Cancellation property of $\nu$")
  (statement := /-- One has $\sum_n \nu(n)/n = 0$ -/)
  (proof := /-- This follows from direct computation. -/)
  (latexEnv := "lemma")]
theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by sorry

@[blueprint
  "cheby-E-1"
  (title := "$E$ initially constant")
  (statement := /-- One has $E(x)=1$ for $1 \leq x \leq 6$. -/)
  (proof := /-- This follows from direct computation. -/)
  (latexEnv := "lemma")]
theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Icc 1 6) : E ν x = 1 := by sorry

@[blueprint
  "cheby-E-periodic"
  (title := "$E$ is periodic")
  (statement := /-- One has $E(x+30) = E(x)$. -/)
  (proof := /-- This follows from direct computation. -/)
  (latexEnv := "lemma")]
theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by sorry

@[blueprint
  "cheby-E-val"
  (title := "$E$ lies between $0$ and $1$")
  (statement := /-- One has $0 \leq E(x) \leq 1$ for all $x \geq 0$. -/)
  (proof := /-- This follows from direct computation for $0 \leq x < 30$, and then by periodicity for larger $x$. -/)
  (latexEnv := "lemma")]
theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by sorry

@[blueprint
  "cheby-U-def"
  (title := "The $U$ function")
  (statement := /-- We define $U(x) := \sum_m \nu(m) T(x/m)$. -/)]
noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

@[blueprint
  "cheby-psi-lower"
  (title := "Lower bounding $\\psi$ by a weighted sum of $T$")
  (statement := /-- For any $x > 0$, one has $\psi(x) \geq \sum_m \nu(m) T(x/m)$. -/)
  (proof := /-- Use Lemma \ref{cheby-T-E} and Lemma \ref{cheby-E-val}. -/)
  (latexEnv := "proposition")]
theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by sorry

@[blueprint
  "cheby-psi-diff"
  (title := "Upper bounding a difference of $\\psi$ by a weighted sum of $T$")
  (statement := /-- For any $x > 0$, one has $\psi(x) - \psi(x/6) \leq \sum_m \nu(m) T(x/m)$. -/)
  (proof := /-- Use Lemma \ref{cheby-T-E}, Lemma \ref{cheby-E-val}, and Lemma \ref{cheby-E-1}. -/)
  (latexEnv := "proposition")]
theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by sorry

@[blueprint
  "a-def"
  (title := "The constant $a$")
  (statement := /-- We define $a := -\sum_m \nu(m) \log m / m$. -/)]
noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

@[blueprint
  "a-val"
  (title := "Numerical value of $a$")
  (statement := /-- We have $0.92129 \leq a \leq 0.92130$. -/)
  (latexEnv := "lemma")]
theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by sorry

@[blueprint
  "U-bounds"
  (title := "Bounds for $U$")
  (statement := /-- For $x \geq 1$, we have $|U(x) - ax| \leq 5(\log x + 1)$. -/)
  (proof := /-- Use Lemma \ref{cheby-T-upper}, Lemma \ref{cheby-T-lower}, the definition of $a$, and the triangle inequality -/)
  (latexEnv := "lemma")]
theorem U_bound (x : ℝ) (hx : 1 ≤ x) : |U x - a * x| ≤ 5 * (log x + 1) := by sorry

@[blueprint
  "psi-lower"
  (title := "Lower bound for $\\psi$")
  (statement := /-- For $x \geq 1$, we have $\psi(x) \geq ax - 5(\log x + 1)$. -/)
  (proof := /-- Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-lower}.-/)
  (latexEnv := "theorem")]
theorem psi_lower (x : ℝ) (hx : 1 ≤ x) : ψ x ≥ a * x - 5 * (log x + 1) := by sorry

@[blueprint
  "psi-diff-upper"
  (title := "Upper bound for $\\psi$ difference")
  (statement := /-- For $x \geq 1$, we have $\psi(x) - \psi(x/6) \leq ax + 5(\log x + 1)$. -/)
  (proof := /-- Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-upper}.-/)
  (latexEnv := "proposition")]
theorem psi_diff_upper (x : ℝ) (hx : 1 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * (log x + 1) := by sorry

@[blueprint
  "psi-upper"
  (title := "Upper bound for $\\psi$")
  (statement := /-- For $x \geq 1$, we have $\psi(x) \leq 6ax/5 + 5(\log 5 / \log 6 + 1)(\log x + 1)$. -/)
  (proof := /-- Iterate Lemma \ref{psi-diff-upper}.-/)
  (latexEnv := "theorem")]
theorem psi_upper (x : ℝ) (hx : 1 ≤ x) : ψ x ≤ 6 * a * x / 5 + 5 * (log 5 / log 6 + 1) * (log x + 1) := by sorry

@[blueprint
  "psi-upper-clean"
  (title := "Clean upper bound for $\\psi$")
  (statement := /-- For $x > 0$, we have $\psi(x) \leq 1.11 x$. -/)
  (proof := /-- For $x$ large enough, this follows from Theorem \ref{psi-upper}. For small $x$, this follows from direct computation.-/)
  (latexEnv := "theorem")]
theorem psi_upper_clean (x : ℝ) (hx : x > 0) : ψ x ≤ 1.11 * x := by sorry














end Chebyshev
