import Architect
import Mathlib.Topology.Order.Basic
import Mathlib.NumberTheory.PrimeCounting

import PrimeNumberTheoremAnd.PrimaryDefinitions


blueprint_comment /--
\section{Definitions}
-/

blueprint_comment /--
In this section we define the basic types of secondary estimates we will work with in the project.
-/

open Real Finset

/- Standard arithmetic functions. TODO: align this with notation used elsewhere in PNT+ -/

@[blueprint
  "pi-def"
  (title := "pi")
  (statement := /-- $\pi(x)$ is the number of primes less than or equal to $x$. -/)]
noncomputable def pi (x : ℝ) : ℝ :=  Nat.primeCounting ⌊x⌋₊

open Topology

@[blueprint
  "li-def"
  (title := "li and Li")
  (statement := /-- $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ (in the principal value sense) and $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
noncomputable def li (x : ℝ) : ℝ := lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦ ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1-ε) (1+ε)), 1 / log t))

@[blueprint "li-def"]
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

@[blueprint
  "log_upper"
  (title := "Log upper bound")
  (statement := /-- For $t > -1$, one has $\log (1+t) \leq t$. -/)
  (proof := /-- This follows from the mean value theorem. -/)
  (latexEnv := "sublemma")]
theorem log_le
    (t : ℝ) (ht : t > -1) :
    log (1 + t) ≤ t := by
    sorry

@[blueprint
  "log_lower_1"
  (title := "First log lower bound")
  (statement := /-- For $t \geq 0$, one has $t - \frac{t^2}{2} \leq \log(1+t)$. -/)
  (proof := /-- Use Taylor's theorem with remainder and the fact that the second derivative of $\log(1+t)$ is at most $1$ for $t \geq 0$.-/)
  (latexEnv := "sublemma")]
theorem log_ge
    (t s : ℝ) (ht : t ≥ 0) (hs : s > 0) :
    t - t ^ 2 / (2 * s ^ 2) ≤ log (1 + t) := by
    sorry

@[blueprint
  "log_lower_2"
  (title := "Second log lower bound")
  (statement := /-- For $0 \leq t \leq t_0 < 1$, one has $\frac{t}{t_0} \log (1-t_0) \leq \log(1-t)$. -/)
  (proof := /-- Use concavity of log.-/)
  (latexEnv := "sublemma")]
theorem log_ge'
    (t t₀ : ℝ) (ht : 0 ≤ t) (ht0 : t ≤ t₀) (ht0' : t₀ < 1) :
    (t / t₀) * log (1 - t₀) ≤ log (1 - t) := by
    sorry

@[blueprint
  "symm_inv_log"
  (title := "Symmetrization of inverse log")
  (statement := /-- For $0 < t \leq 1/2$, one has $| \frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}| \leq \frac{\log(4/3)}{4/3}$. -/)
  (proof := /-- The expression can be written as $\frac{|\log(1-t^2)|}{|\log(1-t)| |\log(1+t)|}$. Now use the previous upper and lower bounds, noting that $t^2 \leq 1/4$. -/)
  (latexEnv := "sublemma")]
theorem symm_inv_log
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |1 / log (1 + t) + 1 / log (1 - t)| ≤ log (4 / 3) / (4 / 3) := by
    sorry

@[blueprint
  "li-approx"
  (title := "li approximation")
  (statement := /-- If $x \geq 2$ and $0 < \eps \leq 1$, then $\mathrm{li}(x) = \int_{[0,x] \backslash [-\eps, \eps]} \frac{dt}{\log t} + O_*( \frac{\log(4/3)}{4/3} \eps)$. -/)
  (proof := /-- Symmetrize the principal value integral around 1 using the previous lemma. -/)
  (latexEnv := "sublemma")
  ]
theorem li.eq
    (x ε : ℝ) (hx : x ≥ 2) (hε1 : 0 < ε) (hε2 : ε ≤ 1) : ∃ E,
    li x = ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)), 1 / log t + E ∧
    |E| ≤ log (4 / 3) / (4 / 3) * ε := by
    sorry

@[blueprint
  "li_minus_Li"
  (title := "li minus Li")
  (statement := /-- $\li(x) - \Li(x) = \li(2)$. -/)
  (proof := /-- This follows from the previous estimate. -/)
  (latexEnv := "remark")
  (discussion := 758)]
theorem li.sub_Li
    (x : ℝ) (h2x : 2 ≤ x) :
    li x - Li x = li 2 := by
    sorry

@[blueprint
  "Ramanujan-Soldner-constant"
  (title := "Ramanujan-Soldner constant")
  (statement := /-- $\li(2) = 1.0451\dots$. -/)
  (proof := /-- Use Sublemma \ref{li-approx} and some numerical integration. -/)
  (latexEnv := "lemma")
  (discussion := 759)]
theorem li.two_approx : li 2 ∈ Set.Icc 1.0451 1.0452 := by
  sorry


@[blueprint
  "theta-def"
  (title := "theta")
  (statement := /-- $\theta(x) = \sum_{p \leq x} \log p$ where the sum is over primes $p$. -/)]
noncomputable def θ (x : ℝ) := Chebyshev.theta x


@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /-- $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| / \mathrm{Li}(x)$ -/)]
noncomputable def Eπ (x : ℝ) : ℝ := |pi x - Li x| / (x / log x)


@[blueprint
  "Etheta-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\theta(x) = |\theta(x) - x| / x$ -/)]
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x


@[blueprint
  "classical-bound-theta"
  (title := "Definition 1, FKS2")
  (statement := /--
  We say that $E_\theta$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  Similarly for $E_\pi$.
  -/)]
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

@[blueprint "classical-bound-pi"
  (title := "Definition 1, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  -/)]
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ A * (log x) ^ B * exp (-C * (log x) ^ (3/5) / (log (log x)) ^ (1/5))

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)

@[blueprint
  "Meissel-Mertens-constant"
  (title := "Meissel-Mertens constant B")
  (statement := /--
  $B := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{1}{p} - \log \log x \right)$. -/)]
noncomputable def meisselMertensConstant : ℝ :=
  lim (Filter.atTop.comap (fun x : ℝ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.range ⌊x⌋₊), 1 / p - log (log x)))

@[blueprint
  "Mertens-constant"
  (title := "Mertens constant E")
  (statement := /--
  $E := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{\log p}{p} - \log x \right)$. -/)]
noncomputable def mertensConstant : ℝ :=
  lim (Filter.atTop.comap (fun x : ℝ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.range ⌊x⌋₊), Real.log p / p - log x))
