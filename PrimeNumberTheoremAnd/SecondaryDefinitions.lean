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
  (statement := /-- $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ and $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
noncomputable def li (x : ℝ) : ℝ := lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦ ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1-ε) (1+ε)), 1 / log t))

@[blueprint "li-def"]
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

@[blueprint
  "li_minus_Li"
  (title := "li minus Li")
  (statement := /-- $\li(x) - \Li(x) = \li(2)$. -/)
  (proof := /-- This follows directly from the definitions of $\li$ and $\Li$. -/)
  (latexEnv := "remark")]
theorem li.sub_Li
    (x : ℝ) (h2x : 2 ≤ x) :
    li x - Li x = li 2 := by
    sorry

@[blueprint
  "Ramanujan-Soldner-constant"
  (title := "Ramanujan-Soldner constant")
  (statement := /-- $\li(2) = 1.0451\dots$. -/)]
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
