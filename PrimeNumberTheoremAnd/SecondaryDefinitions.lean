import Architect
import Mathlib.NumberTheory.PrimeCounting

import PrimeNumberTheoremAnd.PrimaryDefinitions


blueprint_comment /--
\section{Definitions}
-/

blueprint_comment /--
In this section we define the basic types of secondary estimates we will work with in the project. Key references:

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557
-/

open Real Finset

/-- Standard arithmetic functions. TODO: align this with notation used elsewhere in PNT+ -/
noncomputable def pi (x : ℝ) : ℝ :=  Nat.primeCounting ⌊x⌋₊

noncomputable def li (x : ℝ) : ℝ := ∫ t in 0..x, 1 / log t

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def θ (x : ℝ) := Chebyshev.theta x


@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /-- $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| / \mathrm{Li}(x)$ -/)]
noncomputable def E_pi (x : ℝ) : ℝ := |pi x - Li x| / (x / log x)


@[blueprint
  "Etheta-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\theta(x) = |\theta(x) - x| / x$ -/)]
noncomputable def E_theta (x : ℝ) : ℝ := |θ x - x| / x


@[blueprint
  "classical-bound-1"
  (title := "Definition 1, FKS2")
  (statement := /--
  We say that $E_\theta$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  Similarly for $E_\pi$.
  -/)]
def E_theta.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, E_theta x ≤ admissible_bound A B C R x

@[blueprint
  "classical-bound-2"
  (title := "Definition 1, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  -/)]
def E_pi.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, E_pi x ≤ admissible_bound A B C R x

def E_pi.vinogradovBound (A B C x₀ : ℝ) : Prop := ∀ x ≥ x₀, E_pi x ≤ A * (log x) ^ B * exp (-C * (log x) ^ (3/5) / (log (log x)) ^ (1/5))

def E_pi.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, E_pi x ≤ ε

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)
