import Mathlib.NumberTheory.PrimeCounting

import PrimeNumberTheoremAnd.PrimaryDefinitions


/-%%
\section{Definitions}
%%-/

/-%%
In this section we define the basic types of secondary estimates we will work with in the project. Key references:

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557
%%-/

open Real Finset

/-- Standard arithmetic functions. TODO: align this with notation used elsewhere in PNT+ -/
noncomputable def pi (x : ℝ) : ℝ :=  Nat.primeCounting ⌊x⌋₊

noncomputable def li (x : ℝ) : ℝ := ∫ t in 0..x, 1 / log t

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def θ (x : ℝ) := ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, log p

/-%%
\begin{definition}[Equation (1) of FKS2]\label{Epi-def}\lean{Eπ}\leanok
 $E_π(x) = |π(x) - Li(x)| / Li(x)$
\end{definition}
%%-/
noncomputable def Eπ (x : ℝ) : ℝ := |pi x - Li x| / (x / log x)

/-%%
\begin{definition}[Equation (2) of FKS2]\label{Etheta-def}\lean{Eθ}\leanok
 $E_θ(x) = |θ(x) - x| / x$
\end{definition}
%%-/
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x

/-%%
\begin{definition}[Definition 1, FKS2]\label{classical bound'}\lean{Eθ.classicalBound, Eπ.classicalBound}\leanok
We say that $E_θ$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
\[ E_θ(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
Similarly for $E_π$.
\end{definition}
%%-/
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ A * (log x / R) ^ B * exp (-C * (log x / R) ^ (1/2))

def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ A * (log x / R) ^ B * exp (-C * (log x / R) ^ (1/2))

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ A * (log x) ^ B * exp (-C * (log x) ^ (3/5) / (log (log x)) ^ (1/5))

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε



def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)
