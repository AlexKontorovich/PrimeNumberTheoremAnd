import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Real
open ArithmeticFunction hiding log

/-%%
\section{Definitions}
%%-/

/-%%
In this section we define the basic types of primary estimates we will work with in the project.

Key references:

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557
%%-/

/-- The Chebyshev function ψ.  TODO: align this with notation used elsewhere in PNT+ -/
noncomputable def ψ (x : ℝ) : ℝ := ∑ᶠ (n : ℕ) (_: n < x), Λ n

/-%%
\begin{definition}[Equation (2) of FKS2]\label{Epsi-def}\lean{Eψ}\leanok
 $E_ψ(x) = |ψ(x) - x| / x$
\end{definition}
%%-/
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

/-%%
\begin{definition}[Definition 1, FKS2]\label{classical bound}\lean{Eψ.classicalBound}\leanok
We say that $E_ψ$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
\[ E_ψ(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
\end{definition}
%%-/

def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ A * (log x / R) ^ B * exp (-C * (log x / R) ^ (1/2))

/-%%
\begin{definition}[Section 1.1, FKS2]\label{classical zero-free region}\lean{riemannZeta.classicalZeroFree}\leanok
We say that one has a classical zero-free region with parameter $R$ if $zeta(s)$ has no zeroes in the region $Re(s) \geq 1 - 1 / R * \log |\Im s|$ for $\Im(s) > 3$.
\end{definition}
%%-/

noncomputable def riemannZeta.classicalZeroFree (R : ℝ) := ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 / (R * log t) → riemannZeta (σ + t * Complex.I) ≠ 0
