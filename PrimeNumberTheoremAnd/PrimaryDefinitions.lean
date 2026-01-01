import Architect
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Real
open ArithmeticFunction hiding log

blueprint_comment /--
\section{Definitions}
-/

blueprint_comment /--
In this section we define the basic types of primary estimates we will work with in the project.

Key references:

FKS1: Fiori--Kadiri--Swidninsky arXiv:2204.02588

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557
-/

/-- The Chebyshev function ψ.  TODO: align this with notation used elsewhere in PNT+ -/
noncomputable def ψ (x : ℝ) : ℝ := Chebyshev.psi x


@[blueprint
  "Epsi-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_ψ(x) = |ψ(x) - x| / x$ -/)]
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x



noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) := A * (log x / R) ^ B * exp (-C * (log x / R) ^ (1/2))

@[blueprint
  "classical-bound"
  (title := "Definition 1, FKS2")
  (statement := /--
  We say that $E_ψ$ satisfies a \emph{classical-bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_ψ(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  -/)]
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x



@[blueprint
  "classical zero-free region"
  (title := "Section 1.1, FKS2")
  (statement := /-- We say that one has a classical zero-free region with parameter $R$ if $zeta(s)$ has no zeroes in the region $Re(s) \geq 1 - 1 / R * \log |\Im s|$ for $\Im(s) > 3$. -/)]
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) := ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 / (R * log t) → riemannZeta (σ + t * Complex.I) ≠ 0
