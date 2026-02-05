import Architect
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import PrimeNumberTheoremAnd.ZetaSummary

open Real
open ArithmeticFunction hiding log

blueprint_comment /--
\section{Definitions}
-/

blueprint_comment /--
In this section we define the basic types of primary estimates we will work with in the project.

-/

/-- The Chebyshev function ψ.  TODO: align this with notation used elsewhere in PNT+ -/
noncomputable def ψ (x : ℝ) : ℝ := Chebyshev.psi x


@[blueprint
  "Epsi-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_ψ(x) = |ψ(x) - x| / x$ -/)]
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) := A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1:ℝ)/(2:ℝ)))

@[blueprint
  "classical-bound-psi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_ψ$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_ψ(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]

  We say that it obeys a \emph{numerical bound} with parameter $ε(x_0)$ if for all $x \geq x_0$ we have
  \[ E_ψ(x) \leq ε(x_0). \]
  -/)]
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := Eψ.bound (ε x₀) x₀
