import Architect
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order

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
  "classical-bound-psi"
  (title := "Definition 1, FKS2")
  (statement := /--
  We say that $E_ψ$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_ψ(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  -/)]
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x

/-- May need to guard against junk value at s=1 -/
noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0 }

def WithTop.top_to_zero {α : Type*} [Zero α] (a : WithTop α) : α := match a with
| ⊤ => 0
| (some x) => x

noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).top_to_zero

@[blueprint
  "classical-zero-free-region"
  (title := "Section 1.1, FKS2")
  (statement := /-- We say that one has a classical zero-free region with parameter $R$ if $zeta(s)$ has no zeroes in the region $Re(s) \geq 1 - 1 / R * \log |\Im s|$ for $\Im(s) > 3$. -/)]
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) := ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 / (R * log t) → riemannZeta (σ + t * Complex.I) ≠ 0

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(T)")
  (statement := /-- The number of zeroes of imaginary part between 0 and T, counting multiplicity -/)]
noncomputable def riemannZeta.N (T : ℝ) : ℝ := ∑' ρ : { s:ℂ | s ∈ riemannZeta.zeroes ∧ 0 < s.im ∧ s.im < T }, riemannZeta.order ρ

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(σ,T)")
  (statement := /-- The number of zeroes of imaginary part between 0 and T, with real part greater than $\sigma$, counting multiplicity -/)]
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := ∑' ρ : { s:ℂ | s ∈ riemannZeta.zeroes ∧ 0 < s.re ∧ 0 < s.im ∧ s.im < T }, riemannZeta.order ρ

noncomputable def riemannZeta.R (b₁ b₂ b₃ T : ℝ) : ℝ := b₁ * log T + b₂ * log (log T) + b₃

@[blueprint
  "Riemann-von-Mangoldt-estimate"
  (title := "Riemann von Mangoldt estimate")
  (statement := /-- An estimate of the form $N(T) - \frac{T}{2\pi} \log \frac{T}{2\pi e} + \frac{7}{8}| ≤ b_1 \log T + b_2 \log\log T + b_3$ for $T \geq 2$. -/)]
def riemannZeta.Riemann_vonMangoldt_bound (b₁ b₂ b₃ : ℝ) : Prop :=
  ∀ T ≥ 2, |riemannZeta.N T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7/8)| ≤ R b₁ b₂ b₃ T

@[blueprint
  "zero-density-bound"
  (title := "Zero density bound")
  (statement := /-- An estimate of the form $N(\sigma,T) \leq c₁ T^p \log^q T + c₂ \log^2 T - \frac{T}{2\pi} \log \frac{T}{2\pi e} + \frac{7}{8}| ≤ b_1 \log T + b_2 \log\log T + b_3$ for $T \geq 2$. -/)]
def riemannZeta.zero_density_bound (T₀ σ c₁ c₂ p q : ℝ) : Prop :=
 ∀ T ≥ T₀,
    riemannZeta.N' σ T ≤ c₁ * T ^ p * (log T) ^ q + c₂ * (log T) ^ 2
