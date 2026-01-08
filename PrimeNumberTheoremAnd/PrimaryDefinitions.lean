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

noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0 } -- Note that the junk value of zeta at s=1 is known to be nonzero

noncomputable def riemannZeta.zeroes_rect (I J : Set ℝ) : Set ℂ := { s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zeroes }

noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).untopD 0

noncomputable def riemannZeta.zeroes_sum {α : Type*} [RCLike α] (I J : Set ℝ) (f : ℂ → α) : α := ∑' ρ : riemannZeta.zeroes_rect I J, (f ρ) * (riemannZeta.order ρ)

noncomputable def riemannZeta.RH_up_to (T : ℝ) : Prop := ∀ ρ ∈ riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Ioo 0 T), ρ.re = 0.5

@[blueprint
  "classical-zero-free-region"
  (title := "Section 1.1, FKS2")
  (statement := /-- We say that one has a classical zero-free region with parameter $R$ if $zeta(s)$ has no zeroes in the region $Re(s) \geq 1 - 1 / R * \log |\Im s|$ for $\Im(s) > 3$. -/)]
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) := ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 - 1 / (R * log t) → riemannZeta (σ + t * Complex.I) ≠ 0

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(T)")
  (statement := /-- The number of zeroes of imaginary part between 0 and T, counting multiplicity -/)]
noncomputable def riemannZeta.N (T : ℝ) : ℝ := zeroes_sum Set.univ (Set.Ioo 0 T) (fun _ ↦ 1)

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(σ,T)")
  (statement := /-- The number of zeroes of imaginary part between 0 and T, with real part greater than $\sigma$, counting multiplicity -/)]
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1

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
structure zero_density_bound where
T₀ : ℝ
σ_range : Set ℝ
c₁ : ℝ → ℝ
c₂ : ℝ → ℝ
p : ℝ → ℝ
q : ℝ → ℝ
bound : ∀ T ≥ T₀, ∀ σ ∈ σ_range,
    riemannZeta.N' σ T ≤ (c₁ σ) * T ^ (p σ) * (log T) ^ (q σ) + (c₂ σ) * (log T) ^ 2

noncomputable def zero_density_bound.N {ZDB : zero_density_bound} (σ T : ℝ) : ℝ := (ZDB.c₁ σ) * T ^ (ZDB.p σ) * (log T) ^ (ZDB.q σ) + (ZDB.c₂ σ) * (log T) ^ 2
