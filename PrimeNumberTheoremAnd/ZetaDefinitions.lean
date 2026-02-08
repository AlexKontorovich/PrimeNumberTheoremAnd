import Architect
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order
import PrimeNumberTheoremAnd.Defs

open Real

blueprint_comment /--
\section{Definitions}
-/

@[blueprint
  "zeroes-of-riemann-zeta"
  (statement := /--
    $\rho$ is understood to lie in the set $\{s: \zeta(s)=0\}$, counted with multiplicity. We will
    often restrict the zeroes $\rho$ to a rectangle $\{ \Re \rho \in I, \Im \rho \in J \}$, for
    instance through sums of the form $\sum_{\Re \rho \in  I, \Im \rho \in J} f(\rho)$.
  -/)]
-- Note that the junk value of zeta at s=1 is known to be nonzero
noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}

@[blueprint
  "zeroes-of-riemann-zeta"]
noncomputable def riemannZeta.zeroes_rect (I J : Set ℝ) : Set ℂ :=
    {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zeroes}

@[blueprint
  "zeroes-of-riemann-zeta"]
noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).untopD 0

@[blueprint
  "zeroes-of-riemann-zeta"]
noncomputable def riemannZeta.zeroes_sum {α : Type*} [RCLike α]
    (I J : Set ℝ) (f : ℂ → α) : α :=
    ∑' ρ : riemannZeta.zeroes_rect I J, (f ρ) * (riemannZeta.order ρ)

@[blueprint
  "RH-up-to"
  (statement := /--
    We say that the Riemann hypothesis has been verified up to height $T$ if there are no zeroes
    in the rectangle $\{ \Re \rho \in (0.5, 1), \Im \rho \in [0,T] \}$.
  -/)]
noncomputable def riemannZeta.RH_up_to (T : ℝ) : Prop :=
    IsEmpty (riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Icc 0 T))

@[blueprint
  "classical-zero-free-region"
  (title := "Section 1.1, FKS2")
  (statement := /--
    We say that one has a classical zero-free region with parameter $R$ if $zeta(s)$ has no zeroes
    in the region $Re(s) \geq 1 - 1 / R * \log |\Im s|$ for $\Im(s) > 3$.
  -/)]
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) :=
    ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 - 1 / (R * log t) →
    riemannZeta (σ + t * Complex.I) ≠ 0

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(T)")
  (statement := /--
    The number of zeroes of imaginary part between 0 and T, counting multiplicity
  -/)]
noncomputable def riemannZeta.N (T : ℝ) : ℝ := zeroes_sum Set.univ (Set.Ioo 0 T) (fun _ ↦ 1)

@[blueprint
  "zero-counting-function"
  (title := "Zero counting function N(σ,T)")
  (statement := /--
    The number of zeroes of imaginary part between 0 and T, with real part greater than $\sigma$,
    counting multiplicity
  -/)]
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1

@[blueprint
  "Riemann-von-Mangoldt-estimate"]
noncomputable def riemannZeta.RvM (b₁ b₂ b₃ T : ℝ) : ℝ := b₁ * log T + b₂ * log (log T) + b₃

@[blueprint
  "Riemann-von-Mangoldt-estimate"
  (title := "Riemann von Mangoldt estimate")
  (statement := /--
    An estimate of the form
    $N(T) - \frac{T}{2\pi} \log \frac{T}{2\pi e} + \frac{7}{8}| \leq b_1 \log T + b_2 \log\log T
    + b_3$ for $T \geq 2$.
  -/)]
def riemannZeta.Riemann_vonMangoldt_bound (b₁ b₂ b₃ : ℝ) : Prop :=
    ∀ T ≥ 2, |riemannZeta.N T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
      RvM b₁ b₂ b₃ T

@[blueprint
  "zero-density-bound"
  (title := "Zero density bound")
  (statement := /--
    An estimate of the form $N(\sigma,T) \leq c₁ T^p \log^q T + c₂ \log^2 T -
    \frac{T}{2\pi} \log \frac{T}{2\pi e} + \frac{7}{8}| \leq b_1 \log T + b_2 \log\log T + b_3$
    for $T \geq 2$.
  -/)]
structure zero_density_bound where
  T₀ : ℝ
  σ_range : Set ℝ
  c₁ : ℝ → ℝ
  c₂ : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  bound : ∀ T ≥ T₀, ∀ σ ∈ σ_range,
      riemannZeta.N' σ T ≤ (c₁ σ) * T ^ (p σ) * (log T) ^ (q σ) + (c₂ σ) * (log T) ^ 2

@[blueprint
  "zero-density-bound"]
noncomputable def zero_density_bound.N {ZDB : zero_density_bound} (σ T : ℝ) : ℝ :=
    (ZDB.c₁ σ) * T ^ (ZDB.p σ) * (log T) ^ (ZDB.q σ) + (ZDB.c₂ σ) * (log T) ^ 2
