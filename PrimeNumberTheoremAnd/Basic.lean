import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.Analytic.Meromorphic

open Complex BigOperators Finset Nat Classical

open scoped ArithmeticFunction Interval

/-%%

In this file, we prove the Prime Number Theorem. Continuations of this project aim to extend
this work to primes in progressions (Dirichlet's theorem), Chebytarev's density theorem, etc
etc.

%%-/
/-- A `Rectangle` has corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪ [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → ℂ) (s : Set ℂ) : Prop := DifferentiableOn ℂ f s

/-- A function is `MeromorphicOnRectangle`  -/
class MeromorphicOnRectangle (f : ℂ → ℂ) (poles : Set ℂ) (z w : ℂ) : Prop where
  holomorphicOn : HolomorphicOn f ((Rectangle z w) ∩ polesᶜ)
  hasPoleAt : ∀ p ∈ poles, MeromorphicAt f p
  continuousOn : ContinuousOn f (RectangleBorder z w)
/-%%
Class MeromorphicOnRectangle (f)
Theorem ResidueOnRectangle
MellinTransform
Mellin Inversion (Goldfeld-Kontorovich)
ChebyshevPsi
ZeroFreeRegion
Hadamard Factorization
Hoffstein-Lockhart + Goldfeld-Hoffstein-Liemann
9-12 and 2-5 every day
DirichletSeries (NatPos->C)
RiemannZetaFunction
RectangleIntegral
ResidueTheoremOnRectangle
ArgumentPrincipleOnRectangle
Break rectangle into lots of little rectangles where f is holomorphic, and squares with center at a pole
HasPoleAt f z : TendsTo 1/f (N 0)
Equiv: TendsTo f atTop
Then locally f looks like (z-z_0)^N g
For all c sufficiently small, integral over big rectangle with finitely many poles is equal to rectangle integral localized at each pole.
Rectangles tile rectangles! (But not circles -> circles) No need for toy contours!



\begin{def}
The Chebyshev Psi function is defined as
$$
\psi(x) = \sum_{n \leq x} \Lambda(n),
$$
where $\Lambda(n)$ is the von Mangoldt function.
\end{def}
%%-/
noncomputable def ChebyshevPsi (x : ℝ) : ℝ := ∑ n in Finset.Ico (1 : ℕ) (Real.floor (x + 1)), Λ n

/-%%

Main Theorem: The Prime Number Theorem
\begin{theorem}[PrimeNumberTheorem]

%%-/
