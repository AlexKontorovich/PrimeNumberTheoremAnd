import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.Analytic.Meromorphic
import PrimeNumberTheoremAnd.EulerProducts.LSeries

open Complex BigOperators Finset Nat Classical

open scoped ArithmeticFunction Interval

/-%%
\begin{definition}\label{ChebyshevPsi}\lean{ChebyshevPsi}\leanok
The Chebyshev Psi function is defined as
$$
\psi(x) = \sum_{n \leq x} \Lambda(n),
$$
where $\Lambda(n)$ is the von Mangoldt function.
\end{definition}
%%-/
noncomputable def ChebyshevPsi (x : ℝ) : ℝ := (Finset.range (Nat.floor x)).sum Λ

/-%%

Main Theorem: The Prime Number Theorem in strong form.
\begin{theorem}[PrimeNumberTheorem]\label{StrongPNT}\lean{PrimeNumberTheorem}
There is a constant $c > 0$ such that
$$
ψ (x) = x + O(x e^{-c \sqrt{\log x}})
$$
as $x\to \infty$.
\end{theorem}
%%-/
/-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`. -/
theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
    (ChebyshevPsi - id) =O[at_top] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by

  sorry
