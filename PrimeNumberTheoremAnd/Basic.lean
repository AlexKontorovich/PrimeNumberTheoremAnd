import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ZetaFunction

open Complex BigOperators Finset Nat Classical

open scoped ArithmeticFunction

/-%%

In this file, we prove the Prime Number Theorem. We have plans to extend to primes in progressions (Dirichlet's theorem), Chebytarev's density theorem, etc etc.

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
