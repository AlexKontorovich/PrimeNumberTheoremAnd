import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Basic

open Complex BigOperators Finset Nat Classical

open scoped ArithmeticFunction Interval

/-%%

In this file, we prove the Hadamard Factorization theorem for functions of finite order, and prove that the zeta function
is such.

%%-/
