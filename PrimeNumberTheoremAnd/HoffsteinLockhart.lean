import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Analysis.Analytic.Meromorphic
import PrimeNumberTheoremAnd.EulerProducts.LSeries

open Complex BigOperators Finset Nat Classical

open scoped ArithmeticFunction Interval

/-%%

In this file, we use the Hoffstein-Lockhart construction to prove a zero-free region for zeta.

ZeroFreeRegion

Hoffstein-Lockhart + Goldfeld-Hoffstein-Liemann

%%-/
