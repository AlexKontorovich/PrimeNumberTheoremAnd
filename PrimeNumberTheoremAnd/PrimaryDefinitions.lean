import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.PrimesInAP

open ArithmeticFunction hiding log

/-%%
\section{Definitions}
%%-/

/-%%
In this section we define the basic types of primary estimates we will work with in the project.
%%-/

noncomputable def ψ (x : ℝ) : ℝ := ∑ᶠ (n : ℕ) (_: n < x), Λ n

noncomputable def PNT_error (x : ℝ) : ℝ := |ψ x - x|
