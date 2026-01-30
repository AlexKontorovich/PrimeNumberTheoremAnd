import Architect
import Mathlib

open ArithmeticFunction hiding log
open Finset Nat Real

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

blueprint_comment /--
We will want to treat very general additive and multiplicative functions, and set up the API for them.
So if we just use natural numbers for the domain, we will
eventually suffer when we, e.g., want to consider functions defined on ideals in number fields.
Thus we set up the definitions in a more general way.

Therefore we introduce a generalized `ArithmeticFunction` called `GenArithFunction`.
-/

@[blueprint
  "GenArithFunction"
  (statement := /-- Generalized arithmetic function on a type with multiplication and one. -/)]
abbrev GenArithFunction (N R : Type*) [Zero N] [Zero R] :=
  ZeroHom N R

variable {N R : Type*}

/-
We need to add an instance or something so that
we can automatically coerce `GenArithFunction N R` to a function `N → R`.
-/
@[blueprint
  "IsAdditive"
  (statement := /-- Additive function. -/)]
def IsAdditive [MonoidWithZero N] [AddZeroClass R] (f : GenArithFunction N R) : Prop :=
  ∀ {m n : N}, IsRelPrime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (statement := /-- Completely additive function. -/)]
def IsCompletelyAdditive [MulZeroOneClass R] :=
  MonoidWithZeroHom ℕ R
