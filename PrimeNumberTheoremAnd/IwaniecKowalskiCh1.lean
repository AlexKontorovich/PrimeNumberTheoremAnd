import Architect
import Mathlib

open ArithmeticFunction hiding log
open Finset Nat Real

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

variable {R : Type*}

@[blueprint
  "IsAdditive"
  (statement := /-- Additive function. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (statement := /-- Completely additive function. -/)]
def IsCompletelyAdditive [MulZeroOneClass R] :=
  MonoidWithZeroHom ℕ R
