import PrimeNumberTheoremAnd.PrimaryDefinitions


/-%%
\section{Definitions}
%%-/

/-%%
In this section we define the basic types of secondary estimates we will work with in the project.
%%-/

open Real

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)
