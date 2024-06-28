import Mathlib.Algebra.BigOperators.Finprod

variable {M : Type*} {α : Sort*} [CommMonoid M]

@[to_additive]
lemma finprod_cond_and {p q : Prop} [Decidable p] [Decidable q] {x : M} :
    ∏ᶠ (_ : p ∧ q), x = ∏ᶠ (_ : p) (_ : q), x := by
  simp only [finprod_eq_if]; split_ifs <;> tauto
