import PsiFiniteIndependentStatements
import RSBounds.PsiFinite.Buthe

/-!
# Independent check of the finite ψ bounds: statements and axioms

The project's theorems must prove exactly the propositions elaborated in
`PsiFiniteIndependentStatements.lean`, which imports only Mathlib. Each `#print axioms` must list
only `propext`, `Classical.choice`, `Quot.sound`. See `verification/PsiFiniteIndependentCheck.md`.

Run, from `Projects/RSBounds`, after `lake build RSBounds.PsiFinite.Buthe` and after compiling
the statements file as its header says:

    lake env bash -c 'LEAN_PATH=/tmp/psi:$LEAN_PATH lean verification/PsiFiniteIndependentCheck.lean'
-/

open IndepPsiCheck

theorem check_T1 : T1 := fun _ h₁ h₂ => PsiFinite.psi_abs_sub_le_four_fifths_sqrt h₁ h₂

theorem check_T2 : T2 := fun _ h₁ h₂ => PsiFinite.psi_abs_sub_le_sqrt h₁ h₂

theorem check_B62 : B62 := fun _ h₁ h₂ => PsiFinite.buthe_eq_6_2_le_1e10 h₁ h₂

theorem check_T1sum : T1sum := T1sum_of_T1 check_T1

theorem check_T2sum : T2sum := T2sum_of_T2 check_T2

theorem check_B62sum : B62sum := B62sum_of_B62 check_B62

#print axioms check_T1
#print axioms check_T2
#print axioms check_B62
#print axioms check_T1sum
#print axioms check_T2sum
#print axioms check_B62sum
