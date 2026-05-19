import Lean.Meta.Eval
import Lean.Parser.Command
import Mathlib.Data.Nat.Count
import Mathlib.Algebra.Group.Nat.Even

/-
This file defines the `count_ofNat` simproc, which simplifies `Nat.count` expressions where the range is a literal.
-/

open Lean Meta in
unsafe def evalNatExpr (e : Expr) : MetaM (Option Nat) := do
  let ty ← inferType e
  let .const ``Nat _ := ty | return none
  let val ← Lean.Meta.evalExpr Nat (mkConst ``Nat) e
  return some val

open Lean Meta in
simproc_decl count_ofNat (Nat.count _ _) := fun e => do
  let some val ← unsafe evalNatExpr e | return .continue
  let result := mkNatLit val
  let proof ← mkDecideProof (← mkEq e result)
  return .done { expr := result, proof? := some proof }

lemma count_201_true_eq_201 : Nat.count (fun _ ↦ True) 201 = 201 := by
  simp only [count_ofNat]

lemma count_even_201_eq_101 : Nat.count Even 201 = 101 := by
  simp only [count_ofNat]

lemma count_even_2010_eq_1010 : Nat.count Even 2010 = 1005 := by
  simp only [count_ofNat]

/-- info: 'count_even_201_eq_101' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms count_even_201_eq_101
