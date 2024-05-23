/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# additive_combination Tactic

In this file, the `additive_combination` tactic is created.  This tactic, which
works over `AddGroup`s, attempts to simplify the target by creating a additive combination
of a list of equalities and subtracting it from the target.  This file also includes a
definition for `additive_combination_config`.  A `additive_combination_config`
object can be passed into the tactic, allowing the user to specify a
normalization tactic.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
lefthand side of the new goal and the lefthand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

set_option autoImplicit true

namespace Mathlib.Tactic.LinearCombination
open Lean hiding Rat
open Elab Meta Term

theorem pf_smul_c [SMul α β] {a b : α} (p : a = b) (c : β) : a • c = b • c := p ▸ rfl
theorem c_smul_pf [SMul α β] {b c : β} (p : b = c) (a : α) : a • b = a • c := p ▸ rfl
theorem smul_pf [SMul α β] {a₁ b₁ : α} (p₁ : (a₁:α) = b₁) {a₂ b₂ : β} (p₂ : a₂ = b₂) :
    a₁ • a₂ = b₁ • b₂ := p₁ ▸ p₂ ▸ rfl

/--
Performs macro expansion of a additive combination expression,
using `+`/`-`/`*`/`/` on equations and values.
* `some p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandAdditiveCombo (2 • h)` returns `some (c_add_pf 2 h)`
  which is a proof of `2 • a = 2 • b`.
* `none` means that the input expression is not an equation but a value;
  the input syntax itself is used in this case.
-/
partial def expandAdditiveCombo (stx : Syntax.Term) : TermElabM (Option Syntax.Term) := do
  let mut result ← match stx with
  | `(($e)) => expandLinearCombo e
  | `($e₁ + $e₂) => do
    match ← expandAdditiveCombo e₁, ← expandAdditiveCombo e₂ with
    | none, none => pure none
    | some p₁, none => ``(pf_add_c $p₁ $e₂)
    | none, some p₂ => ``(c_add_pf $p₂ $e₁)
    | some p₁, some p₂ => ``(add_pf $p₁ $p₂)
  | `($e₁ - $e₂) => do
    match ← expandAdditiveCombo e₁, ← expandAdditiveCombo e₂ with
    | none, none => pure none
    | some p₁, none => ``(pf_sub_c $p₁ $e₂)
    | none, some p₂ => ``(c_sub_pf $p₂ $e₁)
    | some p₁, some p₂ => ``(sub_pf $p₁ $p₂)
  | `(-$e) => do
    match ← expandAdditiveCombo e with
    | none => pure none
    | some p => ``(neg_pf $p)
  | `(← $e) => do
    match ← expandAdditiveCombo e with
    | none => pure none
    | some p => ``(Eq.symm $p)
  | `($e₁ • $e₂) => do
    match ← expandAdditiveCombo e₁, ← expandAdditiveCombo e₂ with
    | none, none => pure none
    | some p₁, none => ``(pf_smul_c $p₁ $e₂)
    | none, some p₂ => ``(c_smul_pf $p₂ $e₁)
    | some p₁, some p₂ => ``(smul_pf $p₁ $p₂)
  | e => do
    let e ← elabTerm e none
    let eType ← inferType e
    let .true := (← withReducible do whnf eType).isEq | pure none
    some <$> e.toSyntax
  return result.map fun r => ⟨r.raw.setInfo (SourceInfo.fromRef stx true)⟩

/-- Implementation of `additive_combination` and `additive_combination2`. -/
def elabAdditiveCombination
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e => withSynthesize do
    match ← expandAdditiveCombo e with
    | none => `(Eq.refl $e)
    | some p => pure p
  let norm := norm?.getD (Unhygienic.run `(tactic| ((try simp only [smul_add, smul_sub]); abel)))
  Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
    match exp? with
    | some n =>
      if n.getNat = 1 then `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
      else `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
    | _ => `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))


/--
`additive_combination` attempts to simplify the target by creating a additive combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a additive
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the additive combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `additive_combination e` is a additive combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `additive_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the additive combination.
  * The default normalization tactic is `abel`, which closes the goal or fails.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `additive_combination (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `additive_combination (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.
  This feature is not supported for `additive_combination2`.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  additive_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  additive_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  additive_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  additive_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  additive_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  additive_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  additive_combination 3 * h a b + hqc
```
-/
syntax (name := AdditiveCombination) "additive_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| additive_combination $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabAdditiveCombination tac n e
