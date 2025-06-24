/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis, Patrick Massot
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Rify
import Config.Cify.Attr

/-!
# `cify` tactic

Adaptation of the Mathlib4 `rify` tactic
-/

namespace Mathlib.Tactic.Cify

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic

/--
The `cify` tactic is used to shift propositions from `ℕ`, `ℤ` or `ℚ` to `ℂ`.
Although less useful than its cousins `zify`, `qify` and `rify`, it can be useful when your
goal or context already involves complex numbers.

`cify` makes use of the `@[zify_simps]`, `@[qify_simps]`, `@[rify_simps]` and `@[cify_simps]`
attributes to move propositions, and the `push_cast` tactic to simplify the `ℂ`-valued expressions.
-/
syntax (name := cify) "cify" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| cify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp -decide only [zify_simps, qify_simps, rify_simps, cify_simps, push_cast, $args,*]
      $[at $location]?)

@[cify_simps] lemma ofReal_eq (a b : ℝ) : a = b ↔ (a : ℂ) = (b : ℂ) := by simp
@[cify_simps] lemma ofReal_ne (a b : ℝ) : a ≠ b ↔ (a : ℂ) ≠ (b : ℂ) := by simp

@[cify_simps] lemma ofNat_real_complex (a : ℕ) [a.AtLeastTwo] :
    ((ofNat(a) : ℝ) : ℂ) = (ofNat(a) : ℂ) := rfl

end Mathlib.Tactic.Cify
