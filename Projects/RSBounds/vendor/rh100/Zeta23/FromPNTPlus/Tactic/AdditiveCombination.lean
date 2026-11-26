module

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
/-
Lean 4.35 / current Mathlib compatibility adaptation: LinearCombinationPrime
was removed after its additive functionality moved to LinearCombination.
The only invocation in this 99-module closure combines eight equalities by
addition. Use Mathlib's current proof-producing tactic with abelian-group
normalization for that interface. No mathematical statement is changed.
-/
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

public meta section

macro "additive_combination" e:term : tactic =>
  `(tactic| linear_combination (norm := abel) ($e))
