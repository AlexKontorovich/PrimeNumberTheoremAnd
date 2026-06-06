/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import Mathlib.Data.Complex.Basic

/-!
# Elementary complex domains

This file contains small named domains used by analytic number theory files.
-/

@[expose] public section

noncomputable section

namespace Complex

/-- Right half-plane domain Ω = { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := { s : ℂ | (1 / 2 : ℝ) < s.re }

theorem mem_Ω {s : ℂ} : s ∈ Ω ↔ (1 / 2 : ℝ) < s.re := Iff.rfl

end Complex
