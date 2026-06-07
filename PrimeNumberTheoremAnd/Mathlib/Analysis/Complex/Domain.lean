module

public import Mathlib.Data.Complex.Basic

/-!
# Elementary complex domains
-/

@[expose] public section

namespace Complex

/-- Right half-plane domain Ω = { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := { s : ℂ | (1 / 2 : ℝ) < s.re }

theorem mem_Ω {s : ℂ} : s ∈ Ω ↔ (1 / 2 : ℝ) < s.re := Iff.rfl

end Complex
