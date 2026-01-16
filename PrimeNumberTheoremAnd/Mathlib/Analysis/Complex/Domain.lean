import Mathlib.Data.Complex.Basic

noncomputable section

namespace RH.RS

/-- Right half-plane domain Ω = { s : ℂ | 1/2 < Re s }. -/
def Ω : Set ℂ := { s : ℂ | (1 / 2 : ℝ) < s.re }

end RH.RS
