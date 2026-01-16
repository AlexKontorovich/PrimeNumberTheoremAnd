import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace PrimeGaps

structure Provider where
  X₀ : ℕ
  δ : ℝ → ℝ
  prime_in_Icc:
    ∀ {x : ℝ}, (X₀ : ℝ) ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * (1 + δ x)

namespace Provider

abbrev X₀R (P : Provider) : ℝ := (P.X₀ : ℝ)
@[simp] lemma X₀R_def (P : Provider) : P.X₀R = (P.X₀ : ℝ) := rfl

end Provider
end PrimeGaps
