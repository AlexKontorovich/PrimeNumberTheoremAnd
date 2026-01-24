import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Defs

namespace PrimeGaps

structure Provider where
  X₀ : ℕ
  δ : ℝ → ℝ
  δ_nonneg:
    ∀ {x : ℝ}, (X₀ : ℝ) ≤ x → 0 ≤ δ x
  δ_strictly_decreasing:
    ∀ {x y : ℝ}, (X₀ : ℝ) ≤ x → (X₀ : ℝ) ≤ y → x < y → δ y < δ x
  delta_sixth_power_lt_sqrt:
    ∀ {x : ℝ}, (X₀ : ℝ) ≤ x →
      (δ x) ^ (6 : ℝ) < Real.sqrt x
  delta_twelfth_power_le_n_pow_3_div_2:
    ∀ {n : ℕ}, X₀ ≤ n →
      (δ (n : ℝ)) ^ 12 ≤ (n : ℝ)
  prime_in_Icc:
    ∀ {x : ℝ}, (X₀ : ℝ) ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * (1 + δ x)

namespace Provider

abbrev X₀R (P : Provider) : ℝ := (P.X₀ : ℝ)
@[simp] lemma X₀R_def (P : Provider) : P.X₀R = (P.X₀ : ℝ) := rfl

end Provider
end PrimeGaps
