import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Defs

namespace PrimeGaps

structure Provider where
  X₀ : ℕ
  δ : ℝ → ℝ
  h_X₀ : X₀ > 1
  δ_nonneg:
    ∀ {x : ℝ}, x ≥ (X₀ : ℝ) → 0 ≤ δ x
  δ_strictly_decreasing:
    ∀ {x y : ℝ}, (X₀ : ℝ) ≤ x → (X₀ : ℝ) ≤ y → x < y → δ y < δ x
  delta_sixth_power_lt_sqrt:
    ∀ {n : ℕ}, X₀ ^ 2 ≤ n →
      (δ (√(n : ℝ))) ^ (6 : ℝ) < Real.sqrt (n : ℝ)
  delta_twelfth_power_le_n_pow_3_div_2:
    ∀ {n : ℕ}, X₀ ^ 2 ≤ n →
      4 * (1 + δ (√(n : ℝ))) ^ 12 ≤ (n : ℝ) ^ (3 / 2 : ℝ)
  delta_ineq :
    ∀ {n : ℕ}, X₀ ^ 2 ≤ n →
      (∏ i : Fin 3,
          (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))
  prime_in_Icc:
    ∀ {x : ℝ}, (X₀ : ℝ) ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * (1 + δ x)


namespace Provider

abbrev X₀R (P : Provider) : ℝ := (P.X₀ : ℝ)
@[simp] lemma X₀R_def (P : Provider) : P.X₀R = (P.X₀ : ℝ) := rfl

end Provider
end PrimeGaps
