import Mathlib

open Set Function

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  sorry

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  sorry

noncomputable def ChebyshevPsi (x : ℝ) : ℝ := (Finset.range (Nat.floor x)).sum ArithmeticFunction.vonMangoldt


theorem extracted_1 {SmoothingF : ℝ → ℝ} :
    ∃ (C : ℝ) (_ : 3 < C), ∀ (X : ℝ) (_ : C < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖(∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X)) - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by

  have : ∃ c, 0 < c ∧
    ∀ (ε x : ℝ), 0 < ε → 0 < x → x ≤ 1 - c * ε → Smooth1 SmoothingF ε x = 1 := sorry --Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₁, c₁_pos, hc₁⟩ := this

  have : ∃ c, 0 < c ∧
    ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c * ε ≤ x → Smooth1 SmoothingF ε x = 0 := sorry --Smooth1Properties_above suppSmoothingF
  obtain ⟨c₂, c₂_pos, hc₂⟩ := this

  let C : ℝ := c₁ + c₂ + 3
  have C_gt : 3 < C := sorry
  refine ⟨C, C_gt, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
  unfold ChebyshevPsi


  have vonManBnd (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ Real.log n := by
    sorry
  have smooth1BddAbove (n : ℕ) : Smooth1 SmoothingF ε (n / X) ≤ 1 := by
    sorry
  have smooth1BddBelow (n : ℕ) : Smooth1 SmoothingF ε (n / X) ≥ 0 := by
    sorry
  have smoothIs1 (n : ℕ) (n_le : n ≤ X * (1 - c₁ * ε)) :
    Smooth1 SmoothingF ε (↑n / X) = 1 := sorry -- hc₁ (ε := ε) (n / X) εpos ?_


  have smoothIs0 (n : ℕ) (n_le : X * (1 + c₂ * ε) ≤ n) := hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩

  sorry
