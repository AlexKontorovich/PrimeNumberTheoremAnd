import Mathlib

open Set Function

open Finset (range)

open ArithmeticFunction

theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (hc₁ : ∀ (ε x : ℝ), 0 < ε → 0 < x → x ≤ 1 - c₁ * ε → Smooth1 SmoothingF ε x = 1) (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 1)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0) (C_gt' : 3 < c₁ + c₂ + 3) (C : ℝ)
    (C_eq : C = 2 * (c₁ + c₂ + 3)) (C_gt : 3 < C) (X : ℝ) (X_ge_C : C < X)
    (ε : ℝ) (εpos : 0 < ε) (ε_lt_one : ε < 1)
    (this_1 : 0 < X) (X_ne_zero : X ≠ 0) (n_on_X_pos : ∀ {n : ℕ}, 0 < n → 0 < ↑n / X)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) → Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
        ↑((Finset.range ⌊X + 1⌋₊).sum ⇑ArithmeticFunction.vonMangoldt)‖ ≤
    C * ε * X * Real.log X := by
  norm_cast

  let F := Smooth1 SmoothingF ε

  let n₀ := ⌊X * ((1 - c₁ * ε))⌋₊

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) := by
    apply Nat.floor_le
    bound

  have n₀_gt : X * ((1 - c₁ * ε)) - 1 ≤ n₀ := by
    simp only [tsub_le_iff_right]
    convert (Nat.lt_succ_floor _).le
    · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_left_inj, Nat.cast_inj, n₀]
    · exact FloorRing.toFloorSemiring

  have sumΛ : Summable (fun n ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (by trivial) ((le_div_iff₀ this_1).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by exact_mod_cast sumΛ.comp_injective fun Q=>by valid

  have : ∑' (n : ℕ), Λ n * F (n / X) =
    (∑ n ∈ Finset.range (n₀), Λ n * F (n / X)) +
    ∑' (n : ℕ),
      Λ (n + n₀ : ) * F ((n + n₀ : ) / X)
    := by
    rw[← sum_add_tsum_nat_add' (k := n₀)]
    norm_num[‹_›]

  rw [this]
  clear this

  let n₁ := ⌈X * (1 + c₂ * ε)⌉₊

  have n₁_ge : X * (1 + c₂ * ε) ≤ n₁ := by
    apply Nat.le_ceil

  have n₁_le : (n₁ : ℝ) < X * (1 + c₂ * ε) + 1 := by
    apply Nat.ceil_lt_add_one
    positivity

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
     exact (Nat.floor_mono (by nlinarith[mul_pos εpos this_1])).trans
      (Nat.floor_le_ceil _)

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ < X * ε * (c₂ + c₁) + 2 := by
    calc
      (n₁ : ℝ) - n₀ < X * (1 + c₂ * ε) + 1 - n₀ := by
                        exact sub_lt_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) + 1 - (X * (1 - c₁ * ε) - 1) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε) + 1)
       _            = X * ε * (c₂ + c₁) + 2 := by ring

  have : (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
    (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
    (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) := by
    rw[← sum_add_tsum_nat_add' (k := n₁ - n₀)]
    congr! 5
    · simp only [Nat.cast_add]
    · omega
    · congr! 1
      norm_cast
      omega
    · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega

  rw [this]
  clear this

  have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = 0 := by
    convert tsum_zero with n
    have : n₁ ≤ n + n₁ := by exact Nat.le_add_left n₁ n
    convert mul_zero _
    convert smoothIs0 (n + n₁) ?_
    exact (le_div_iff₀' this_1).mpr (n₁_ge.trans (Nat.cast_le.mpr this))

  rw [this]
  clear this

  have : ∑ x ∈ Finset.range ⌊X + 1⌋₊, Λ x =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) := by
    field_simp[add_comm _ n₀,n₀_le.trans,le_of_lt,n₀.le_floor,Finset.sum_range_add]
    rw [← Finset.sum_range_add,n₀.add_sub_of_le (Nat.floor_mono (by·linear_combination εpos*c₁*(X)))]

  rw [this]
  clear this

  have : ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases n_zero : n = 0
    · rw [n_zero]
      simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      convert smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range] at hn
      have : (n : ℝ) < n₀ := by exact_mod_cast hn
      linarith

  rw [this]
  clear this

  have :
    ∑ n ∈ Finset.range n₀, Λ n + (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) + 0) -
      (∑ x ∈ Finset.range n₀, Λ x + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀))
      =
      (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀)) := by
    ring

  rw [this]
  clear this

  have :
    ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) - ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀)‖
    ≤
    (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ := by
    exact (norm_sub_le_of_le ((norm_sum_le_of_le _) fun a s=>norm_mul_le _ _)) (norm_sum_le _ _)

  refine this.trans ?_

  clear this

  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    sorry

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by

    sorry

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤
    (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by

    sorry

  have := add_le_add bnd1 bnd2

  refine this.trans ?_

  clear this bnd1 bnd2



  sorry

  -- + ∑ n : ℕ in Icc (X * (1 + c₂ * ε)) ⌊X + 1⌋₊, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X) := by
  --   sorry
  -- sorry
