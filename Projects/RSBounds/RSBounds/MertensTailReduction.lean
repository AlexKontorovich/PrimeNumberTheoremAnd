import TernaryGoldbach.Prelim.PNTMertens

/-!
# A centered tail estimate for the second Mertens error

This reuses the unconditional Mertens identity already ported from IEANTN.
The remaining analytic input is a uniform bound on the variation of `E₁Λ`
on the tail. No RH or Büthe hypothesis is used here.
-/

namespace TernaryGoldbach.RSBounds

open Real TernaryGoldbach.PNTMertens

/-- Centering the existing Mertens identity at `E₁Λ x` removes its boundary
term. The tail is integrable by the existing unconditional boundedness of
the first Mertens error. -/
theorem mertensError_eq_neg_centered_tail {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = - ∫ t in Set.Ioi x, (E₁Λ t - E₁Λ x) / (t * log t ^ 2) := by
  have hi : (∫ t in Set.Ioi x, (E₁Λ t - E₁Λ x) / (t * log t ^ 2)) =
      (∫ t in Set.Ioi x, E₁Λ t / (t * log t ^ 2)) - E₁Λ x / log x := by
    have heq : (fun t : ℝ ↦ (E₁Λ t - E₁Λ x) / (t * log t ^ 2)) =
        (fun t : ℝ ↦ E₁Λ t / (t * log t ^ 2) - E₁Λ x / (t * log t ^ 2)) := by
      funext t
      exact sub_div _ _ _
    rw [heq, MeasureTheory.integral_sub (integrable_E₁Λ_div_mul_log_sq hx)
      (integrable_const_div_mul_log_sq (E₁Λ x) hx),
      integ_div_mul_log_sq (E₁Λ x) hx]
  rw [hi, E₂Λ.eq hx]
  ring

/-- A variation bound centered at the initial value loses no factor two:
`|E₂Λ x| ≤ D/log x`. The variation hypothesis is an explicit, still needed
analytic input; this theorem does not assert an effective value of `D`. -/
theorem mertensError_abs_le_of_tail_variation {x D : ℝ} (hx : 2 ≤ x)
    (h : ∀ t, x < t → |E₁Λ t - E₁Λ x| ≤ D) :
    |E₂Λ x| ≤ D / log x := by
  rw [E₂Λ.eq hx]
  have hup : (∫ t in Set.Ioi x, E₁Λ t / (t * log t ^ 2)) ≤
      (E₁Λ x + D) / log x := by
    rw [← integ_div_mul_log_sq (E₁Λ x + D) hx]
    apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
      (integrable_const_div_mul_log_sq (E₁Λ x + D) hx) measurableSet_Ioi
    intro t ht
    have ht' : x < t := ht
    have ht0 : 0 < t := by linarith
    exact div_le_div_of_nonneg_right (by linarith [(abs_le.1 (h t ht')).2])
      (mul_nonneg ht0.le (sq_nonneg _))
  have hlo : (E₁Λ x - D) / log x ≤
      ∫ t in Set.Ioi x, E₁Λ t / (t * log t ^ 2) := by
    rw [← integ_div_mul_log_sq (E₁Λ x - D) hx]
    apply MeasureTheory.setIntegral_mono_on
      (integrable_const_div_mul_log_sq (E₁Λ x - D) hx)
      (integrable_E₁Λ_div_mul_log_sq hx) measurableSet_Ioi
    intro t ht
    have ht' : x < t := ht
    have ht0 : 0 < t := by linarith
    exact div_le_div_of_nonneg_right (by linarith [(abs_le.1 (h t ht')).1])
      (mul_nonneg ht0.le (sq_nonneg _))
  rw [add_div] at hup
  rw [sub_div] at hlo
  rw [abs_le]
  constructor <;> linarith

end TernaryGoldbach.RSBounds
