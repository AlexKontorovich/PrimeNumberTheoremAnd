import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
The scalar step from RS62 (3.29) and (3.14) to the prime-product bound used
for the totient estimate. The two analytic estimates remain explicit inputs.
This file does not prove the unrestricted totient theorem.
-/

namespace TernaryGoldbach.RSBounds
open Real

theorem rs62_totient_scalar {G t s : ℝ} (hG : 1 ≤ G) (hG' : G ≤ 1.7811)
    (ht : 6 ≤ t) (hs : t - 1 / (2 * t - 1) ≤ s) :
    G * (t + 1 / (2 * t)) < G * s + 2.50637 / s := by
  have ht0 : 0 < t := by linarith
  have hG0 : 0 < G := by linarith
  have hd0 : 0 < 2 * t - 1 := by linarith
  have hd : 1 / (2 * t - 1) ≤ 1 / 11 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  set u := t - 1 / (2 * t - 1) with hu
  have hu5 : 5 ≤ u := by dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hut : u ≤ t := sub_le_self _ (by positivity)
  have hus : u ≤ s := hs
  have hs0 : 0 < s := lt_of_lt_of_le hu0 hus
  have hfrac : t / (2 * t - 1) ≤ 6 / 11 := by
    rw [div_le_iff₀ hd0]; linarith
  have hsmall : G * (1 / (2 * t) + 1 / (2 * t - 1)) * u < 2.50637 := by
    have hnonneg : 0 ≤ G * (1 / (2 * t) + 1 / (2 * t - 1)) := by positivity
    calc
      G * (1 / (2 * t) + 1 / (2 * t - 1)) * u
          ≤ G * (1 / (2 * t) + 1 / (2 * t - 1)) * t :=
        mul_le_mul_of_nonneg_left hut hnonneg
      _ = G * (1 / 2 + t / (2 * t - 1)) := by field_simp
      _ ≤ 1.7811 * (1 / 2 + 6 / 11) := by gcongr
      _ < 2.50637 := by norm_num
  have hfirst : G * (t + 1 / (2 * t)) < G * u + 2.50637 / u := by
    have hh := (lt_div_iff₀ hu0).2 hsmall
    dsimp [u] at hh ⊢
    linarith
  have hmono : G * u + 2.50637 / u ≤ G * s + 2.50637 / s := by
    have hus25 : 25 ≤ u * s := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hG (mul_pos hu0 hs0).le
    have hprod : 2.50637 ≤ G * (u * s) := by nlinarith
    have hdiff : 0 ≤ (s - u) * (G * (u * s) - 2.50637) :=
      mul_nonneg (sub_nonneg.2 hus) (sub_nonneg.2 hprod)
    rw [← sub_nonneg]
    have heq : G * s + 2.50637 / s - (G * u + 2.50637 / u) =
        (s - u) * (G * (u * s) - 2.50637) / (u * s) := by field_simp; ring
    rw [heq]
    exact div_nonneg hdiff (mul_pos hu0 hs0).le
  exact hfirst.trans_le hmono

theorem rs62_primeProduct_bound_of_inputs {G x θ P : ℝ}
    (hG : 1 ≤ G) (hG' : G ≤ 1.7811) (hx : 0 < x) (hxlog : 6 ≤ log x)
    (hθ : x * (1 - 1 / (2 * log x)) ≤ θ)
    (hP : P < G * (log x + 1 / (2 * log x))) :
    P < G * log θ + 2.50637 / log θ := by
  have ht0 : 0 < log x := by linarith
  have hd0 : 0 < 2 * log x - 1 := by linarith
  have hv : 0 < 1 - 1 / (2 * log x) := by
    have hh : 1 / (2 * log x) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  have hlo := Real.log_le_log (mul_pos hx hv) hθ
  rw [Real.log_mul hx.ne' hv.ne'] at hlo
  have hlow := Real.one_sub_inv_le_log_of_pos hv
  have heq : 1 - (1 - 1 / (2 * log x))⁻¹ = -1 / (2 * log x - 1) := by
    field_simp
    <;> ring
  rw [heq] at hlow
  have hs : log x - 1 / (2 * log x - 1) ≤ log θ := by
    calc
      log x - 1 / (2 * log x - 1) = log x + (-1 / (2 * log x - 1)) := by ring
      _ ≤ log x + log (1 - 1 / (2 * log x)) := by
        simpa only [add_comm] using add_le_add_left hlow (log x)
      _ ≤ log θ := hlo
  exact hP.trans (rs62_totient_scalar hG hG' hxlog hs)

end TernaryGoldbach.RSBounds
