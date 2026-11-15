import RSBounds.Mertens
import RSBounds.MertensPsiAbel

/-! Finite signed-integral identities, separated from the infinite zero-potential proof. -/

open Real Filter MeasureTheory
open scoped Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensDLimit

open TernaryGoldbach.PNTMertens MertensPsiAbel

theorem E1_eq_mangoldtWeightedSum (x : ℝ) :
    E₁Λ x = mangoldtWeightedSum x - Real.log x := by
  have hs : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) / n) =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Λ n : ℝ) / n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
      exact ⟨Nat.zero_le _, hn.2⟩
    · intro n hn hnot
      have hn0 : n = 0 := by
        simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn hnot
        omega
      simp [hn0]
  exact congrArg (fun y : ℝ => y - Real.log x) hs

theorem D_eq_integral {x : ℝ} (hx : 1 ≤ x) :
    D x = ∫ t in 1..x, (Chebyshev.psi t - t) / t ^ 2 := by
  rw [D, E1_eq_mangoldtWeightedSum, mangoldtWeightedSum_eq_psi_div_add_integral hx,
    integral_psi_error_div_sq le_rfl hx, Real.log_one]
  ring

theorem D_sub_eq_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    D b - D a = ∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 := by
  have h := mangoldtWeightedSum_sub_log_eq_anchor ha hab
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  rw [sub_div, sub_div, div_self ha0, div_self hb0] at h
  rw [D, D, E1_eq_mangoldtWeightedSum, E1_eq_mangoldtWeightedSum]
  linarith

end TernaryGoldbach.RSBounds.MertensDLimit
