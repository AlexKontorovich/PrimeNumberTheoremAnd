import RSBounds.BacklundCenter
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact root certificates and integral-test tails for the Backlund center. -/

open scoped BigOperators
open Finset MeasureTheory

namespace TernaryGoldbach.RSBounds.CenterNumerics

theorem norm_zeta_eq_tsum_rpow {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ = ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  have hc : riemannZeta (σ : ℂ) =
      Complex.ofReal (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ), Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.cpow_neg, one_div]
  rw [hc, Complex.norm_of_nonneg (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _))]

noncomputable def rpowSum (σ : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (n : ℝ) ^ (-σ) + rpowSum σ (n + 1) m

theorem rpowSum_eq (σ : ℝ) (n m : ℕ) :
    rpowSum σ n m = ∑ j ∈ Finset.range m, ((j + n : ℕ) : ℝ) ^ (-σ) := by
  induction m generalizing n with
  | zero => simp [rpowSum]
  | succ m ih =>
    simp [rpowSum, Finset.sum_range_succ', ih, Nat.add_assoc, add_comm, add_left_comm]

theorem zeta_tail_upper {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 0 < N) :
    ‖riemannZeta (σ : ℂ)‖ ≤
      rpowSum σ 1 N + (N : ℝ) ^ (1 - σ) / (σ - 1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
  have ht := anti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hN')
    (fun t ht => Real.rpow_nonneg (le_of_lt (hN'.trans ht)) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hN'] at ht
  have htail : (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      (N : ℝ) ^ (1 - σ) / (σ - 1) := by
    convert ht using 1
    rw [show -σ + 1 = 1 - σ by ring, show σ - 1 = -(1 - σ) by ring,
      div_neg, neg_div]
  rw [norm_zeta_eq_tsum_rpow hσ, hsum.tsum_eq_zero_add]
  rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [← hs1.sum_add_tsum_nat_add N, rpowSum_eq]
  exact add_le_add le_rfl htail

theorem zeta_partial_lower {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    rpowSum σ 1 N ≤ ‖riemannZeta (σ : ℂ)‖ := by
  rw [norm_zeta_eq_tsum_rpow hσ]
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [hsum.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add, rpowSum_eq]
  exact hs1.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem zeta_tail_lower {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    rpowSum σ 1 N + ((N + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤
      ‖riemannZeta (σ : ℂ)‖ := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hN' : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici ((N + 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN'.trans_le hx) hxy (by linarith)
  have ht := anti.integral_le_tsum_comp_add (N + 1) hsum
    (fun t ht => Real.rpow_nonneg (le_of_lt (hN'.trans ht)) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hN'] at ht
  have htail : ((N + 1 : ℕ) : ℝ) ^ (1 - σ) / (σ - 1) ≤
      ∑' n : ℕ, ((n + (N + 1) : ℕ) : ℝ) ^ (-σ) := by
    convert ht using 1
    rw [show -σ + 1 = 1 - σ by ring, show σ - 1 = -(1 - σ) by ring,
      div_neg, neg_div]
  rw [norm_zeta_eq_tsum_rpow hσ, hsum.tsum_eq_zero_add]
  rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add]
  have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := hsum.comp_injective (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [← hs1.sum_add_tsum_nat_add N, rpowSum_eq]
  apply add_le_add le_rfl
  simpa only [Nat.add_assoc] using htail

theorem rpow_root_identity {n p k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((n : ℝ) ^ (-(p : ℝ) / k)) ^ k = ((n : ℝ) ^ p)⁻¹ := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [div_mul_cancel₀ _ hk', Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]

theorem root_lower {n p k D b : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
    (hb : b ^ k * n ^ p ≤ D ^ k) :
    (b : ℝ) / D ≤ (n : ℝ) ^ (-(p : ℝ) / k) := by
  apply (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hk.ne').mp
  rw [div_pow, rpow_root_identity hn hk]
  have hn' : 0 < (n : ℝ) ^ p := pow_pos (by exact_mod_cast hn) _
  have hD' : 0 < (D : ℝ) ^ k := pow_pos (by exact_mod_cast hD) _
  rw [div_le_iff₀ hD', le_inv_mul_iff₀ hn']
  exact_mod_cast (by simpa [mul_comm] using hb : n ^ p * b ^ k ≤ D ^ k)

theorem root_upper {n p k D b : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
    (hb : D ^ k ≤ b ^ k * n ^ p) :
    (n : ℝ) ^ (-(p : ℝ) / k) ≤ (b : ℝ) / D := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity) hk.ne').mp
  rw [div_pow, rpow_root_identity hn hk]
  have hn' : 0 < (n : ℝ) ^ p := pow_pos (by exact_mod_cast hn) _
  have hD' : 0 < (D : ℝ) ^ k := pow_pos (by exact_mod_cast hD) _
  rw [le_div_iff₀ hD', inv_mul_le_iff₀ hn']
  exact_mod_cast (by simpa [mul_comm] using hb : D ^ k ≤ n ^ p * b ^ k)

def rootCheck (p k D n : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => decide (b ^ k * n ^ p ≤ D ^ k ∧ D ^ k ≤ (b + 1) ^ k * n ^ p) &&
      rootCheck p k D (n + 1) bs

theorem rootCheck_sound {p k D n : ℕ} (hn : 0 < n) (hk : 0 < k) (hD : 0 < D)
    {bs : List ℕ} (hc : rootCheck p k D n bs = true) :
    (bs.sum : ℝ) / D ≤ rpowSum ((p : ℝ) / k) n bs.length ∧
    rpowSum ((p : ℝ) / k) n bs.length ≤ ((bs.sum + bs.length : ℕ) : ℝ) / D := by
  induction bs generalizing n with
  | nil => simp [rpowSum]
  | cons b bs ih =>
    simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl, hu⟩ := ih (by omega) hc.2
    have hbl := root_lower hn hk hD hc.1.1
    have hbu := root_upper hn hk hD hc.1.2
    simp only [List.sum_cons, List.length_cons, rpowSum, Nat.cast_add, Nat.cast_one]
    rw [neg_div] at hbl hbu
    simp only [Nat.cast_add, Nat.cast_one, add_div] at hbu hu ⊢
    constructor <;> linarith

end TernaryGoldbach.RSBounds.CenterNumerics
