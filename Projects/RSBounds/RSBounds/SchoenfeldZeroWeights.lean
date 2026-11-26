import RSBounds.SchoenfeldLaplacePhysical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The variable zero weights in Schoenfeld's Theorem 11

These are elementary identities and monotonicity statements for the exact
Phi_0/Phi_2 weights and Rosser derivative quotient used in (7.11)--(7.18).
-/

open Real Set MeasureTheory
open scoped Interval

namespace TernaryGoldbach.RSBounds.SchoenfeldZeroWeights

noncomputable def Phi (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-a / Real.log (t / 17)) / t ^ (m + 1)

noncomputable def PhiDerivative (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  Phi a m t * (a / Real.log (t / 17) ^ 2 - (m + 1)) / t

noncomputable def q (t : ℝ) : ℝ :=
  (0.137 + 0.443 / Real.log t) / (t * Real.log (t / (2 * Real.pi)))

theorem Phi_pos (a : ℝ) (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < Phi a m t := by
  unfold Phi
  positivity

theorem hasDerivAt_Phi (a : ℝ) (m : ℕ) {t : ℝ} (ht : 17 < t) :
    HasDerivAt (Phi a m) (PhiDerivative a m t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log (t / 17) := Real.log_pos (by linarith)
  have hi := hasDerivAt_id t
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t / 17)) (1 / t) t := by
    convert (hi.div_const 17).log (by positivity : t / 17 ≠ 0) using 1 <;> simp only [id_eq] <;> field_simp [ht0.ne']
  have he := ((hasDerivAt_const t (-a)).div hlog hl.ne').exp
  have hh := he.div (hi.pow (m + 1)) (by positivity : t ^ (m + 1) ≠ 0)
  convert hh using 1
  · rfl
  · simp only [PhiDerivative, Phi, id_eq, Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.neg_apply, neg_div, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, pow_succ]
    field_simp [ht0.ne', hl.ne']
    <;> ring

theorem PhiDerivative_zero_nonneg {a t : ℝ} (ht : 17 < t)
    (ha : Real.log (t / 17) ^ 2 ≤ a) : 0 ≤ PhiDerivative a 0 t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log (t / 17) := Real.log_pos (by linarith)
  have hquot : 1 ≤ a / Real.log (t / 17) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    simpa using ha
  unfold PhiDerivative
  norm_num only [Nat.cast_zero, zero_add]
  exact div_nonneg (mul_nonneg (Phi_pos a 0 ht0).le (by linarith)) ht0.le

theorem PhiDerivative_two_nonpos {a t : ℝ} (ht : 17 < t)
    (ha : a ≤ 2 * Real.log (t / 17) ^ 2) : PhiDerivative a 2 t ≤ 0 := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log (t / 17) := Real.log_pos (by linarith)
  have hquot : a / Real.log (t / 17) ^ 2 ≤ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hl)).mpr ha
  unfold PhiDerivative
  norm_num only [Nat.cast_ofNat]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (Phi_pos a 2 ht0).le (by linarith)) ht0.le

theorem q_nonneg {t : ℝ} (ht1 : 1 < t) (htπ : 2 * Real.pi < t) : 0 ≤ q t := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_pos ht1
  have hlogπ : 0 < Real.log (t / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div (by positivity)).mpr htπ)
  unfold q
  positivity

theorem q_antitone {l t : ℝ} (hl1 : 1 < l) (hlπ : 2 * Real.pi < l) (hlt : l ≤ t) :
    q t ≤ q l := by
  have hl0 : 0 < l := by linarith
  have ht0 : 0 < t := hl0.trans_le hlt
  have hll : 0 < Real.log l := Real.log_pos hl1
  have hllt : Real.log l ≤ Real.log t := Real.log_le_log hl0 hlt
  have hπ : 0 < 2 * Real.pi := by positivity
  have hlogl : 0 < Real.log (l / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div hπ).mpr hlπ)
  have hloglt : Real.log (l / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_le_log (div_pos hl0 hπ) (div_le_div_of_nonneg_right hlt hπ.le)
  have hnum : 0.137 + 0.443 / Real.log t ≤ 0.137 + 0.443 / Real.log l := by
    exact add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 0.443) hll hllt)
  have hnum0 : 0 ≤ 0.137 + 0.443 / Real.log l := by positivity
  have hden0 : 0 < l * Real.log (l / (2 * Real.pi)) := mul_pos hl0 hlogl
  have hden : l * Real.log (l / (2 * Real.pi)) ≤ t * Real.log (t / (2 * Real.pi)) :=
    mul_le_mul hlt hloglt hlogl.le ht0.le
  unfold q
  calc
    _ ≤ (0.137 + 0.443 / Real.log l) / (t * Real.log (t / (2 * Real.pi))) :=
      div_le_div_of_nonneg_right hnum (hden0.le.trans hden)
    _ ≤ _ := div_le_div_of_nonneg_left hnum0 hden0 hden

/-- The density factor in (7.14), before applying the Laplace integral bound. -/
theorem density_le_q {l t : ℝ} (hl1 : 1 < l) (hlπ : 2 * Real.pi < l) (hlt : l ≤ t) :
    Real.log (t / (2 * Real.pi)) / (2 * Real.pi) +
      (0.137 + 0.443 / Real.log t) / t ≤
      (1 / (2 * Real.pi) + q l) * Real.log (t / (2 * Real.pi)) := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log (t / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div (by positivity)).mpr (hlπ.trans_le hlt))
  have he : (0.137 + 0.443 / Real.log t) / t = q t * Real.log (t / (2 * Real.pi)) := by
    unfold q
    field_simp [ht0.ne', hlog.ne']
  rw [he]
  have hq := mul_le_mul_of_nonneg_right (q_antitone hl1 hlπ hlt) hlog.le
  convert add_le_add_left hq (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) using 1 <;> ring

end TernaryGoldbach.RSBounds.SchoenfeldZeroWeights
