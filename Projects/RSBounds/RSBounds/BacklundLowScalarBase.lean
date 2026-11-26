import RSBounds.SmallTotientProduct
import RSBounds.WeightedZeroSums
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rational scalar certificates for the finite zero-count handoff

Every logarithm is enclosed using the already proved twelve-term artanh
checker. The only pi bounds used are Mathlib's `3.14 < pi < 22/7`.
The certificate checks below are statements of rational arithmetic.
-/

open Real

namespace TernaryGoldbach.RSBounds.BacklundLowScalar
open SmallTotientProduct

structure LogCert where
  k : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq

def LogCert.Valid (c : LogCert) : Prop := 0 < c.a ∧ 0 < c.b ∧ c.b ≤ c.a
instance (c : LogCert) : Decidable c.Valid := by unfold LogCert.Valid; infer_instance

def LogCert.ratio (c : LogCert) : ℚ := (2 : ℚ) ^ c.k * (1 + (c.b : ℚ) / c.a)
def LogCert.lower (c : LogCert) : ℚ :=
  ((c.k : ℚ) * qLo 1 1 + qLo c.a c.b) / (10 ^ 30 : ℚ)
def LogCert.upper (c : LogCert) : ℚ :=
  ((c.k : ℚ) * qHi 1 1 + qHi c.a c.b) / (10 ^ 30 : ℚ)

lemma LogCert.lower_nonneg (c : LogCert) : (0 : ℝ) ≤ (c.lower : ℝ) := by
  unfold LogCert.lower
  push_cast
  positivity

lemma LogCert.log_bounds {c : LogCert} (hc : c.Valid) :
    (c.lower : ℝ) ≤ Real.log (c.ratio : ℝ) ∧
      Real.log (c.ratio : ℝ) ≤ (c.upper : ℝ) := by
  have ha : (0 : ℝ) < c.a := by exact_mod_cast hc.1
  have hb : (0 : ℝ) < c.b := by exact_mod_cast hc.2.1
  have h1 := q_bounds hc.1 hc.2.1 hc.2.2
  have h2 := q_bounds (a := 1) (b := 1) (by decide) (by decide) (by decide)
  norm_num only [Nat.cast_one, div_one] at h2
  have hk : (0 : ℝ) ≤ c.k := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left h2.1 hk
  have hu := mul_le_mul_of_nonneg_left h2.2 hk
  have he : Real.log (c.ratio : ℝ) =
      (c.k : ℝ) * Real.log 2 + Real.log (1 + (c.b : ℝ) / c.a) := by
    unfold LogCert.ratio
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rw [he]
  unfold LogCert.lower LogCert.upper
  push_cast
  constructor
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 ^ 30)]
    nlinarith
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 30)]
    nlinarith

lemma LogCert.log_gt {c : LogCert} (hc : c.Valid) {l : ℚ} (hl : l < c.lower) :
    (l : ℝ) < Real.log (c.ratio : ℝ) :=
  (show (l : ℝ) < (c.lower : ℝ) by exact_mod_cast hl).trans_le (LogCert.log_bounds hc).1

structure MainCert where
  t : ℚ
  lower : LogCert
  upper : LogCert
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def MainCert.Valid (c : MainCert) : Prop :=
  c.lower.Valid ∧ c.upper.Valid ∧
  1 < c.lower.ratio ∧ 0 ≤ c.upper.ratio ∧
  c.lower.ratio * (44 / 7 : ℚ) ≤ c.t ∧
  c.t ≤ c.upper.ratio * (157 / 25 : ℚ) ∧
  c.lo < c.lower.ratio * c.lower.lower - c.upper.ratio + 7 / 8 ∧
  c.upper.ratio * c.upper.upper - c.lower.ratio + 7 / 8 < c.hi
instance (c : MainCert) : Decidable c.Valid := by unfold MainCert.Valid; infer_instance

lemma MainCert.sound {c : MainCert} (hc : c.Valid) :
    (c.lo : ℝ) < rosserF (c.t : ℝ) ∧ rosserF (c.t : ℝ) < (c.hi : ℝ) := by
  rcases hc with ⟨hlv, huv, hl1, hu0, hlt, hut, hlow, hupp⟩
  have hl1' : (1 : ℝ) < (c.lower.ratio : ℝ) := by exact_mod_cast hl1
  have hu0' : (0 : ℝ) ≤ (c.upper.ratio : ℝ) := by exact_mod_cast hu0
  have hlt' : (c.lower.ratio : ℝ) * (44 / 7) ≤ (c.t : ℝ) := by
    have hh : c.lower.ratio * 44 ≤ c.t * 7 := by linarith
    have hh' : (c.lower.ratio : ℝ) * 44 ≤ (c.t : ℝ) * 7 := by exact_mod_cast hh
    linarith
  have hut' : (c.t : ℝ) ≤ (c.upper.ratio : ℝ) * (157 / 25) := by
    have hh : c.t * 25 ≤ c.upper.ratio * 157 := by linarith
    have hh' : (c.t : ℝ) * 25 ≤ (c.upper.ratio : ℝ) * 157 := by exact_mod_cast hh
    linarith
  have hl0 : (0 : ℝ) < (c.lower.ratio : ℝ) := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hql : (c.lower.ratio : ℝ) ≤ (c.t : ℝ) / (2 * Real.pi) := by
    rw [le_div_iff₀ hp]
    have hπ : 2 * Real.pi ≤ (44 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    exact (mul_le_mul_of_nonneg_left hπ hl0.le).trans hlt'
  have hqu : (c.t : ℝ) / (2 * Real.pi) ≤ (c.upper.ratio : ℝ) := by
    rw [div_le_iff₀ hp]
    have hπ : (157 / 25 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_d2]
    exact hut'.trans (mul_le_mul_of_nonneg_left hπ hu0')
  have hq0 : (0 : ℝ) < (c.t : ℝ) / (2 * Real.pi) := hl0.trans_le hql
  have hll := (LogCert.log_bounds hlv).1
  have hlu := (LogCert.log_bounds huv).2
  have hlogl : (c.lower.lower : ℝ) ≤ Real.log ((c.t : ℝ) / (2 * Real.pi)) :=
    hll.trans (Real.log_le_log hl0 hql)
  have hlogu : Real.log ((c.t : ℝ) / (2 * Real.pi)) ≤ (c.upper.upper : ℝ) :=
    (Real.log_le_log hq0 hqu).trans hlu
  have hpL := mul_le_mul hql hlogl c.lower.lower_nonneg hq0.le
  have hpU := mul_le_mul hqu hlogu (Real.log_nonneg (hl1'.le.trans hql)) hu0'
  have hlo' : (c.lo : ℝ) < (c.lower.ratio : ℝ) * (c.lower.lower : ℝ) -
      (c.upper.ratio : ℝ) + 7 / 8 := by
    have hh : 8 * c.lo < 8 * (c.lower.ratio * c.lower.lower - c.upper.ratio) + 7 := by
      linarith
    have hh' : (8 : ℝ) * (c.lo : ℝ) <
        8 * ((c.lower.ratio : ℝ) * (c.lower.lower : ℝ) - (c.upper.ratio : ℝ)) + 7 := by
      exact_mod_cast hh
    linarith
  have hup' : (c.upper.ratio : ℝ) * (c.upper.upper : ℝ) -
      (c.lower.ratio : ℝ) + 7 / 8 < (c.hi : ℝ) := by
    have hh : 8 * (c.upper.ratio * c.upper.upper - c.lower.ratio) + 7 < 8 * c.hi := by
      linarith
    have hh' : (8 : ℝ) * ((c.upper.ratio : ℝ) * (c.upper.upper : ℝ) -
        (c.lower.ratio : ℝ)) + 7 < 8 * (c.hi : ℝ) := by exact_mod_cast hh
    linarith
  unfold rosserF
  constructor <;> linarith

end TernaryGoldbach.RSBounds.BacklundLowScalar
