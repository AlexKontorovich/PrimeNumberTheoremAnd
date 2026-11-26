import RSBounds.BacklundLowScalarBase
import RSBounds.Mertens
import RSBounds.Targets
import TernaryGoldbach.Prelim.PNTMertens

/-!
# Elementary finite certificates for the RS62 weighted Mertens lower bound

The coarse bound `mertensE < -1.3` uses only Euler's constant and the first
10 prime terms of the convergent defining sum. The block reduction allows
finite rational log certificates to cover real intervals, with the final
RS62 constant kept in the conclusion. No prime-number estimate is used.
-/

open Finset Real

namespace TernaryGoldbach.RSBounds.MertensFiniteScalars

open BacklundLowScalar TernaryGoldbach.PNTMertens

private theorem log_2_lower : (693 / 1000 : ℝ) < Real.log 2 := by
  let c : LogCert := ⟨0, 1, 1⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (693 / 1000 : ℚ) < c.lower := by
    change (693 / 1000 : ℚ) < (LogCert.mk 0 1 1).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_3_lower : (1098 / 1000 : ℝ) < Real.log 3 := by
  let c : LogCert := ⟨1, 2, 1⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (1098 / 1000 : ℚ) < c.lower := by
    change (1098 / 1000 : ℚ) < (LogCert.mk 1 2 1).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_5_lower : (1609 / 1000 : ℝ) < Real.log 5 := by
  let c : LogCert := ⟨2, 4, 1⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (1609 / 1000 : ℚ) < c.lower := by
    change (1609 / 1000 : ℚ) < (LogCert.mk 2 4 1).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_7_lower : (1945 / 1000 : ℝ) < Real.log 7 := by
  let c : LogCert := ⟨2, 4, 3⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (1945 / 1000 : ℚ) < c.lower := by
    change (1945 / 1000 : ℚ) < (LogCert.mk 2 4 3).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_11_lower : (2397 / 1000 : ℝ) < Real.log 11 := by
  let c : LogCert := ⟨3, 8, 3⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (2397 / 1000 : ℚ) < c.lower := by
    change (2397 / 1000 : ℚ) < (LogCert.mk 3 8 3).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_13_lower : (2564 / 1000 : ℝ) < Real.log 13 := by
  let c : LogCert := ⟨3, 8, 5⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (2564 / 1000 : ℚ) < c.lower := by
    change (2564 / 1000 : ℚ) < (LogCert.mk 3 8 5).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_17_lower : (2833 / 1000 : ℝ) < Real.log 17 := by
  let c : LogCert := ⟨4, 16, 1⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (2833 / 1000 : ℚ) < c.lower := by
    change (2833 / 1000 : ℚ) < (LogCert.mk 4 16 1).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_19_lower : (2944 / 1000 : ℝ) < Real.log 19 := by
  let c : LogCert := ⟨4, 16, 3⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (2944 / 1000 : ℚ) < c.lower := by
    change (2944 / 1000 : ℚ) < (LogCert.mk 4 16 3).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_23_lower : (3135 / 1000 : ℝ) < Real.log 23 := by
  let c : LogCert := ⟨4, 16, 7⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (3135 / 1000 : ℚ) < c.lower := by
    change (3135 / 1000 : ℚ) < (LogCert.mk 4 16 7).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

private theorem log_29_lower : (3367 / 1000 : ℝ) < Real.log 29 := by
  let c : LogCert := ⟨4, 16, 13⟩
  have hv : c.Valid := by norm_num [c, LogCert.Valid]
  have hl : (3367 / 1000 : ℚ) < c.lower := by
    change (3367 / 1000 : ℚ) < (LogCert.mk 4 16 13).lower
    decide +kernel
  have h := LogCert.log_gt hv hl
  norm_num [c, LogCert.ratio] at h
  convert h using 1 <;> norm_num

/-- A deliberately coarse upper bound, sufficient for finite lower-bound checks. -/
theorem mertensE_lt_neg_thirteen_tenths : Goals.mertensE < -(1.3 : ℝ) := by
  have hsum := E₁.summable.sum_le_tsum
    ({2,3,5,7,11,13,17,19,23,29} : Finset ℕ)
    (fun p _ => E₁.summand_nonneg p)
  norm_num at hsum
  have hpartial : (0.723 : ℝ) < E₁ := by
    dsimp only [E₁]
    linarith [log_2_lower, log_3_lower, log_5_lower, log_7_lower, log_11_lower, log_13_lower, log_17_lower, log_19_lower, log_23_lower, log_29_lower]
  have hγ := SmallTotientProduct.gamma_bounds.1
  change -Real.eulerMascheroniConstant - E₁ < -(1.3 : ℝ)
  linarith

/-- The prime-weighted sum is nondecreasing, including at prime jumps. -/
theorem primeWeightedSum_mono {a b : ℝ} (hab : a ≤ b) :
    primeWeightedSum a ≤ primeWeightedSum b := by
  unfold primeWeightedSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hab)⟩, hp.2⟩
  · intro p hp hnot
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- The increasing real main term can be tested at the right block endpoint. -/
theorem lower_main_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    Real.log x - 1 / (2 * Real.log x) ≤
      Real.log y - 1 / (2 * Real.log y) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have hinv : 1 / (2 * Real.log y) ≤ 1 / (2 * Real.log x) := by gcongr
  linarith

/-- An exact numerical anchor proves the original RS62 inequality on a block. -/
theorem mertens_lower_of_block {a b x : ℝ} (ha : 1 < a)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hanchor : Real.log b - 1.3 - 1 / (2 * Real.log b) < primeWeightedSum a) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  have hm := lower_main_mono (lt_of_lt_of_le ha hax) hxb
  have hs := primeWeightedSum_mono hax
  have hE := mertensE_lt_neg_thirteen_tenths
  linarith

end TernaryGoldbach.RSBounds.MertensFiniteScalars
