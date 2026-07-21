/-
Computational certificates for Rosser–Schoenfeld
`∑_{p ≤ n} (log p)/p < log n` on `2 ≤ n ≤ 40`, plus the real lift on `(1, 40]`.
Stepping stone toward closing `RS_prime.theorem_d` in `TMEEMT.lean`.
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.IntervalCases
import LeanCert.Tactic

set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false

open Real
open Nat hiding log
open Finset

namespace RS_prime

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `2`. -/
private lemma sum_log_div_p_lt_log_2 :
    ∑ q ∈ filter Nat.Prime (Iic 2), Real.log q / (q : ℝ) < Real.log 2 := by
  have hset : filter Nat.Prime (Iic 2) = {2} := by native_decide
  rw [hset]
  simp only [sum_singleton, cast_ofNat]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `3`. -/
private lemma sum_log_div_p_lt_log_3 :
    ∑ q ∈ filter Nat.Prime (Iic 3), Real.log q / (q : ℝ) < Real.log 3 := by
  have hset : filter Nat.Prime (Iic 3) = {2, 3} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `5`. -/
private lemma sum_log_div_p_lt_log_5 :
    ∑ q ∈ filter Nat.Prime (Iic 5), Real.log q / (q : ℝ) < Real.log 5 := by
  have hset : filter Nat.Prime (Iic 5) = {2, 3, 5} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `7`. -/
private lemma sum_log_div_p_lt_log_7 :
    ∑ q ∈ filter Nat.Prime (Iic 7), Real.log q / (q : ℝ) < Real.log 7 := by
  have hset : filter Nat.Prime (Iic 7) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `11`. -/
private lemma sum_log_div_p_lt_log_11 :
    ∑ q ∈ filter Nat.Prime (Iic 11), Real.log q / (q : ℝ) < Real.log 11 := by
  have hset : filter Nat.Prime (Iic 11) = {2, 3, 5, 7, 11} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `13`. -/
private lemma sum_log_div_p_lt_log_13 :
    ∑ q ∈ filter Nat.Prime (Iic 13), Real.log q / (q : ℝ) < Real.log 13 := by
  have hset : filter Nat.Prime (Iic 13) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `17`. -/
private lemma sum_log_div_p_lt_log_17 :
    ∑ q ∈ filter Nat.Prime (Iic 17), Real.log q / (q : ℝ) < Real.log 17 := by
  have hset : filter Nat.Prime (Iic 17) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `19`. -/
private lemma sum_log_div_p_lt_log_19 :
    ∑ q ∈ filter Nat.Prime (Iic 19), Real.log q / (q : ℝ) < Real.log 19 := by
  have hset : filter Nat.Prime (Iic 19) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `23`. -/
private lemma sum_log_div_p_lt_log_23 :
    ∑ q ∈ filter Nat.Prime (Iic 23), Real.log q / (q : ℝ) < Real.log 23 := by
  have hset : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `29`. -/
private lemma sum_log_div_p_lt_log_29 :
    ∑ q ∈ filter Nat.Prime (Iic 29), Real.log q / (q : ℝ) < Real.log 29 := by
  have hset : filter Nat.Prime (Iic 29) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `31`. -/
private lemma sum_log_div_p_lt_log_31 :
    ∑ q ∈ filter Nat.Prime (Iic 31), Real.log q / (q : ℝ) < Real.log 31 := by
  have hset : filter Nat.Prime (Iic 31) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Certificate at prime `37`. -/
private lemma sum_log_div_p_lt_log_37 :
    ∑ q ∈ filter Nat.Prime (Iic 37), Real.log q / (q : ℝ) < Real.log 37 := by
  have hset : filter Nat.Prime (Iic 37) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on prime log-sums
/-- Integer form: `∑_{p ≤ n} (log p)/p < log n` for `2 ≤ n ≤ 40`. -/
lemma sum_log_div_p_lt_log_of_le (n : ℕ) (hn₁ : 2 ≤ n) (hn₂ : n ≤ 40) :
    ∑ p ∈ filter Nat.Prime (Iic n), Real.log p / (p : ℝ) < Real.log n := by
  interval_cases n
  · exact sum_log_div_p_lt_log_2
  · exact sum_log_div_p_lt_log_3
  · have hset : filter Nat.Prime (Iic 4) = {2, 3} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 4), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 3), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 3) = {2, 3} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_3
    have hlog : Real.log 3 < Real.log 4 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 4)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_5
  · have hset : filter Nat.Prime (Iic 6) = {2, 3, 5} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 6), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 5), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 5) = {2, 3, 5} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_5
    have hlog : Real.log 5 < Real.log 6 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 6)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_7
  · have hset : filter Nat.Prime (Iic 8) = {2, 3, 5, 7} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 8), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 7), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 7) = {2, 3, 5, 7} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_7
    have hlog : Real.log 7 < Real.log 8 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 7) (by norm_num : (0 : ℝ) < 8)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 9) = {2, 3, 5, 7} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 9), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 7), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 7) = {2, 3, 5, 7} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_7
    have hlog : Real.log 7 < Real.log 9 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 7) (by norm_num : (0 : ℝ) < 9)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 10) = {2, 3, 5, 7} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 10), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 7), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 7) = {2, 3, 5, 7} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_7
    have hlog : Real.log 7 < Real.log 10 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 7) (by norm_num : (0 : ℝ) < 10)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_11
  · have hset : filter Nat.Prime (Iic 12) = {2, 3, 5, 7, 11} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 12), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 11), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 11) = {2, 3, 5, 7, 11} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_11
    have hlog : Real.log 11 < Real.log 12 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 11) (by norm_num : (0 : ℝ) < 12)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_13
  · have hset : filter Nat.Prime (Iic 14) = {2, 3, 5, 7, 11, 13} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 14), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 13), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 13) = {2, 3, 5, 7, 11, 13} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_13
    have hlog : Real.log 13 < Real.log 14 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 13) (by norm_num : (0 : ℝ) < 14)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 15) = {2, 3, 5, 7, 11, 13} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 15), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 13), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 13) = {2, 3, 5, 7, 11, 13} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_13
    have hlog : Real.log 13 < Real.log 15 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 13) (by norm_num : (0 : ℝ) < 15)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 16) = {2, 3, 5, 7, 11, 13} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 16), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 13), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 13) = {2, 3, 5, 7, 11, 13} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_13
    have hlog : Real.log 13 < Real.log 16 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 13) (by norm_num : (0 : ℝ) < 16)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_17
  · have hset : filter Nat.Prime (Iic 18) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 18), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 17), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 17) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_17
    have hlog : Real.log 17 < Real.log 18 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 17) (by norm_num : (0 : ℝ) < 18)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_19
  · have hset : filter Nat.Prime (Iic 20) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 20), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 19), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 19) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_19
    have hlog : Real.log 19 < Real.log 20 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 19) (by norm_num : (0 : ℝ) < 20)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 21) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 21), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 19), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 19) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_19
    have hlog : Real.log 19 < Real.log 21 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 19) (by norm_num : (0 : ℝ) < 21)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 22) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 22), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 19), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 19) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_19
    have hlog : Real.log 19 < Real.log 22 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 19) (by norm_num : (0 : ℝ) < 22)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_23
  · have hset : filter Nat.Prime (Iic 24) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 24), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 23), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_23
    have hlog : Real.log 23 < Real.log 24 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 23) (by norm_num : (0 : ℝ) < 24)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 25) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 25), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 23), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_23
    have hlog : Real.log 23 < Real.log 25 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 23) (by norm_num : (0 : ℝ) < 25)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 26) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 26), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 23), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_23
    have hlog : Real.log 23 < Real.log 26 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 23) (by norm_num : (0 : ℝ) < 26)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 27) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 27), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 23), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_23
    have hlog : Real.log 23 < Real.log 27 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 23) (by norm_num : (0 : ℝ) < 27)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 28) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 28), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 23), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_23
    have hlog : Real.log 23 < Real.log 28 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 23) (by norm_num : (0 : ℝ) < 28)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_29
  · have hset : filter Nat.Prime (Iic 30) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 30), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 29), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 29) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_29
    have hlog : Real.log 29 < Real.log 30 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 29) (by norm_num : (0 : ℝ) < 30)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_31
  · have hset : filter Nat.Prime (Iic 32) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 32), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 31), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 31) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_31
    have hlog : Real.log 31 < Real.log 32 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 31) (by norm_num : (0 : ℝ) < 32)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 33) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 33), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 31), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 31) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_31
    have hlog : Real.log 31 < Real.log 33 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 31) (by norm_num : (0 : ℝ) < 33)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 34) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 34), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 31), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 31) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_31
    have hlog : Real.log 31 < Real.log 34 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 31) (by norm_num : (0 : ℝ) < 34)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 35) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 35), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 31), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 31) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_31
    have hlog : Real.log 31 < Real.log 35 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 31) (by norm_num : (0 : ℝ) < 35)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 36) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 36), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 31), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 31) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_31
    have hlog : Real.log 31 < Real.log 36 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 31) (by norm_num : (0 : ℝ) < 36)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · exact sum_log_div_p_lt_log_37
  · have hset : filter Nat.Prime (Iic 38) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 38), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 37), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 37) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_37
    have hlog : Real.log 37 < Real.log 38 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 37) (by norm_num : (0 : ℝ) < 38)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 39) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 39), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 37), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 37) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_37
    have hlog : Real.log 37 < Real.log 39 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 37) (by norm_num : (0 : ℝ) < 39)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)
  · have hset : filter Nat.Prime (Iic 40) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
    have hsum : ∑ p ∈ filter Nat.Prime (Iic 40), Real.log p / (p : ℝ) =
        ∑ p ∈ filter Nat.Prime (Iic 37), Real.log p / (p : ℝ) := by
      have hset' : filter Nat.Prime (Iic 37) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by native_decide
      simp [hset, hset']
    have hprev := sum_log_div_p_lt_log_37
    have hlog : Real.log 37 < Real.log 40 :=
      (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 37) (by norm_num : (0 : ℝ) < 40)).2
        (by norm_num)
    exact hsum ▸ (lt_trans hprev hlog)

/-- Real form on `(1, 40]`: reduces to the integer certificate via monotonicity of `log`. -/
theorem sum_log_div_p_lt_log_of_mem_Ioc (x : ℝ) (hx₁ : 1 < x) (hx₂ : x ≤ 40) :
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), Real.log p / (p : ℝ) < Real.log x := by
  have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx₁)
  by_cases h2 : x < 2
  · have hfl : ⌊x⌋₊ = 1 := by
      refine (Nat.floor_eq_iff (n := 1) hx0).2 ⟨?_, ?_⟩
      · exact_mod_cast (le_of_lt hx₁ : (1 : ℝ) ≤ x)
      · have : ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) := by norm_num
        exact this ▸ h2
    have hempty : filter Nat.Prime (Iic 1) = (∅ : Finset ℕ) := by native_decide
    simp [hfl, hempty, Real.log_pos hx₁]
  · replace h2 : (2 : ℝ) ≤ x := le_of_not_gt h2
    set n := ⌊x⌋₊
    have hn2 : 2 ≤ n := (Nat.le_floor_iff hx0).2 h2
    have hnN : n ≤ 40 := by
      have : (n : ℝ) ≤ x := Nat.floor_le hx0
      exact_mod_cast this.trans hx₂
    have hsum := sum_log_div_p_lt_log_of_le n hn2 hnN
    have hn_le_x : (n : ℝ) ≤ x := Nat.floor_le hx0
    have hn_pos : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2)
    exact lt_of_lt_of_le hsum (Real.log_le_log hn_pos hn_le_x)

end RS_prime
