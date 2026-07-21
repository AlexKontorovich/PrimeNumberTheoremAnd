/-
Computational certificates for Rosser–Schoenfeld
`∑_{p ≤ n} 1/p > log log n` on `3 ≤ n ≤ 30`, plus the real lift on `(1, 30]`.
Stepping stone toward closing `RS_prime.theorem_c` in `TMEEMT.lean`.
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
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_3 :
    ∑ p ∈ filter Nat.Prime (Iic 3), (1 : ℝ) / p > Real.log (Real.log 3) := by
  have hset : filter Nat.Prime (Iic 3) = {2, 3} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_4 :
    ∑ p ∈ filter Nat.Prime (Iic 4), (1 : ℝ) / p > Real.log (Real.log 4) := by
  have hset : filter Nat.Prime (Iic 4) = {2, 3} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_5 :
    ∑ p ∈ filter Nat.Prime (Iic 5), (1 : ℝ) / p > Real.log (Real.log 5) := by
  have hset : filter Nat.Prime (Iic 5) = {2, 3, 5} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_6 :
    ∑ p ∈ filter Nat.Prime (Iic 6), (1 : ℝ) / p > Real.log (Real.log 6) := by
  have hset : filter Nat.Prime (Iic 6) = {2, 3, 5} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_7 :
    ∑ p ∈ filter Nat.Prime (Iic 7), (1 : ℝ) / p > Real.log (Real.log 7) := by
  have hset : filter Nat.Prime (Iic 7) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_8 :
    ∑ p ∈ filter Nat.Prime (Iic 8), (1 : ℝ) / p > Real.log (Real.log 8) := by
  have hset : filter Nat.Prime (Iic 8) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_9 :
    ∑ p ∈ filter Nat.Prime (Iic 9), (1 : ℝ) / p > Real.log (Real.log 9) := by
  have hset : filter Nat.Prime (Iic 9) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_10 :
    ∑ p ∈ filter Nat.Prime (Iic 10), (1 : ℝ) / p > Real.log (Real.log 10) := by
  have hset : filter Nat.Prime (Iic 10) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_11 :
    ∑ p ∈ filter Nat.Prime (Iic 11), (1 : ℝ) / p > Real.log (Real.log 11) := by
  have hset : filter Nat.Prime (Iic 11) = {2, 3, 5, 7, 11} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_12 :
    ∑ p ∈ filter Nat.Prime (Iic 12), (1 : ℝ) / p > Real.log (Real.log 12) := by
  have hset : filter Nat.Prime (Iic 12) = {2, 3, 5, 7, 11} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_13 :
    ∑ p ∈ filter Nat.Prime (Iic 13), (1 : ℝ) / p > Real.log (Real.log 13) := by
  have hset : filter Nat.Prime (Iic 13) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_14 :
    ∑ p ∈ filter Nat.Prime (Iic 14), (1 : ℝ) / p > Real.log (Real.log 14) := by
  have hset : filter Nat.Prime (Iic 14) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_15 :
    ∑ p ∈ filter Nat.Prime (Iic 15), (1 : ℝ) / p > Real.log (Real.log 15) := by
  have hset : filter Nat.Prime (Iic 15) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_16 :
    ∑ p ∈ filter Nat.Prime (Iic 16), (1 : ℝ) / p > Real.log (Real.log 16) := by
  have hset : filter Nat.Prime (Iic 16) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_17 :
    ∑ p ∈ filter Nat.Prime (Iic 17), (1 : ℝ) / p > Real.log (Real.log 17) := by
  have hset : filter Nat.Prime (Iic 17) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_18 :
    ∑ p ∈ filter Nat.Prime (Iic 18), (1 : ℝ) / p > Real.log (Real.log 18) := by
  have hset : filter Nat.Prime (Iic 18) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_19 :
    ∑ p ∈ filter Nat.Prime (Iic 19), (1 : ℝ) / p > Real.log (Real.log 19) := by
  have hset : filter Nat.Prime (Iic 19) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_20 :
    ∑ p ∈ filter Nat.Prime (Iic 20), (1 : ℝ) / p > Real.log (Real.log 20) := by
  have hset : filter Nat.Prime (Iic 20) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_21 :
    ∑ p ∈ filter Nat.Prime (Iic 21), (1 : ℝ) / p > Real.log (Real.log 21) := by
  have hset : filter Nat.Prime (Iic 21) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_22 :
    ∑ p ∈ filter Nat.Prime (Iic 22), (1 : ℝ) / p > Real.log (Real.log 22) := by
  have hset : filter Nat.Prime (Iic 22) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_23 :
    ∑ p ∈ filter Nat.Prime (Iic 23), (1 : ℝ) / p > Real.log (Real.log 23) := by
  have hset : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_24 :
    ∑ p ∈ filter Nat.Prime (Iic 24), (1 : ℝ) / p > Real.log (Real.log 24) := by
  have hset : filter Nat.Prime (Iic 24) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_25 :
    ∑ p ∈ filter Nat.Prime (Iic 25), (1 : ℝ) / p > Real.log (Real.log 25) := by
  have hset : filter Nat.Prime (Iic 25) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_26 :
    ∑ p ∈ filter Nat.Prime (Iic 26), (1 : ℝ) / p > Real.log (Real.log 26) := by
  have hset : filter Nat.Prime (Iic 26) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_27 :
    ∑ p ∈ filter Nat.Prime (Iic 27), (1 : ℝ) / p > Real.log (Real.log 27) := by
  have hset : filter Nat.Prime (Iic 27) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_28 :
    ∑ p ∈ filter Nat.Prime (Iic 28), (1 : ℝ) / p > Real.log (Real.log 28) := by
  have hset : filter Nat.Prime (Iic 28) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_29 :
    ∑ p ∈ filter Nat.Prime (Iic 29), (1 : ℝ) / p > Real.log (Real.log 29) := by
  have hset : filter Nat.Prime (Iic 29) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide on reciprocal prime sums
private lemma sum_inv_p_gt_log_log_30 :
    ∑ p ∈ filter Nat.Prime (Iic 30), (1 : ℝ) / p > Real.log (Real.log 30) := by
  have hset : filter Nat.Prime (Iic 30) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_2 :
    ∑ p ∈ filter Nat.Prime (Iic 2), (1 : ℝ) / p > Real.log (Real.log (2 + 1)) := by
  have hset : filter Nat.Prime (Iic 2) = {2} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_3 :
    ∑ p ∈ filter Nat.Prime (Iic 3), (1 : ℝ) / p > Real.log (Real.log (3 + 1)) := by
  have hset : filter Nat.Prime (Iic 3) = {2, 3} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_4 :
    ∑ p ∈ filter Nat.Prime (Iic 4), (1 : ℝ) / p > Real.log (Real.log (4 + 1)) := by
  have hset : filter Nat.Prime (Iic 4) = {2, 3} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_5 :
    ∑ p ∈ filter Nat.Prime (Iic 5), (1 : ℝ) / p > Real.log (Real.log (5 + 1)) := by
  have hset : filter Nat.Prime (Iic 5) = {2, 3, 5} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_6 :
    ∑ p ∈ filter Nat.Prime (Iic 6), (1 : ℝ) / p > Real.log (Real.log (6 + 1)) := by
  have hset : filter Nat.Prime (Iic 6) = {2, 3, 5} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_7 :
    ∑ p ∈ filter Nat.Prime (Iic 7), (1 : ℝ) / p > Real.log (Real.log (7 + 1)) := by
  have hset : filter Nat.Prime (Iic 7) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_8 :
    ∑ p ∈ filter Nat.Prime (Iic 8), (1 : ℝ) / p > Real.log (Real.log (8 + 1)) := by
  have hset : filter Nat.Prime (Iic 8) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_9 :
    ∑ p ∈ filter Nat.Prime (Iic 9), (1 : ℝ) / p > Real.log (Real.log (9 + 1)) := by
  have hset : filter Nat.Prime (Iic 9) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_10 :
    ∑ p ∈ filter Nat.Prime (Iic 10), (1 : ℝ) / p > Real.log (Real.log (10 + 1)) := by
  have hset : filter Nat.Prime (Iic 10) = {2, 3, 5, 7} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_11 :
    ∑ p ∈ filter Nat.Prime (Iic 11), (1 : ℝ) / p > Real.log (Real.log (11 + 1)) := by
  have hset : filter Nat.Prime (Iic 11) = {2, 3, 5, 7, 11} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_12 :
    ∑ p ∈ filter Nat.Prime (Iic 12), (1 : ℝ) / p > Real.log (Real.log (12 + 1)) := by
  have hset : filter Nat.Prime (Iic 12) = {2, 3, 5, 7, 11} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_13 :
    ∑ p ∈ filter Nat.Prime (Iic 13), (1 : ℝ) / p > Real.log (Real.log (13 + 1)) := by
  have hset : filter Nat.Prime (Iic 13) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_14 :
    ∑ p ∈ filter Nat.Prime (Iic 14), (1 : ℝ) / p > Real.log (Real.log (14 + 1)) := by
  have hset : filter Nat.Prime (Iic 14) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_15 :
    ∑ p ∈ filter Nat.Prime (Iic 15), (1 : ℝ) / p > Real.log (Real.log (15 + 1)) := by
  have hset : filter Nat.Prime (Iic 15) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_16 :
    ∑ p ∈ filter Nat.Prime (Iic 16), (1 : ℝ) / p > Real.log (Real.log (16 + 1)) := by
  have hset : filter Nat.Prime (Iic 16) = {2, 3, 5, 7, 11, 13} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_17 :
    ∑ p ∈ filter Nat.Prime (Iic 17), (1 : ℝ) / p > Real.log (Real.log (17 + 1)) := by
  have hset : filter Nat.Prime (Iic 17) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_18 :
    ∑ p ∈ filter Nat.Prime (Iic 18), (1 : ℝ) / p > Real.log (Real.log (18 + 1)) := by
  have hset : filter Nat.Prime (Iic 18) = {2, 3, 5, 7, 11, 13, 17} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_19 :
    ∑ p ∈ filter Nat.Prime (Iic 19), (1 : ℝ) / p > Real.log (Real.log (19 + 1)) := by
  have hset : filter Nat.Prime (Iic 19) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_20 :
    ∑ p ∈ filter Nat.Prime (Iic 20), (1 : ℝ) / p > Real.log (Real.log (20 + 1)) := by
  have hset : filter Nat.Prime (Iic 20) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_21 :
    ∑ p ∈ filter Nat.Prime (Iic 21), (1 : ℝ) / p > Real.log (Real.log (21 + 1)) := by
  have hset : filter Nat.Prime (Iic 21) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_22 :
    ∑ p ∈ filter Nat.Prime (Iic 22), (1 : ℝ) / p > Real.log (Real.log (22 + 1)) := by
  have hset : filter Nat.Prime (Iic 22) = {2, 3, 5, 7, 11, 13, 17, 19} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_23 :
    ∑ p ∈ filter Nat.Prime (Iic 23), (1 : ℝ) / p > Real.log (Real.log (23 + 1)) := by
  have hset : filter Nat.Prime (Iic 23) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_24 :
    ∑ p ∈ filter Nat.Prime (Iic 24), (1 : ℝ) / p > Real.log (Real.log (24 + 1)) := by
  have hset : filter Nat.Prime (Iic 24) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_25 :
    ∑ p ∈ filter Nat.Prime (Iic 25), (1 : ℝ) / p > Real.log (Real.log (25 + 1)) := by
  have hset : filter Nat.Prime (Iic 25) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_26 :
    ∑ p ∈ filter Nat.Prime (Iic 26), (1 : ℝ) / p > Real.log (Real.log (26 + 1)) := by
  have hset : filter Nat.Prime (Iic 26) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_27 :
    ∑ p ∈ filter Nat.Prime (Iic 27), (1 : ℝ) / p > Real.log (Real.log (27 + 1)) := by
  have hset : filter Nat.Prime (Iic 27) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_28 :
    ∑ p ∈ filter Nat.Prime (Iic 28), (1 : ℝ) / p > Real.log (Real.log (28 + 1)) := by
  have hset : filter Nat.Prime (Iic 28) = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

set_option maxHeartbeats 800000 in
-- interval_decide; supports the real lift on half-open intervals
private lemma sum_inv_p_gt_log_log_succ_29 :
    ∑ p ∈ filter Nat.Prime (Iic 29), (1 : ℝ) / p > Real.log (Real.log (29 + 1)) := by
  have hset : filter Nat.Prime (Iic 29) = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by native_decide
  rw [hset]
  simp only [mem_insert, reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    cast_ofNat, sum_singleton]
  interval_decide

/-- Integer form: `∑_{p ≤ n} 1/p > log log n` for `3 ≤ n ≤ 30`. -/
lemma sum_inv_p_gt_log_log_of_le (n : ℕ) (hn₁ : 3 ≤ n) (hn₂ : n ≤ 30) :
    ∑ p ∈ filter Nat.Prime (Iic n), (1 : ℝ) / p > Real.log (Real.log n) := by
  interval_cases n
  · exact sum_inv_p_gt_log_log_3
  · exact sum_inv_p_gt_log_log_4
  · exact sum_inv_p_gt_log_log_5
  · exact sum_inv_p_gt_log_log_6
  · exact sum_inv_p_gt_log_log_7
  · exact sum_inv_p_gt_log_log_8
  · exact sum_inv_p_gt_log_log_9
  · exact sum_inv_p_gt_log_log_10
  · exact sum_inv_p_gt_log_log_11
  · exact sum_inv_p_gt_log_log_12
  · exact sum_inv_p_gt_log_log_13
  · exact sum_inv_p_gt_log_log_14
  · exact sum_inv_p_gt_log_log_15
  · exact sum_inv_p_gt_log_log_16
  · exact sum_inv_p_gt_log_log_17
  · exact sum_inv_p_gt_log_log_18
  · exact sum_inv_p_gt_log_log_19
  · exact sum_inv_p_gt_log_log_20
  · exact sum_inv_p_gt_log_log_21
  · exact sum_inv_p_gt_log_log_22
  · exact sum_inv_p_gt_log_log_23
  · exact sum_inv_p_gt_log_log_24
  · exact sum_inv_p_gt_log_log_25
  · exact sum_inv_p_gt_log_log_26
  · exact sum_inv_p_gt_log_log_27
  · exact sum_inv_p_gt_log_log_28
  · exact sum_inv_p_gt_log_log_29
  · exact sum_inv_p_gt_log_log_30

private lemma sum_inv_p_nonneg (n : ℕ) :
    (0 : ℝ) ≤ ∑ p ∈ filter Nat.Prime (Iic n), (1 : ℝ) / p :=
  Finset.sum_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)

private lemma sum_inv_p_gt_log_log_succ_of_le (n : ℕ) (hn₁ : 2 ≤ n) (hn₂ : n ≤ 30 - 1) :
    ∑ p ∈ filter Nat.Prime (Iic n), (1 : ℝ) / p > Real.log (Real.log (n + 1)) := by
  interval_cases n
  · exact sum_inv_p_gt_log_log_succ_2
  · exact sum_inv_p_gt_log_log_succ_3
  · exact sum_inv_p_gt_log_log_succ_4
  · exact sum_inv_p_gt_log_log_succ_5
  · exact sum_inv_p_gt_log_log_succ_6
  · exact sum_inv_p_gt_log_log_succ_7
  · exact sum_inv_p_gt_log_log_succ_8
  · exact sum_inv_p_gt_log_log_succ_9
  · exact sum_inv_p_gt_log_log_succ_10
  · exact sum_inv_p_gt_log_log_succ_11
  · exact sum_inv_p_gt_log_log_succ_12
  · exact sum_inv_p_gt_log_log_succ_13
  · exact sum_inv_p_gt_log_log_succ_14
  · exact sum_inv_p_gt_log_log_succ_15
  · exact sum_inv_p_gt_log_log_succ_16
  · exact sum_inv_p_gt_log_log_succ_17
  · exact sum_inv_p_gt_log_log_succ_18
  · exact sum_inv_p_gt_log_log_succ_19
  · exact sum_inv_p_gt_log_log_succ_20
  · exact sum_inv_p_gt_log_log_succ_21
  · exact sum_inv_p_gt_log_log_succ_22
  · exact sum_inv_p_gt_log_log_succ_23
  · exact sum_inv_p_gt_log_log_succ_24
  · exact sum_inv_p_gt_log_log_succ_25
  · exact sum_inv_p_gt_log_log_succ_26
  · exact sum_inv_p_gt_log_log_succ_27
  · exact sum_inv_p_gt_log_log_succ_28
  · exact sum_inv_p_gt_log_log_succ_29

/-- Real form on `(1, 30]`. -/
theorem sum_inv_p_gt_log_log_of_mem_Ioc (x : ℝ) (hx₁ : 1 < x) (hx₂ : x ≤ 30) :
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), (1 : ℝ) / p > Real.log (Real.log x) := by
  have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx₁)
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx₁
  by_cases he : x < Real.exp 1
  · have hlogx_lt1 : Real.log x < 1 :=
      (Real.log_lt_iff_lt_exp (lt_trans zero_lt_one hx₁)).mpr he
    have hrhs : Real.log (Real.log x) < 0 := by
      have : Real.log x < Real.exp 0 := by simpa using hlogx_lt1
      exact (Real.log_lt_iff_lt_exp hlogx_pos).mpr this
    exact lt_of_lt_of_le hrhs (sum_inv_p_nonneg _)
  · replace he : Real.exp 1 ≤ x := le_of_not_gt he
    set n := ⌊x⌋₊
    have hnN : n ≤ 30 := by exact_mod_cast (Nat.floor_le hx0).trans hx₂
    have hn2 : 2 ≤ n :=
      (Nat.le_floor_iff hx0).2 (le_trans (by interval_decide : (2 : ℝ) ≤ Real.exp 1) he)
    by_cases hN : n = 30
    · have h1 : (30 : ℝ) ≤ x := by
        have : (n : ℝ) ≤ x := Nat.floor_le hx0
        simpa [hN] using this
      have hxeq : x = (30 : ℝ) := le_antisymm hx₂ h1
      simpa [hN, hxeq] using sum_inv_p_gt_log_log_30
    · have hn_le : n ≤ 30 - 1 := Nat.le_pred_of_lt (lt_of_le_of_ne hnN hN)
      have hsum := sum_inv_p_gt_log_log_succ_of_le n hn2 hn_le
      have hxlt : x < (n + 1 : ℝ) := Nat.lt_floor_add_one x
      have hxpos' : (0 : ℝ) < x := lt_trans zero_lt_one hx₁
      have hlog_mono : Real.log x ≤ Real.log (n + 1) :=
        Real.log_le_log hxpos' (le_of_lt hxlt)
      have hloglog_mono : Real.log (Real.log x) ≤ Real.log (Real.log (n + 1)) :=
        Real.log_le_log hlogx_pos hlog_mono
      exact lt_of_le_of_lt hloglog_mono hsum

end RS_prime
