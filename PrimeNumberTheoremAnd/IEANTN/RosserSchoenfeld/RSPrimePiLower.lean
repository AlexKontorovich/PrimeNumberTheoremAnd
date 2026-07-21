/-
Computational certificates for Rosser–Schoenfeld `π(n) > n / log n`
on `17 ≤ n ≤ 60`, plus the real lift on `[17, 60]`.
Stepping stone toward closing `RS_prime.theorem_b` in `TMEEMT.lean`.
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.IntervalCases
import LeanCert.Tactic

set_option linter.style.nativeDecide false

open Real
open Nat hiding log

namespace RS_prime

private lemma primeCounting_17 : Nat.primeCounting 17 = 7 := by native_decide
private lemma primeCounting_18 : Nat.primeCounting 18 = 7 := by native_decide
private lemma primeCounting_19 : Nat.primeCounting 19 = 8 := by native_decide
private lemma primeCounting_20 : Nat.primeCounting 20 = 8 := by native_decide
private lemma primeCounting_21 : Nat.primeCounting 21 = 8 := by native_decide
private lemma primeCounting_22 : Nat.primeCounting 22 = 8 := by native_decide
private lemma primeCounting_23 : Nat.primeCounting 23 = 9 := by native_decide
private lemma primeCounting_24 : Nat.primeCounting 24 = 9 := by native_decide
private lemma primeCounting_25 : Nat.primeCounting 25 = 9 := by native_decide
private lemma primeCounting_26 : Nat.primeCounting 26 = 9 := by native_decide
private lemma primeCounting_27 : Nat.primeCounting 27 = 9 := by native_decide
private lemma primeCounting_28 : Nat.primeCounting 28 = 9 := by native_decide
private lemma primeCounting_29 : Nat.primeCounting 29 = 10 := by native_decide
private lemma primeCounting_30 : Nat.primeCounting 30 = 10 := by native_decide
private lemma primeCounting_31 : Nat.primeCounting 31 = 11 := by native_decide
private lemma primeCounting_32 : Nat.primeCounting 32 = 11 := by native_decide
private lemma primeCounting_33 : Nat.primeCounting 33 = 11 := by native_decide
private lemma primeCounting_34 : Nat.primeCounting 34 = 11 := by native_decide
private lemma primeCounting_35 : Nat.primeCounting 35 = 11 := by native_decide
private lemma primeCounting_36 : Nat.primeCounting 36 = 11 := by native_decide
private lemma primeCounting_37 : Nat.primeCounting 37 = 12 := by native_decide
private lemma primeCounting_38 : Nat.primeCounting 38 = 12 := by native_decide
private lemma primeCounting_39 : Nat.primeCounting 39 = 12 := by native_decide
private lemma primeCounting_40 : Nat.primeCounting 40 = 12 := by native_decide
private lemma primeCounting_41 : Nat.primeCounting 41 = 13 := by native_decide
private lemma primeCounting_42 : Nat.primeCounting 42 = 13 := by native_decide
private lemma primeCounting_43 : Nat.primeCounting 43 = 14 := by native_decide
private lemma primeCounting_44 : Nat.primeCounting 44 = 14 := by native_decide
private lemma primeCounting_45 : Nat.primeCounting 45 = 14 := by native_decide
private lemma primeCounting_46 : Nat.primeCounting 46 = 14 := by native_decide
private lemma primeCounting_47 : Nat.primeCounting 47 = 15 := by native_decide
private lemma primeCounting_48 : Nat.primeCounting 48 = 15 := by native_decide
private lemma primeCounting_49 : Nat.primeCounting 49 = 15 := by native_decide
private lemma primeCounting_50 : Nat.primeCounting 50 = 15 := by native_decide
private lemma primeCounting_51 : Nat.primeCounting 51 = 15 := by native_decide
private lemma primeCounting_52 : Nat.primeCounting 52 = 15 := by native_decide
private lemma primeCounting_53 : Nat.primeCounting 53 = 16 := by native_decide
private lemma primeCounting_54 : Nat.primeCounting 54 = 16 := by native_decide
private lemma primeCounting_55 : Nat.primeCounting 55 = 16 := by native_decide
private lemma primeCounting_56 : Nat.primeCounting 56 = 16 := by native_decide
private lemma primeCounting_57 : Nat.primeCounting 57 = 16 := by native_decide
private lemma primeCounting_58 : Nat.primeCounting 58 = 16 := by native_decide
private lemma primeCounting_59 : Nat.primeCounting 59 = 17 := by native_decide
private lemma primeCounting_60 : Nat.primeCounting 60 = 17 := by native_decide

/-- Integer form: `π(n) > n / log n` for `17 ≤ n ≤ 60`. -/
lemma primeCounting_gt_div_log_of_le (n : ℕ) (hn₁ : 17 ≤ n) (hn₂ : n ≤ 60) :
    (n.primeCounting : ℝ) > (n : ℝ) / Real.log n := by
  interval_cases n
  · have hpi : ((17 : ℕ).primeCounting : ℝ) = 7 := by rw [primeCounting_17]; norm_num
    have hexp : Real.exp ((5 : ℝ) / 2) < 17 := by interval_decide
    have hlog : (5 : ℝ) / 2 < Real.log 17 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 17)).mpr hexp
    have hqpos : (0 : ℝ) < (5 : ℝ) / 2 := by positivity
    have hdiv : (17 : ℝ) / Real.log 17 < (17 : ℝ) / ((5 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 17) hqpos hlog
    have hcmp : (17 : ℝ) / ((5 : ℝ) / 2) < 7 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((18 : ℕ).primeCounting : ℝ) = 7 := by rw [primeCounting_18]; norm_num
    have hexp : Real.exp ((11 : ℝ) / 4) < 18 := by interval_decide
    have hlog : (11 : ℝ) / 4 < Real.log 18 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 18)).mpr hexp
    have hqpos : (0 : ℝ) < (11 : ℝ) / 4 := by positivity
    have hdiv : (18 : ℝ) / Real.log 18 < (18 : ℝ) / ((11 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 18) hqpos hlog
    have hcmp : (18 : ℝ) / ((11 : ℝ) / 4) < 7 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((19 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_19]; norm_num
    have hexp : Real.exp ((5 : ℝ) / 2) < 19 := by interval_decide
    have hlog : (5 : ℝ) / 2 < Real.log 19 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 19)).mpr hexp
    have hqpos : (0 : ℝ) < (5 : ℝ) / 2 := by positivity
    have hdiv : (19 : ℝ) / Real.log 19 < (19 : ℝ) / ((5 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 19) hqpos hlog
    have hcmp : (19 : ℝ) / ((5 : ℝ) / 2) < 8 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((20 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_20]; norm_num
    have hexp : Real.exp ((11 : ℝ) / 4) < 20 := by interval_decide
    have hlog : (11 : ℝ) / 4 < Real.log 20 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 20)).mpr hexp
    have hqpos : (0 : ℝ) < (11 : ℝ) / 4 := by positivity
    have hdiv : (20 : ℝ) / Real.log 20 < (20 : ℝ) / ((11 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 20) hqpos hlog
    have hcmp : (20 : ℝ) / ((11 : ℝ) / 4) < 8 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((21 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_21]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 21 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 21 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 21)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (21 : ℝ) / Real.log 21 < (21 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 21) hqpos hlog
    have hcmp : (21 : ℝ) / ((3 : ℝ) / 1) < 8 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((22 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_22]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 22 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 22 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 22)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (22 : ℝ) / Real.log 22 < (22 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 22) hqpos hlog
    have hcmp : (22 : ℝ) / ((3 : ℝ) / 1) < 8 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((23 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_23]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 23 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 23 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 23)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (23 : ℝ) / Real.log 23 < (23 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 23) hqpos hlog
    have hcmp : (23 : ℝ) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((24 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_24]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 24 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 24 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 24)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (24 : ℝ) / Real.log 24 < (24 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 24) hqpos hlog
    have hcmp : (24 : ℝ) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((25 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_25]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 25 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 25 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 25)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (25 : ℝ) / Real.log 25 < (25 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 25) hqpos hlog
    have hcmp : (25 : ℝ) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((26 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_26]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 26 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 26 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 26)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (26 : ℝ) / Real.log 26 < (26 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 26) hqpos hlog
    have hcmp : (26 : ℝ) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((27 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_27]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 27 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 27 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 27)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : (27 : ℝ) / Real.log 27 < (27 : ℝ) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 27) hqpos hlog
    have hcmp : (27 : ℝ) / ((13 : ℝ) / 4) < 9 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((28 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_28]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 28 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 28 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 28)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : (28 : ℝ) / Real.log 28 < (28 : ℝ) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 28) hqpos hlog
    have hcmp : (28 : ℝ) / ((13 : ℝ) / 4) < 9 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((29 : ℕ).primeCounting : ℝ) = 10 := by rw [primeCounting_29]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 29 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 29 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 29)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (29 : ℝ) / Real.log 29 < (29 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 29) hqpos hlog
    have hcmp : (29 : ℝ) / ((3 : ℝ) / 1) < 10 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((30 : ℕ).primeCounting : ℝ) = 10 := by rw [primeCounting_30]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 30 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 30 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 30)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : (30 : ℝ) / Real.log 30 < (30 : ℝ) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 30) hqpos hlog
    have hcmp : (30 : ℝ) / ((13 : ℝ) / 4) < 10 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((31 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_31]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 31 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 31 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 31)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (31 : ℝ) / Real.log 31 < (31 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 31) hqpos hlog
    have hcmp : (31 : ℝ) / ((3 : ℝ) / 1) < 11 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((32 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_32]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 32 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 32 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 32)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : (32 : ℝ) / Real.log 32 < (32 : ℝ) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 32) hqpos hlog
    have hcmp : (32 : ℝ) / ((3 : ℝ) / 1) < 11 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((33 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_33]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 33 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 33 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 33)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : (33 : ℝ) / Real.log 33 < (33 : ℝ) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 33) hqpos hlog
    have hcmp : (33 : ℝ) / ((13 : ℝ) / 4) < 11 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((34 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_34]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 34 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 34 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 34)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (34 : ℝ) / Real.log 34 < (34 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 34) hqpos hlog
    have hcmp : (34 : ℝ) / ((7 : ℝ) / 2) < 11 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((35 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_35]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 35 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 35 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 35)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (35 : ℝ) / Real.log 35 < (35 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 35) hqpos hlog
    have hcmp : (35 : ℝ) / ((7 : ℝ) / 2) < 11 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((36 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_36]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 36 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 36 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 36)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (36 : ℝ) / Real.log 36 < (36 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 36) hqpos hlog
    have hcmp : (36 : ℝ) / ((7 : ℝ) / 2) < 11 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((37 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_37]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 37 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 37 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 37)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (37 : ℝ) / Real.log 37 < (37 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 37) hqpos hlog
    have hcmp : (37 : ℝ) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((38 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_38]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 38 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 38 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 38)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (38 : ℝ) / Real.log 38 < (38 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 38) hqpos hlog
    have hcmp : (38 : ℝ) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((39 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_39]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 39 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 39 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 39)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (39 : ℝ) / Real.log 39 < (39 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 39) hqpos hlog
    have hcmp : (39 : ℝ) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((40 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_40]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 40 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 40 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 40)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (40 : ℝ) / Real.log 40 < (40 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 40) hqpos hlog
    have hcmp : (40 : ℝ) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((41 : ℕ).primeCounting : ℝ) = 13 := by rw [primeCounting_41]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 41 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 41 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 41)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (41 : ℝ) / Real.log 41 < (41 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 41) hqpos hlog
    have hcmp : (41 : ℝ) / ((7 : ℝ) / 2) < 13 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((42 : ℕ).primeCounting : ℝ) = 13 := by rw [primeCounting_42]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 42 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 42 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 42)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (42 : ℝ) / Real.log 42 < (42 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 42) hqpos hlog
    have hcmp : (42 : ℝ) / ((7 : ℝ) / 2) < 13 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((43 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_43]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 43 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 43 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 43)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (43 : ℝ) / Real.log 43 < (43 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 43) hqpos hlog
    have hcmp : (43 : ℝ) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((44 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_44]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 44 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 44 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 44)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (44 : ℝ) / Real.log 44 < (44 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 44) hqpos hlog
    have hcmp : (44 : ℝ) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((45 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_45]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 45 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 45 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 45)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (45 : ℝ) / Real.log 45 < (45 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 45) hqpos hlog
    have hcmp : (45 : ℝ) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((46 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_46]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 46 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 46 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 46)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (46 : ℝ) / Real.log 46 < (46 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 46) hqpos hlog
    have hcmp : (46 : ℝ) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((47 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_47]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 47 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 47 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 47)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (47 : ℝ) / Real.log 47 < (47 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 47) hqpos hlog
    have hcmp : (47 : ℝ) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((48 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_48]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 48 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 48 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 48)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (48 : ℝ) / Real.log 48 < (48 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 48) hqpos hlog
    have hcmp : (48 : ℝ) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((49 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_49]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 49 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 49 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 49)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (49 : ℝ) / Real.log 49 < (49 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 49) hqpos hlog
    have hcmp : (49 : ℝ) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((50 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_50]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 50 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 50 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 50)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (50 : ℝ) / Real.log 50 < (50 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 50) hqpos hlog
    have hcmp : (50 : ℝ) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((51 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_51]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 51 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 51 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 51)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (51 : ℝ) / Real.log 51 < (51 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 51) hqpos hlog
    have hcmp : (51 : ℝ) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((52 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_52]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 52 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 52 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 52)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (52 : ℝ) / Real.log 52 < (52 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 52) hqpos hlog
    have hcmp : (52 : ℝ) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((53 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_53]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 53 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 53 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 53)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (53 : ℝ) / Real.log 53 < (53 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 53) hqpos hlog
    have hcmp : (53 : ℝ) / ((7 : ℝ) / 2) < 16 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((54 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_54]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 54 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 54 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 54)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : (54 : ℝ) / Real.log 54 < (54 : ℝ) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 54) hqpos hlog
    have hcmp : (54 : ℝ) / ((7 : ℝ) / 2) < 16 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((55 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_55]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 55 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 55 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 55)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : (55 : ℝ) / Real.log 55 < (55 : ℝ) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 55) hqpos hlog
    have hcmp : (55 : ℝ) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((56 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_56]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 56 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 56 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 56)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : (56 : ℝ) / Real.log 56 < (56 : ℝ) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 56) hqpos hlog
    have hcmp : (56 : ℝ) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((57 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_57]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 57 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 57 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 57)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : (57 : ℝ) / Real.log 57 < (57 : ℝ) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 57) hqpos hlog
    have hcmp : (57 : ℝ) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((58 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_58]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 58 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 58 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 58)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : (58 : ℝ) / Real.log 58 < (58 : ℝ) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 58) hqpos hlog
    have hcmp : (58 : ℝ) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((59 : ℕ).primeCounting : ℝ) = 17 := by rw [primeCounting_59]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 59 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 59 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 59)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : (59 : ℝ) / Real.log 59 < (59 : ℝ) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 59) hqpos hlog
    have hcmp : (59 : ℝ) / ((4 : ℝ) / 1) < 17 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp
  · have hpi : ((60 : ℕ).primeCounting : ℝ) = 17 := by rw [primeCounting_60]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 60 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 60 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 60)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : (60 : ℝ) / Real.log 60 < (60 : ℝ) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 60) hqpos hlog
    have hcmp : (60 : ℝ) / ((4 : ℝ) / 1) < 17 := by field_simp; norm_num
    exact hpi ▸ lt_trans hdiv hcmp

/-- Real form on `[17, 60]`. -/
lemma pi_gt_div_log_of_le_real (x : ℝ) (hx₁ : 17 ≤ x) (hx₂ : x ≤ 60) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) > x / Real.log x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  set n := ⌊x⌋₊ with hn_def
  have hn₁ : 17 ≤ n := (Nat.le_floor_iff hx0).2 (by exact_mod_cast hx₁)
  have hn₂ : n ≤ 60 := by
    have : (n : ℝ) ≤ 60 := (Nat.floor_le hx0).trans hx₂
    exact_mod_cast this
  have hxlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 17) hn₁)
  have hloge : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 17) hn₁)
  have hlogn : 0 < Real.log n := Real.log_pos hloge
  interval_cases n
  · have hpi : ((17 : ℕ).primeCounting : ℝ) = 7 := by rw [primeCounting_17]; norm_num
    have hexp : Real.exp ((11 : ℝ) / 4) < 17 := by interval_decide
    have hlog : (11 : ℝ) / 4 < Real.log 17 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 17)).mpr hexp
    have hqpos : (0 : ℝ) < (11 : ℝ) / 4 := by positivity
    have hdiv : ((17 : ℝ) + 1) / Real.log 17 < ((17 : ℝ) + 1) / ((11 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((17 : ℝ) + 1) / ((11 : ℝ) / 4) < 7 := by field_simp; norm_num
    have hsucc : ((17 : ℝ) + 1) / Real.log 17 < 7 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((17 : ℝ) + 1) / Real.log 17 := by
      have h1 : x / Real.log x < ((17 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((17 : ℝ) + 1) / Real.log x ≤ ((17 : ℝ) + 1) / Real.log 17 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((18 : ℕ).primeCounting : ℝ) = 7 := by rw [primeCounting_18]; norm_num
    have hexp : Real.exp ((11 : ℝ) / 4) < 18 := by interval_decide
    have hlog : (11 : ℝ) / 4 < Real.log 18 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 18)).mpr hexp
    have hqpos : (0 : ℝ) < (11 : ℝ) / 4 := by positivity
    have hdiv : ((18 : ℝ) + 1) / Real.log 18 < ((18 : ℝ) + 1) / ((11 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((18 : ℝ) + 1) / ((11 : ℝ) / 4) < 7 := by field_simp; norm_num
    have hsucc : ((18 : ℝ) + 1) / Real.log 18 < 7 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((18 : ℝ) + 1) / Real.log 18 := by
      have h1 : x / Real.log x < ((18 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((18 : ℝ) + 1) / Real.log x ≤ ((18 : ℝ) + 1) / Real.log 18 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((19 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_19]; norm_num
    have hexp : Real.exp ((11 : ℝ) / 4) < 19 := by interval_decide
    have hlog : (11 : ℝ) / 4 < Real.log 19 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 19)).mpr hexp
    have hqpos : (0 : ℝ) < (11 : ℝ) / 4 := by positivity
    have hdiv : ((19 : ℝ) + 1) / Real.log 19 < ((19 : ℝ) + 1) / ((11 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((19 : ℝ) + 1) / ((11 : ℝ) / 4) < 8 := by field_simp; norm_num
    have hsucc : ((19 : ℝ) + 1) / Real.log 19 < 8 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((19 : ℝ) + 1) / Real.log 19 := by
      have h1 : x / Real.log x < ((19 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((19 : ℝ) + 1) / Real.log x ≤ ((19 : ℝ) + 1) / Real.log 19 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((20 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_20]; norm_num
    have hexp : Real.exp ((11 : ℝ) / 4) < 20 := by interval_decide
    have hlog : (11 : ℝ) / 4 < Real.log 20 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 20)).mpr hexp
    have hqpos : (0 : ℝ) < (11 : ℝ) / 4 := by positivity
    have hdiv : ((20 : ℝ) + 1) / Real.log 20 < ((20 : ℝ) + 1) / ((11 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((20 : ℝ) + 1) / ((11 : ℝ) / 4) < 8 := by field_simp; norm_num
    have hsucc : ((20 : ℝ) + 1) / Real.log 20 < 8 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((20 : ℝ) + 1) / Real.log 20 := by
      have h1 : x / Real.log x < ((20 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((20 : ℝ) + 1) / Real.log x ≤ ((20 : ℝ) + 1) / Real.log 20 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((21 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_21]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 21 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 21 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 21)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : ((21 : ℝ) + 1) / Real.log 21 < ((21 : ℝ) + 1) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((21 : ℝ) + 1) / ((3 : ℝ) / 1) < 8 := by field_simp; norm_num
    have hsucc : ((21 : ℝ) + 1) / Real.log 21 < 8 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((21 : ℝ) + 1) / Real.log 21 := by
      have h1 : x / Real.log x < ((21 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((21 : ℝ) + 1) / Real.log x ≤ ((21 : ℝ) + 1) / Real.log 21 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((22 : ℕ).primeCounting : ℝ) = 8 := by rw [primeCounting_22]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 22 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 22 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 22)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : ((22 : ℝ) + 1) / Real.log 22 < ((22 : ℝ) + 1) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((22 : ℝ) + 1) / ((3 : ℝ) / 1) < 8 := by field_simp; norm_num
    have hsucc : ((22 : ℝ) + 1) / Real.log 22 < 8 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((22 : ℝ) + 1) / Real.log 22 := by
      have h1 : x / Real.log x < ((22 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((22 : ℝ) + 1) / Real.log x ≤ ((22 : ℝ) + 1) / Real.log 22 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((23 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_23]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 23 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 23 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 23)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : ((23 : ℝ) + 1) / Real.log 23 < ((23 : ℝ) + 1) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((23 : ℝ) + 1) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    have hsucc : ((23 : ℝ) + 1) / Real.log 23 < 9 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((23 : ℝ) + 1) / Real.log 23 := by
      have h1 : x / Real.log x < ((23 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((23 : ℝ) + 1) / Real.log x ≤ ((23 : ℝ) + 1) / Real.log 23 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((24 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_24]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 24 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 24 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 24)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : ((24 : ℝ) + 1) / Real.log 24 < ((24 : ℝ) + 1) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((24 : ℝ) + 1) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    have hsucc : ((24 : ℝ) + 1) / Real.log 24 < 9 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((24 : ℝ) + 1) / Real.log 24 := by
      have h1 : x / Real.log x < ((24 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((24 : ℝ) + 1) / Real.log x ≤ ((24 : ℝ) + 1) / Real.log 24 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((25 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_25]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 25 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 25 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 25)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : ((25 : ℝ) + 1) / Real.log 25 < ((25 : ℝ) + 1) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((25 : ℝ) + 1) / ((3 : ℝ) / 1) < 9 := by field_simp; norm_num
    have hsucc : ((25 : ℝ) + 1) / Real.log 25 < 9 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((25 : ℝ) + 1) / Real.log 25 := by
      have h1 : x / Real.log x < ((25 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((25 : ℝ) + 1) / Real.log x ≤ ((25 : ℝ) + 1) / Real.log 25 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((26 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_26]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 26 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 26 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 26)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((26 : ℝ) + 1) / Real.log 26 < ((26 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((26 : ℝ) + 1) / ((13 : ℝ) / 4) < 9 := by field_simp; norm_num
    have hsucc : ((26 : ℝ) + 1) / Real.log 26 < 9 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((26 : ℝ) + 1) / Real.log 26 := by
      have h1 : x / Real.log x < ((26 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((26 : ℝ) + 1) / Real.log x ≤ ((26 : ℝ) + 1) / Real.log 26 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((27 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_27]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 27 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 27 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 27)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((27 : ℝ) + 1) / Real.log 27 < ((27 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((27 : ℝ) + 1) / ((13 : ℝ) / 4) < 9 := by field_simp; norm_num
    have hsucc : ((27 : ℝ) + 1) / Real.log 27 < 9 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((27 : ℝ) + 1) / Real.log 27 := by
      have h1 : x / Real.log x < ((27 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((27 : ℝ) + 1) / Real.log x ≤ ((27 : ℝ) + 1) / Real.log 27 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((28 : ℕ).primeCounting : ℝ) = 9 := by rw [primeCounting_28]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 28 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 28 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 28)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((28 : ℝ) + 1) / Real.log 28 < ((28 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((28 : ℝ) + 1) / ((13 : ℝ) / 4) < 9 := by field_simp; norm_num
    have hsucc : ((28 : ℝ) + 1) / Real.log 28 < 9 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((28 : ℝ) + 1) / Real.log 28 := by
      have h1 : x / Real.log x < ((28 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((28 : ℝ) + 1) / Real.log x ≤ ((28 : ℝ) + 1) / Real.log 28 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((29 : ℕ).primeCounting : ℝ) = 10 := by rw [primeCounting_29]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 29 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 29 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 29)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((29 : ℝ) + 1) / Real.log 29 < ((29 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((29 : ℝ) + 1) / ((13 : ℝ) / 4) < 10 := by field_simp; norm_num
    have hsucc : ((29 : ℝ) + 1) / Real.log 29 < 10 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((29 : ℝ) + 1) / Real.log 29 := by
      have h1 : x / Real.log x < ((29 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((29 : ℝ) + 1) / Real.log x ≤ ((29 : ℝ) + 1) / Real.log 29 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((30 : ℕ).primeCounting : ℝ) = 10 := by rw [primeCounting_30]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 30 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 30 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 30)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((30 : ℝ) + 1) / Real.log 30 < ((30 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((30 : ℝ) + 1) / ((13 : ℝ) / 4) < 10 := by field_simp; norm_num
    have hsucc : ((30 : ℝ) + 1) / Real.log 30 < 10 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((30 : ℝ) + 1) / Real.log 30 := by
      have h1 : x / Real.log x < ((30 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((30 : ℝ) + 1) / Real.log x ≤ ((30 : ℝ) + 1) / Real.log 30 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((31 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_31]; norm_num
    have hexp : Real.exp ((3 : ℝ) / 1) < 31 := by interval_decide
    have hlog : (3 : ℝ) / 1 < Real.log 31 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 31)).mpr hexp
    have hqpos : (0 : ℝ) < (3 : ℝ) / 1 := by positivity
    have hdiv : ((31 : ℝ) + 1) / Real.log 31 < ((31 : ℝ) + 1) / ((3 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((31 : ℝ) + 1) / ((3 : ℝ) / 1) < 11 := by field_simp; norm_num
    have hsucc : ((31 : ℝ) + 1) / Real.log 31 < 11 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((31 : ℝ) + 1) / Real.log 31 := by
      have h1 : x / Real.log x < ((31 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((31 : ℝ) + 1) / Real.log x ≤ ((31 : ℝ) + 1) / Real.log 31 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((32 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_32]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 32 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 32 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 32)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((32 : ℝ) + 1) / Real.log 32 < ((32 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((32 : ℝ) + 1) / ((13 : ℝ) / 4) < 11 := by field_simp; norm_num
    have hsucc : ((32 : ℝ) + 1) / Real.log 32 < 11 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((32 : ℝ) + 1) / Real.log 32 := by
      have h1 : x / Real.log x < ((32 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((32 : ℝ) + 1) / Real.log x ≤ ((32 : ℝ) + 1) / Real.log 32 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((33 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_33]; norm_num
    have hexp : Real.exp ((13 : ℝ) / 4) < 33 := by interval_decide
    have hlog : (13 : ℝ) / 4 < Real.log 33 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 33)).mpr hexp
    have hqpos : (0 : ℝ) < (13 : ℝ) / 4 := by positivity
    have hdiv : ((33 : ℝ) + 1) / Real.log 33 < ((33 : ℝ) + 1) / ((13 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((33 : ℝ) + 1) / ((13 : ℝ) / 4) < 11 := by field_simp; norm_num
    have hsucc : ((33 : ℝ) + 1) / Real.log 33 < 11 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((33 : ℝ) + 1) / Real.log 33 := by
      have h1 : x / Real.log x < ((33 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((33 : ℝ) + 1) / Real.log x ≤ ((33 : ℝ) + 1) / Real.log 33 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((34 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_34]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 34 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 34 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 34)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((34 : ℝ) + 1) / Real.log 34 < ((34 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((34 : ℝ) + 1) / ((7 : ℝ) / 2) < 11 := by field_simp; norm_num
    have hsucc : ((34 : ℝ) + 1) / Real.log 34 < 11 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((34 : ℝ) + 1) / Real.log 34 := by
      have h1 : x / Real.log x < ((34 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((34 : ℝ) + 1) / Real.log x ≤ ((34 : ℝ) + 1) / Real.log 34 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((35 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_35]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 35 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 35 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 35)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((35 : ℝ) + 1) / Real.log 35 < ((35 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((35 : ℝ) + 1) / ((7 : ℝ) / 2) < 11 := by field_simp; norm_num
    have hsucc : ((35 : ℝ) + 1) / Real.log 35 < 11 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((35 : ℝ) + 1) / Real.log 35 := by
      have h1 : x / Real.log x < ((35 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((35 : ℝ) + 1) / Real.log x ≤ ((35 : ℝ) + 1) / Real.log 35 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((36 : ℕ).primeCounting : ℝ) = 11 := by rw [primeCounting_36]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 36 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 36 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 36)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((36 : ℝ) + 1) / Real.log 36 < ((36 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((36 : ℝ) + 1) / ((7 : ℝ) / 2) < 11 := by field_simp; norm_num
    have hsucc : ((36 : ℝ) + 1) / Real.log 36 < 11 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((36 : ℝ) + 1) / Real.log 36 := by
      have h1 : x / Real.log x < ((36 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((36 : ℝ) + 1) / Real.log x ≤ ((36 : ℝ) + 1) / Real.log 36 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((37 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_37]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 37 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 37 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 37)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((37 : ℝ) + 1) / Real.log 37 < ((37 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((37 : ℝ) + 1) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    have hsucc : ((37 : ℝ) + 1) / Real.log 37 < 12 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((37 : ℝ) + 1) / Real.log 37 := by
      have h1 : x / Real.log x < ((37 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((37 : ℝ) + 1) / Real.log x ≤ ((37 : ℝ) + 1) / Real.log 37 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((38 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_38]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 38 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 38 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 38)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((38 : ℝ) + 1) / Real.log 38 < ((38 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((38 : ℝ) + 1) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    have hsucc : ((38 : ℝ) + 1) / Real.log 38 < 12 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((38 : ℝ) + 1) / Real.log 38 := by
      have h1 : x / Real.log x < ((38 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((38 : ℝ) + 1) / Real.log x ≤ ((38 : ℝ) + 1) / Real.log 38 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((39 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_39]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 39 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 39 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 39)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((39 : ℝ) + 1) / Real.log 39 < ((39 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((39 : ℝ) + 1) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    have hsucc : ((39 : ℝ) + 1) / Real.log 39 < 12 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((39 : ℝ) + 1) / Real.log 39 := by
      have h1 : x / Real.log x < ((39 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((39 : ℝ) + 1) / Real.log x ≤ ((39 : ℝ) + 1) / Real.log 39 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((40 : ℕ).primeCounting : ℝ) = 12 := by rw [primeCounting_40]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 40 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 40 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 40)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((40 : ℝ) + 1) / Real.log 40 < ((40 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((40 : ℝ) + 1) / ((7 : ℝ) / 2) < 12 := by field_simp; norm_num
    have hsucc : ((40 : ℝ) + 1) / Real.log 40 < 12 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((40 : ℝ) + 1) / Real.log 40 := by
      have h1 : x / Real.log x < ((40 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((40 : ℝ) + 1) / Real.log x ≤ ((40 : ℝ) + 1) / Real.log 40 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((41 : ℕ).primeCounting : ℝ) = 13 := by rw [primeCounting_41]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 41 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 41 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 41)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((41 : ℝ) + 1) / Real.log 41 < ((41 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((41 : ℝ) + 1) / ((7 : ℝ) / 2) < 13 := by field_simp; norm_num
    have hsucc : ((41 : ℝ) + 1) / Real.log 41 < 13 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((41 : ℝ) + 1) / Real.log 41 := by
      have h1 : x / Real.log x < ((41 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((41 : ℝ) + 1) / Real.log x ≤ ((41 : ℝ) + 1) / Real.log 41 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((42 : ℕ).primeCounting : ℝ) = 13 := by rw [primeCounting_42]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 42 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 42 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 42)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((42 : ℝ) + 1) / Real.log 42 < ((42 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((42 : ℝ) + 1) / ((7 : ℝ) / 2) < 13 := by field_simp; norm_num
    have hsucc : ((42 : ℝ) + 1) / Real.log 42 < 13 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((42 : ℝ) + 1) / Real.log 42 := by
      have h1 : x / Real.log x < ((42 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((42 : ℝ) + 1) / Real.log x ≤ ((42 : ℝ) + 1) / Real.log 42 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((43 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_43]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 43 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 43 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 43)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((43 : ℝ) + 1) / Real.log 43 < ((43 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((43 : ℝ) + 1) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    have hsucc : ((43 : ℝ) + 1) / Real.log 43 < 14 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((43 : ℝ) + 1) / Real.log 43 := by
      have h1 : x / Real.log x < ((43 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((43 : ℝ) + 1) / Real.log x ≤ ((43 : ℝ) + 1) / Real.log 43 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((44 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_44]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 44 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 44 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 44)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((44 : ℝ) + 1) / Real.log 44 < ((44 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((44 : ℝ) + 1) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    have hsucc : ((44 : ℝ) + 1) / Real.log 44 < 14 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((44 : ℝ) + 1) / Real.log 44 := by
      have h1 : x / Real.log x < ((44 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((44 : ℝ) + 1) / Real.log x ≤ ((44 : ℝ) + 1) / Real.log 44 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((45 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_45]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 45 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 45 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 45)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((45 : ℝ) + 1) / Real.log 45 < ((45 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((45 : ℝ) + 1) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    have hsucc : ((45 : ℝ) + 1) / Real.log 45 < 14 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((45 : ℝ) + 1) / Real.log 45 := by
      have h1 : x / Real.log x < ((45 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((45 : ℝ) + 1) / Real.log x ≤ ((45 : ℝ) + 1) / Real.log 45 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((46 : ℕ).primeCounting : ℝ) = 14 := by rw [primeCounting_46]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 46 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 46 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 46)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((46 : ℝ) + 1) / Real.log 46 < ((46 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((46 : ℝ) + 1) / ((7 : ℝ) / 2) < 14 := by field_simp; norm_num
    have hsucc : ((46 : ℝ) + 1) / Real.log 46 < 14 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((46 : ℝ) + 1) / Real.log 46 := by
      have h1 : x / Real.log x < ((46 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((46 : ℝ) + 1) / Real.log x ≤ ((46 : ℝ) + 1) / Real.log 46 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((47 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_47]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 47 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 47 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 47)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((47 : ℝ) + 1) / Real.log 47 < ((47 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((47 : ℝ) + 1) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    have hsucc : ((47 : ℝ) + 1) / Real.log 47 < 15 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((47 : ℝ) + 1) / Real.log 47 := by
      have h1 : x / Real.log x < ((47 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((47 : ℝ) + 1) / Real.log x ≤ ((47 : ℝ) + 1) / Real.log 47 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((48 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_48]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 48 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 48 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 48)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((48 : ℝ) + 1) / Real.log 48 < ((48 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((48 : ℝ) + 1) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    have hsucc : ((48 : ℝ) + 1) / Real.log 48 < 15 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((48 : ℝ) + 1) / Real.log 48 := by
      have h1 : x / Real.log x < ((48 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((48 : ℝ) + 1) / Real.log x ≤ ((48 : ℝ) + 1) / Real.log 48 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((49 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_49]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 49 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 49 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 49)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((49 : ℝ) + 1) / Real.log 49 < ((49 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((49 : ℝ) + 1) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    have hsucc : ((49 : ℝ) + 1) / Real.log 49 < 15 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((49 : ℝ) + 1) / Real.log 49 := by
      have h1 : x / Real.log x < ((49 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((49 : ℝ) + 1) / Real.log x ≤ ((49 : ℝ) + 1) / Real.log 49 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((50 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_50]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 50 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 50 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 50)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((50 : ℝ) + 1) / Real.log 50 < ((50 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((50 : ℝ) + 1) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    have hsucc : ((50 : ℝ) + 1) / Real.log 50 < 15 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((50 : ℝ) + 1) / Real.log 50 := by
      have h1 : x / Real.log x < ((50 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((50 : ℝ) + 1) / Real.log x ≤ ((50 : ℝ) + 1) / Real.log 50 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((51 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_51]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 51 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 51 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 51)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((51 : ℝ) + 1) / Real.log 51 < ((51 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((51 : ℝ) + 1) / ((7 : ℝ) / 2) < 15 := by field_simp; norm_num
    have hsucc : ((51 : ℝ) + 1) / Real.log 51 < 15 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((51 : ℝ) + 1) / Real.log 51 := by
      have h1 : x / Real.log x < ((51 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((51 : ℝ) + 1) / Real.log x ≤ ((51 : ℝ) + 1) / Real.log 51 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((52 : ℕ).primeCounting : ℝ) = 15 := by rw [primeCounting_52]; norm_num
    have hexp : Real.exp ((15 : ℝ) / 4) < 52 := by interval_decide
    have hlog : (15 : ℝ) / 4 < Real.log 52 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 52)).mpr hexp
    have hqpos : (0 : ℝ) < (15 : ℝ) / 4 := by positivity
    have hdiv : ((52 : ℝ) + 1) / Real.log 52 < ((52 : ℝ) + 1) / ((15 : ℝ) / 4) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((52 : ℝ) + 1) / ((15 : ℝ) / 4) < 15 := by field_simp; norm_num
    have hsucc : ((52 : ℝ) + 1) / Real.log 52 < 15 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((52 : ℝ) + 1) / Real.log 52 := by
      have h1 : x / Real.log x < ((52 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((52 : ℝ) + 1) / Real.log x ≤ ((52 : ℝ) + 1) / Real.log 52 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((53 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_53]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 53 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 53 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 53)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((53 : ℝ) + 1) / Real.log 53 < ((53 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((53 : ℝ) + 1) / ((7 : ℝ) / 2) < 16 := by field_simp; norm_num
    have hsucc : ((53 : ℝ) + 1) / Real.log 53 < 16 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((53 : ℝ) + 1) / Real.log 53 := by
      have h1 : x / Real.log x < ((53 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((53 : ℝ) + 1) / Real.log x ≤ ((53 : ℝ) + 1) / Real.log 53 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((54 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_54]; norm_num
    have hexp : Real.exp ((7 : ℝ) / 2) < 54 := by interval_decide
    have hlog : (7 : ℝ) / 2 < Real.log 54 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 54)).mpr hexp
    have hqpos : (0 : ℝ) < (7 : ℝ) / 2 := by positivity
    have hdiv : ((54 : ℝ) + 1) / Real.log 54 < ((54 : ℝ) + 1) / ((7 : ℝ) / 2) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((54 : ℝ) + 1) / ((7 : ℝ) / 2) < 16 := by field_simp; norm_num
    have hsucc : ((54 : ℝ) + 1) / Real.log 54 < 16 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((54 : ℝ) + 1) / Real.log 54 := by
      have h1 : x / Real.log x < ((54 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((54 : ℝ) + 1) / Real.log x ≤ ((54 : ℝ) + 1) / Real.log 54 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((55 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_55]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 55 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 55 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 55)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : ((55 : ℝ) + 1) / Real.log 55 < ((55 : ℝ) + 1) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((55 : ℝ) + 1) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    have hsucc : ((55 : ℝ) + 1) / Real.log 55 < 16 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((55 : ℝ) + 1) / Real.log 55 := by
      have h1 : x / Real.log x < ((55 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((55 : ℝ) + 1) / Real.log x ≤ ((55 : ℝ) + 1) / Real.log 55 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((56 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_56]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 56 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 56 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 56)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : ((56 : ℝ) + 1) / Real.log 56 < ((56 : ℝ) + 1) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((56 : ℝ) + 1) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    have hsucc : ((56 : ℝ) + 1) / Real.log 56 < 16 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((56 : ℝ) + 1) / Real.log 56 := by
      have h1 : x / Real.log x < ((56 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((56 : ℝ) + 1) / Real.log x ≤ ((56 : ℝ) + 1) / Real.log 56 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((57 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_57]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 57 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 57 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 57)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : ((57 : ℝ) + 1) / Real.log 57 < ((57 : ℝ) + 1) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((57 : ℝ) + 1) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    have hsucc : ((57 : ℝ) + 1) / Real.log 57 < 16 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((57 : ℝ) + 1) / Real.log 57 := by
      have h1 : x / Real.log x < ((57 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((57 : ℝ) + 1) / Real.log x ≤ ((57 : ℝ) + 1) / Real.log 57 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((58 : ℕ).primeCounting : ℝ) = 16 := by rw [primeCounting_58]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 58 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 58 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 58)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : ((58 : ℝ) + 1) / Real.log 58 < ((58 : ℝ) + 1) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((58 : ℝ) + 1) / ((4 : ℝ) / 1) < 16 := by field_simp; norm_num
    have hsucc : ((58 : ℝ) + 1) / Real.log 58 < 16 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((58 : ℝ) + 1) / Real.log 58 := by
      have h1 : x / Real.log x < ((58 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((58 : ℝ) + 1) / Real.log x ≤ ((58 : ℝ) + 1) / Real.log 58 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((59 : ℕ).primeCounting : ℝ) = 17 := by rw [primeCounting_59]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 59 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 59 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 59)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : ((59 : ℝ) + 1) / Real.log 59 < ((59 : ℝ) + 1) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((59 : ℝ) + 1) / ((4 : ℝ) / 1) < 17 := by field_simp; norm_num
    have hsucc : ((59 : ℝ) + 1) / Real.log 59 < 17 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((59 : ℝ) + 1) / Real.log 59 := by
      have h1 : x / Real.log x < ((59 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((59 : ℝ) + 1) / Real.log x ≤ ((59 : ℝ) + 1) / Real.log 59 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc
  · have hpi : ((60 : ℕ).primeCounting : ℝ) = 17 := by rw [primeCounting_60]; norm_num
    have hexp : Real.exp ((4 : ℝ) / 1) < 60 := by interval_decide
    have hlog : (4 : ℝ) / 1 < Real.log 60 :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 60)).mpr hexp
    have hqpos : (0 : ℝ) < (4 : ℝ) / 1 := by positivity
    have hdiv : ((60 : ℝ) + 1) / Real.log 60 < ((60 : ℝ) + 1) / ((4 : ℝ) / 1) :=
      div_lt_div_of_pos_left (by positivity) hqpos hlog
    have hcmp : ((60 : ℝ) + 1) / ((4 : ℝ) / 1) < 17 := by field_simp; norm_num
    have hsucc : ((60 : ℝ) + 1) / Real.log 60 < 17 := lt_trans hdiv hcmp
    have hxbound : x / Real.log x < ((60 : ℝ) + 1) / Real.log 60 := by
      have h1 : x / Real.log x < ((60 : ℝ) + 1) / Real.log x :=
        div_lt_div_of_pos_right hxlt hlogx
      have h2 : ((60 : ℝ) + 1) / Real.log x ≤ ((60 : ℝ) + 1) / Real.log 60 :=
        div_le_div_of_nonneg_left (by positivity) hlogn
          (Real.log_le_log hnpos hnx)
      exact lt_of_lt_of_le h1 h2
    exact hpi ▸ lt_trans hxbound hsucc

end RS_prime
