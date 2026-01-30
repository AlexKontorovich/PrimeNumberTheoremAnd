import Architect
import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime_tables
import PrimeNumberTheoremAnd.BKLNW_app_tables


blueprint_comment /--
\section{Numerical content of BKLNW}

Purely numerical calculations from \cite{BKLNW}.  This is kept in a separate file from the main file to avoid heavy recompilations.  Because of this, this file should not import any other files from the PNT+ project, other than further numerical data files.

-/

namespace BKLNW

open Real

/-- Add a margin to the values in Table 14 to account for numerical errors. -/
abbrev Table_14_margin : ℝ := BKLNW_app.table_8_margin * 1.001


noncomputable def Table_14 : List (ℝ × ℝ × ℝ) := [
  (20, 4.2676e-5 * Table_14_margin, 9.1639e-5 * Table_14_margin),
  (25, 3.5031e-6 * Table_14_margin, 7.4366e-6 * Table_14_margin),
  (30, 2.8755e-7 * Table_14_margin, 6.0751e-7 * Table_14_margin),
  (35, 2.3603e-8 * Table_14_margin, 4.9766e-8 * Table_14_margin),
  (40, 1.9338e-8 * Table_14_margin, 2.1482e-8 * Table_14_margin),
  (19 * log 10, 1.9338e-8 * Table_14_margin, 1.9667e-8 * Table_14_margin),
  (45, 1.0907e-8 * Table_14_margin, 1.1084e-8 * Table_14_margin),
  (50, 1.1199e-9 * Table_14_margin, 1.1344e-9 * Table_14_margin),
  (60, 1.2215e-11 * Table_14_margin, 1.2312e-11 * Table_14_margin),
  (70, 2.7923e-12 * Table_14_margin, 2.7930e-12 * Table_14_margin),
  (80, 2.6108e-12 * Table_14_margin, 2.6108e-12 * Table_14_margin),
  (90, 2.5213e-12 * Table_14_margin, 2.5213e-12 * Table_14_margin),
  (100, 2.4530e-12 * Table_14_margin, 2.4530e-12 * Table_14_margin),
  (200, 2.1815e-12 * Table_14_margin, 2.1816e-12 * Table_14_margin),
  (300, 2.0902e-12 * Table_14_margin, 2.0903e-12 * Table_14_margin),
  (400, 2.0398e-12 * Table_14_margin, 2.0399e-12 * Table_14_margin),
  (500, 1.9999e-12 * Table_14_margin, 1.9999e-12 * Table_14_margin),
  (700, 1.9764e-12 * Table_14_margin, 1.9765e-12 * Table_14_margin),
  (1000, 1.9475e-12 * Table_14_margin, 1.9476e-12 * Table_14_margin),
  (2000, 1.9228e-12 * Table_14_margin, 1.9228e-12 * Table_14_margin),
  (3000, 4.5997e-14 * Table_14_margin, 4.5998e-14 * Table_14_margin),
  (4000, 1.4263e-16 * Table_14_margin, 1.4264e-16 * Table_14_margin),
  (5000, 5.6303e-19 * Table_14_margin, 5.6303e-19 * Table_14_margin),
  (7000, 2.0765e-23 * Table_14_margin, 2.0766e-23 * Table_14_margin),
  (10000, 3.7849e-29 * Table_14_margin, 3.7850e-29 * Table_14_margin),
  (11000, 7.1426e-31 * Table_14_margin, 7.1427e-31 * Table_14_margin),
  (12000, 1.5975e-32 * Table_14_margin, 1.5976e-32 * Table_14_margin),
  (13000, 4.1355e-34 * Table_14_margin, 4.1356e-34 * Table_14_margin),
  (13800.7464, 2.5423e-35 * Table_14_margin, 2.5424e-35 * Table_14_margin),
  (15000, 4.1070e-37 * Table_14_margin, 4.1070e-37 * Table_14_margin),
  (17000, 6.2040e-40 * Table_14_margin, 6.2040e-40 * Table_14_margin),
  (20000, 7.1621e-44 * Table_14_margin, 7.1621e-44 * Table_14_margin),
  (22000, 2.4392e-46 * Table_14_margin, 2.4392e-46 * Table_14_margin),
  (25000, 7.5724e-50 * Table_14_margin, 7.5724e-50 * Table_14_margin)
]

def check_row_prop (row : ℝ × ℝ × ℝ) : Prop :=
  let (b, M, m) := row
  20 ≤ b ∧
  BKLNW_app.table_8_ε b ≤ M ∧
  BKLNW_app.table_8_ε b + RS_prime.c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5)) ≤ m

-- This lemma no longer works because we changed the definition of table_8_ε to use sInf.  It may be safely deleted.
--
-- lemma row_1_checked : check_row_prop (20, 4.2676e-5, 9.1639e-5) := by
--   norm_num [check_row_prop, BKLNW_app.table_8_ε, RS_prime.c₀]
--   rw [← neg_one_mul 10, ← neg_one_mul (40 / 3), ← neg_one_mul 16, exp_mul, exp_mul, exp_mul]
--   grw [exp_neg_one_lt_d9]
--   suffices (0.3678794412 : ℝ) ^ (40 / 3 : ℝ) < 0.00000162 by grw [this]; norm_num only
--   rw [← pow_lt_pow_iff_left₀ (by positivity) (n := 3), ← rpow_mul_natCast] <;> norm_num only

@[blueprint
  "bklnw-table-14-check"
  (statement := /-- The entries in Table 14 obey the criterion in Sublemma \ref{bklnw-thm-1a-checked}. -/)
  (latexEnv := "sublemma")
  (discussion := 808)]
theorem table_14_check {b M m : ℝ} (h_table : (b, M, m) ∈ Table_14) : check_row_prop (b, M, m) := by sorry



end BKLNW
