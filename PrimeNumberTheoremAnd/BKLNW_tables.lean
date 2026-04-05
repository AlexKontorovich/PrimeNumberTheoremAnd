import Architect
import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime_tables
import PrimeNumberTheoremAnd.BKLNW_app_tables
import PrimeNumberTheoremAnd.LogTables


blueprint_comment /--
\section{Numerical content of BKLNW}

Purely numerical calculations from \cite{BKLNW}.  This is kept in a separate file from the main file to avoid heavy recompilations.  Because of this, this file should not import any other files from the PNT+ project, other than further numerical data files.

-/

namespace BKLNW

open Real

/-- Add a margin to the values in Table 14 to account for numerical errors. -/
abbrev table_14_margin : ℝ := BKLNW_app.table_8_margin * 1.001

noncomputable def table_14 : List (ℝ × ℝ × ℝ) := [
  (20, 4.2676e-5 * table_14_margin, 9.1639e-5 * table_14_margin),
  (25, 3.5031e-6 * table_14_margin, 7.4366e-6 * table_14_margin),
  (30, 2.8755e-7 * table_14_margin, 6.0751e-7 * table_14_margin),
  (35, 2.3603e-8 * table_14_margin, 4.9766e-8 * table_14_margin),
  (40, 1.9338e-8 * table_14_margin, 2.1482e-8 * table_14_margin),
  (19 * log 10, 1.9338e-8 * table_14_margin, 1.9667e-8 * table_14_margin),
  (45, 1.0907e-8 * table_14_margin, 1.1084e-8 * table_14_margin),
  (50, 1.1199e-9 * table_14_margin, 1.1344e-9 * table_14_margin),
  (60, 1.2215e-11 * table_14_margin, 1.2312e-11 * table_14_margin),
  (70, 2.7923e-12 * table_14_margin, 2.7930e-12 * table_14_margin),
  (80, 2.6108e-12 * table_14_margin, 2.6108e-12 * table_14_margin),
  (90, 2.5213e-12 * table_14_margin, 2.5213e-12 * table_14_margin),
  (100, 2.4530e-12 * table_14_margin, 2.4530e-12 * table_14_margin),
  (200, 2.1815e-12 * table_14_margin, 2.1816e-12 * table_14_margin),
  (300, 2.0902e-12 * table_14_margin, 2.0903e-12 * table_14_margin),
  (400, 2.0398e-12 * table_14_margin, 2.0399e-12 * table_14_margin),
  (500, 1.9999e-12 * table_14_margin, 1.9999e-12 * table_14_margin),
  (700, 1.9764e-12 * table_14_margin, 1.9765e-12 * table_14_margin),
  (1000, 1.9475e-12 * table_14_margin, 1.9476e-12 * table_14_margin),
  (2000, 1.9228e-12 * table_14_margin, 1.9228e-12 * table_14_margin),
  (3000, 4.5997e-14 * table_14_margin, 4.5998e-14 * table_14_margin),
  (4000, 1.4263e-16 * table_14_margin, 1.4264e-16 * table_14_margin),
  (5000, 5.6303e-19 * table_14_margin, 5.6303e-19 * table_14_margin),
  (7000, 2.0765e-23 * table_14_margin, 2.0766e-23 * table_14_margin),
  (10000, 3.7849e-29 * table_14_margin, 3.7850e-29 * table_14_margin),
  (11000, 7.1426e-31 * table_14_margin, 7.1427e-31 * table_14_margin),
  (12000, 1.5975e-32 * table_14_margin, 1.5976e-32 * table_14_margin),
  (13000, 4.1355e-34 * table_14_margin, 4.1356e-34 * table_14_margin),
  (13800.7464, 2.5423e-35 * table_14_margin, 2.5424e-35 * table_14_margin),
  (15000, 4.1070e-37 * table_14_margin, 4.1070e-37 * table_14_margin),
  (17000, 6.2040e-40 * table_14_margin, 6.2040e-40 * table_14_margin),
  (20000, 7.1621e-44 * table_14_margin, 7.1621e-44 * table_14_margin),
  (22000, 2.4392e-46 * table_14_margin, 2.4392e-46 * table_14_margin),
  (25000, 7.5724e-50 * table_14_margin, 7.5724e-50 * table_14_margin)
]

def check_row_prop (row : ℝ × ℝ × ℝ) : Prop :=
  let (b, M, m) := row
  20 ≤ b ∧
  BKLNW_app.table_8_ε b ≤ M ∧
  BKLNW_app.table_8_ε b + RS_prime.c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5)) ≤ m

/-- Upper bound used for `exp (-1)` in numerical estimates. -/
abbrev exp_neg_one_ub : ℝ := 0.3678794412

lemma exp_neg_le_rpow (x : ℝ) (hx : 0 ≤ x) : exp (-x) ≤ exp_neg_one_ub ^ x := by
  have hmul : (-1 : ℝ) * x = -x := by ring
  have h1 : exp (-x) = exp (-1) ^ x := by
    simpa [hmul] using (Real.exp_mul (-1) x)
  have hbase : exp (-1) ≤ exp_neg_one_ub := by
    exact le_of_lt Real.exp_neg_one_lt_d9
  have hpos : 0 ≤ exp (-1) := by positivity
  calc
    exp (-x) = exp (-1) ^ x := h1
    _ ≤ exp_neg_one_ub ^ x := by
      exact rpow_le_rpow hpos hbase hx

lemma exp_neg_le_rpow' (x : ℝ) (hx : 0 ≤ x) : exp (-x) ≤ exp_neg_one_ub ^ x := by
  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using exp_neg_le_rpow (x:=x) hx

lemma rpow_le_of_pow_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {p q : ℕ} (hq : q ≠ 0)
    (h : a ^ p ≤ c ^ q) : a ^ (p / (q : ℝ)) ≤ c := by
  have hpow : (a ^ (p / (q : ℝ))) ^ q = a ^ p := by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    calc
      (a ^ (p / (q : ℝ))) ^ q = a ^ ((p / (q : ℝ)) * q) := by
        symm
        exact Real.rpow_mul_natCast ha (p / (q : ℝ)) q
      _ = a ^ (p : ℝ) := by
        field_simp [hq']
      _ = a ^ p := by
        simp [Real.rpow_natCast]
  have h' : (a ^ (p / (q : ℝ))) ^ q ≤ c ^ q := by
    simpa [hpow] using h
  exact (pow_le_pow_iff_left₀ (by positivity) hc hq).1 h'

lemma exp_neg_le_pow (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) : exp (-x) ≤ exp_neg_one_ub ^ n := by
  have h1 : exp (-x) ≤ exp (-(n : ℝ)) := by
    have : -x ≤ -(n : ℝ) := by linarith
    exact (Real.exp_le_exp).2 this
  have hbase : exp (-1) ≤ exp_neg_one_ub := by
    exact le_of_lt Real.exp_neg_one_lt_d9
  have hpos : 0 ≤ exp (-1) := by positivity
  have hExp : exp (-(n : ℝ)) = exp (-1) ^ n := by
    have hmul : (n : ℝ) * (-1) = -(n : ℝ) := by ring
    simpa [hmul] using (Real.exp_nat_mul (-1) n)
  calc
    exp (-x) ≤ exp (-(n : ℝ)) := h1
    _ = exp (-1) ^ n := hExp
    _ ≤ exp_neg_one_ub ^ n := by
      exact pow_le_pow_left₀ hpos hbase n

lemma exp_neg_le_pow' (n : ℕ) {x : ℝ} (hx : (n : ℝ) ≤ x) : exp (-x) ≤ exp_neg_one_ub ^ n := by
  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using exp_neg_le_pow (n:=n) (x:=x) hx

lemma check_row_prop_of_bounds {b M m eps c1 c2 c3 : ℝ}
    (hb : 20 ≤ b)
    (h_eps : BKLNW_app.table_8_ε b ≤ eps)
    (h_epsM : eps ≤ M)
    (h1 : exp (-b / 2) ≤ c1)
    (h2 : exp (-2 * b / 3) ≤ c2)
    (h3 : exp (-4 * b / 5) ≤ c3)
    (hbound : eps + RS_prime.c₀ * (c1 + c2 + c3) ≤ m) :
    check_row_prop (b, M, m) := by
  refine ⟨hb, ?_, ?_⟩
  · exact le_trans h_eps h_epsM
  · have hc0 : 0 ≤ RS_prime.c₀ := by norm_num [RS_prime.c₀]
    have hsum : exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5) ≤ c1 + c2 + c3 := by
      linarith [h1, h2, h3]
    have hsum' : RS_prime.c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5)) ≤
        RS_prime.c₀ * (c1 + c2 + c3) := by
      exact mul_le_mul_of_nonneg_left hsum hc0
    have hmain : BKLNW_app.table_8_ε b + RS_prime.c₀ *
        (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5)) ≤
        eps + RS_prime.c₀ * (c1 + c2 + c3) := by
      linarith [h_eps, hsum']
    exact hmain.trans hbound

-- This lemma no longer works because we changed the definition of table_8_ε to use sInf.  It may be safely deleted.
--
-- lemma row_1_checked : check_row_prop (20, 4.2676e-5, 9.1639e-5) := by
--   norm_num [check_row_prop, BKLNW_app.table_8_ε, RS_prime.c₀]
--   rw [← neg_one_mul 10, ← neg_one_mul (40 / 3), ← neg_one_mul 16, exp_mul, exp_mul, exp_mul]
--   grw [exp_neg_one_lt_d9]
--   suffices (0.3678794412 : ℝ) ^ (40 / 3 : ℝ) < 0.00000162 by grw [this]; norm_num only
--   rw [← pow_lt_pow_iff_left₀ (by positivity) (n := 3), ← rpow_mul_natCast] <;> norm_num only

set_option maxRecDepth 10000 in
@[blueprint
  "bklnw-table-14-check"
  (statement := /-- The entries in Table 14 obey the criterion in Sublemma \ref{bklnw-thm-1a-checked}. -/)
  (latexEnv := "sublemma")
  (discussion := 808)]
theorem table_14_check {b M m : ℝ} (h_table : (b, M, m) ∈ table_14) : check_row_prop (b, M, m) := by
  classical
  simp only [table_14, List.mem_cons, List.not_mem_nil, or_false] at h_table
  rcases h_table with h_table | h_table
  · rcases h_table with ⟨rfl, rfl, rfl⟩
    have hb : (20 : ℝ) ≤ 20 := by norm_num
    have hrow : BKLNW_app.table_8_ε 20 ≤ 4.2676e-5 :=
      BKLNW_app.table_8_ε_le_of_row (b₀ := 20) (ε := 4.2676e-5) (BKLNW_app.table_8_mem_20) (by exact le_rfl)
    have h_epsM : (4.2676e-5 : ℝ) ≤ 4.2676e-5 * table_14_margin := by norm_num [table_14_margin]
    have h1 : exp (-20 / 2) ≤ exp_neg_one_ub ^ 10 := by
      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=10) (x:=20/2) (by norm_num))
    have h2 : exp (-2 * 20 / 3) ≤ 1.62e-6 := by
      have h2' : exp (-2 * 20 / 3) ≤ exp_neg_one_ub ^ ((40:ℝ) / 3) := by
        have hx : (2:ℝ) * 20 / 3 = (40:ℝ) / 3 := by ring
        simpa [hx, neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
          (exp_neg_le_rpow' (x:=2*20/3) (by norm_num))
      have h2'' : exp_neg_one_ub ^ ((40:ℝ) / 3) ≤ 1.62e-6 := by
        have ha : 0 ≤ exp_neg_one_ub := by norm_num [exp_neg_one_ub]
        have hc : 0 ≤ (1.62e-6 : ℝ) := by norm_num
        refine rpow_le_of_pow_le (a:=exp_neg_one_ub) (c:=1.62e-6) ha hc (p:=40) (q:=3)
          (by norm_num) ?_
        norm_num [exp_neg_one_ub]
      exact h2'.trans h2''
    have h3 : exp (-4 * 20 / 5) ≤ exp_neg_one_ub ^ 16 := by
      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=16) (x:=4*20/5) (by norm_num))
    have hbound : (4.2676e-5 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 10 + 1.62e-6 + exp_neg_one_ub ^ 16) ≤ 9.1639e-5 * table_14_margin := by
      norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
    exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
  · rcases h_table with h_table | h_table
    · rcases h_table with ⟨rfl, rfl, rfl⟩
      have hb : (20 : ℝ) ≤ 25 := by norm_num
      have hrow : BKLNW_app.table_8_ε 25 ≤ 3.5032e-6 :=
        BKLNW_app.table_8_ε_le_of_row (b₀ := 25) (ε := 3.5032e-6) (BKLNW_app.table_8_mem_25) (by exact le_rfl)
      have h_epsM : (3.5032e-6 : ℝ) ≤ 3.5031e-6 * table_14_margin := by norm_num [table_14_margin]
      have h1 : exp (-25 / 2) ≤ 3.73e-6 := by
        have h1' : exp (-25 / 2) ≤ exp_neg_one_ub ^ ((25:ℝ) / 2) := by
          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_rpow' (x:=25/2) (by norm_num))
        have h1'' : exp_neg_one_ub ^ ((25:ℝ) / 2) ≤ 3.73e-6 := by
          refine rpow_le_of_pow_le (by positivity) (by norm_num) (p:=25) (q:=2) (by norm_num) ?_
          norm_num [exp_neg_one_ub]
        exact h1'.trans h1''
      have h2 : exp (-2 * 25 / 3) ≤ 5.78e-8 := by
        have h2' : exp (-2 * 25 / 3) ≤ exp_neg_one_ub ^ ((50:ℝ) / 3) := by
          have hx : (2:ℝ) * 25 / 3 = (50:ℝ) / 3 := by ring
          simpa [hx, neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
            (exp_neg_le_rpow' (x:=2*25/3) (by norm_num))
        have h2'' : exp_neg_one_ub ^ ((50:ℝ) / 3) ≤ 5.78e-8 := by
          have ha : 0 ≤ exp_neg_one_ub := by norm_num [exp_neg_one_ub]
          have hc : 0 ≤ (5.78e-8 : ℝ) := by norm_num
          refine rpow_le_of_pow_le (a:=exp_neg_one_ub) (c:=5.78e-8) ha hc (p:=50) (q:=3)
            (by norm_num) ?_
          norm_num [exp_neg_one_ub]
        exact h2'.trans h2''
      have h3 : exp (-4 * 25 / 5) ≤ exp_neg_one_ub ^ 20 := by
        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=20) (x:=4*25/5) (by norm_num))
      have hbound : (3.5032e-6 : ℝ) + RS_prime.c₀ * (3.73e-6 + 5.78e-8 + exp_neg_one_ub ^ 20) ≤ 7.4366e-6 * table_14_margin := by
        norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
      exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
    · rcases h_table with h_table | h_table
      · rcases h_table with ⟨rfl, rfl, rfl⟩
        have hb : (20 : ℝ) ≤ 30 := by norm_num
        have hrow : BKLNW_app.table_8_ε 30 ≤ 2.8756e-7 :=
          BKLNW_app.table_8_ε_le_of_row (b₀ := 30) (ε := 2.8756e-7) (BKLNW_app.table_8_mem_30) (by exact le_rfl)
        have h_epsM : (2.8756e-7 : ℝ) ≤ 2.8755e-7 * table_14_margin := by norm_num [table_14_margin]
        have h1 : exp (-30 / 2) ≤ exp_neg_one_ub ^ 15 := by
          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=15) (x:=30/2) (by norm_num))
        have h2 : exp (-2 * 30 / 3) ≤ exp_neg_one_ub ^ 20 := by
          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=20) (x:=2*30/3) (by norm_num))
        have h3 : exp (-4 * 30 / 5) ≤ exp_neg_one_ub ^ 24 := by
          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=24) (x:=4*30/5) (by norm_num))
        have hbound : (2.8756e-7 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 15 + exp_neg_one_ub ^ 20 + exp_neg_one_ub ^ 24) ≤ 6.0751e-7 * table_14_margin := by
          norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
        exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
      · rcases h_table with h_table | h_table
        · rcases h_table with ⟨rfl, rfl, rfl⟩
          have hb : (20 : ℝ) ≤ 35 := by norm_num
          have hrow : BKLNW_app.table_8_ε 35 ≤ 2.3604e-8 :=
            BKLNW_app.table_8_ε_le_of_row (b₀ := 35) (ε := 2.3604e-8) (BKLNW_app.table_8_mem_35) (by exact le_rfl)
          have h_epsM : (2.3604e-8 : ℝ) ≤ 2.3603e-8 * table_14_margin := by norm_num [table_14_margin]
          have h1 : exp (-35 / 2) ≤ 2.52e-8 := by
            have h1' : exp (-35 / 2) ≤ exp_neg_one_ub ^ ((35:ℝ) / 2) := by
              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_rpow' (x:=35/2) (by norm_num))
            have h1'' : exp_neg_one_ub ^ ((35:ℝ) / 2) ≤ 2.52e-8 := by
              refine rpow_le_of_pow_le (by positivity) (by norm_num) (p:=35) (q:=2) (by norm_num) ?_
              norm_num [exp_neg_one_ub]
            exact h1'.trans h1''
          have h2 : exp (-2 * 35 / 3) ≤ 7.36e-11 := by
            have h2' : exp (-2 * 35 / 3) ≤ exp_neg_one_ub ^ ((70:ℝ) / 3) := by
              have hx : (2:ℝ) * 35 / 3 = (70:ℝ) / 3 := by ring
              simpa [hx, neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
                (exp_neg_le_rpow' (x:=2*35/3) (by norm_num))
            have h2'' : exp_neg_one_ub ^ ((70:ℝ) / 3) ≤ 7.36e-11 := by
              have ha : 0 ≤ exp_neg_one_ub := by norm_num [exp_neg_one_ub]
              have hc : 0 ≤ (7.36e-11 : ℝ) := by norm_num
              refine rpow_le_of_pow_le (a:=exp_neg_one_ub) (c:=7.36e-11) ha hc (p:=70) (q:=3)
                (by norm_num) ?_
              norm_num [exp_neg_one_ub]
            exact h2'.trans h2''
          have h3 : exp (-4 * 35 / 5) ≤ exp_neg_one_ub ^ 28 := by
            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=28) (x:=4*35/5) (by norm_num))
          have hbound : (2.3604e-8 : ℝ) + RS_prime.c₀ * (2.52e-8 + 7.36e-11 + exp_neg_one_ub ^ 28) ≤ 4.9766e-8 * table_14_margin := by
            norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
          exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
        · rcases h_table with h_table | h_table
          · rcases h_table with ⟨rfl, rfl, rfl⟩
            have hb : (20 : ℝ) ≤ 40 := by norm_num
            have hrow : BKLNW_app.table_8_ε 40 ≤ 1.9339e-8 :=
              BKLNW_app.table_8_ε_le_of_row (b₀ := 40) (ε := 1.9339e-8) (BKLNW_app.table_8_mem_40) (by exact le_rfl)
            have h_epsM : (1.9339e-8 : ℝ) ≤ 1.9338e-8 * table_14_margin := by norm_num [table_14_margin]
            have h1 : exp (-40 / 2) ≤ exp_neg_one_ub ^ 20 := by
              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=20) (x:=40/2) (by norm_num))
            have h2 : exp (-2 * 40 / 3) ≤ exp_neg_one_ub ^ 26 := by
              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=26) (x:=2*40/3) (by norm_num))
            have h3 : exp (-4 * 40 / 5) ≤ exp_neg_one_ub ^ 32 := by
              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=32) (x:=4*40/5) (by norm_num))
            have hbound : (1.9339e-8 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 20 + exp_neg_one_ub ^ 26 + exp_neg_one_ub ^ 32) ≤ 2.1482e-8 * table_14_margin := by
              norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
            exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
          · rcases h_table with h_table | h_table
            · rcases h_table with ⟨rfl, rfl, rfl⟩
              have h_log_approx : 43 < 19 * log 10 ∧ 19 * log 10 < 44 :=
                ⟨by nlinarith [LogTables.log_10_gt], by nlinarith [LogTables.log_10_lt]⟩
              have hb : (20 : ℝ) ≤ 19 * log 10 := by linarith [h_log_approx.1]
              have hrow : BKLNW_app.table_8_ε (19 * log 10) ≤ 1.9339e-8 :=
                BKLNW_app.table_8_ε_le_of_row (b₀ := 40) (ε := 1.9339e-8)
                  (BKLNW_app.table_8_mem_40) (by linarith [h_log_approx.1])
              have h_epsM : (1.9339e-8 : ℝ) ≤ 1.9338e-8 * table_14_margin := by norm_num [table_14_margin]
              have h1 : exp (-(19 * log 10) / 2) ≤ 3.17e-10 := by
                have h1' : exp (-(19 * log 10) / 2) = (1/10 : ℝ) ^ ((19:ℝ) / 2) := by
                  have hmul : -(19 * log 10) / 2 = (log 10) * (-(19 : ℝ) / 2) := by ring
                  calc
                    exp (-(19 * log 10) / 2) = exp (log 10 * (-(19 : ℝ) / 2)) := by
                      simp [hmul]
                    _ = exp (log 10) ^ (-(19 : ℝ) / 2) := by
                      simpa using (Real.exp_mul (log 10) (-(19 : ℝ) / 2))
                    _ = exp (log 10) ^ (-( (19:ℝ) / 2)) := by
                      simp [neg_div]
                    _ = (10 : ℝ) ^ (-( (19:ℝ) / 2)) := by
                      have h10 : (0 : ℝ) < 10 := by norm_num
                      simp [Real.exp_log h10]
                    _ = (1/10 : ℝ) ^ ((19:ℝ) / 2) := by
                      simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((19:ℝ) / 2))
                have h1'' : (1/10 : ℝ) ^ ((19:ℝ) / 2) ≤ 3.17e-10 := by
                  have ha : 0 ≤ (1/10 : ℝ) := by norm_num
                  have hc : 0 ≤ (3.17e-10 : ℝ) := by norm_num
                  refine rpow_le_of_pow_le (a:=1/10) (c:=3.17e-10) ha hc (p:=19) (q:=2)
                    (by norm_num) ?_
                  norm_num
                simpa [h1'] using h1''
              have h2 : exp (-2 * (19 * log 10) / 3) ≤ 2.16e-13 := by
                have h2' : exp (-2 * (19 * log 10) / 3) = (1/10 : ℝ) ^ ((38:ℝ) / 3) := by
                  have hmul : -(2 * (19 * log 10)) / 3 = (log 10) * (-(38 : ℝ) / 3) := by ring
                  calc
                    exp (-2 * (19 * log 10) / 3) = exp (-(2 * (19 * log 10)) / 3) := by
                      ring_nf
                    _ = exp (log 10 * (-(38 : ℝ) / 3)) := by
                      simp [hmul]
                    _ = exp (log 10) ^ (-(38 : ℝ) / 3) := by
                      simpa using (Real.exp_mul (log 10) (-(38 : ℝ) / 3))
                    _ = exp (log 10) ^ (-( (38:ℝ) / 3)) := by
                      simp [neg_div]
                    _ = (10 : ℝ) ^ (-( (38:ℝ) / 3)) := by
                      have h10 : (0 : ℝ) < 10 := by norm_num
                      simp [Real.exp_log h10]
                    _ = (1/10 : ℝ) ^ ((38:ℝ) / 3) := by
                      simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((38:ℝ) / 3))
                have h2'' : (1/10 : ℝ) ^ ((38:ℝ) / 3) ≤ 2.16e-13 := by
                  have ha : 0 ≤ (1/10 : ℝ) := by norm_num
                  have hc : 0 ≤ (2.16e-13 : ℝ) := by norm_num
                  refine rpow_le_of_pow_le (a:=1/10) (c:=2.16e-13) ha hc (p:=38) (q:=3)
                    (by norm_num) ?_
                  norm_num
                calc
                  exp (-2 * (19 * log 10) / 3) = (1/10 : ℝ) ^ ((38:ℝ) / 3) := h2'
                  _ ≤ 2.16e-13 := h2''
              have h3 : exp (-4 * (19 * log 10) / 5) ≤ 6.32e-16 := by
                have h3' : exp (-4 * (19 * log 10) / 5) = (1/10 : ℝ) ^ ((76:ℝ) / 5) := by
                  have hmul : -(4 * (19 * log 10)) / 5 = (log 10) * (-(76 : ℝ) / 5) := by ring
                  calc
                    exp (-4 * (19 * log 10) / 5) = exp (-(4 * (19 * log 10)) / 5) := by
                      ring_nf
                    _ = exp (log 10 * (-(76 : ℝ) / 5)) := by
                      simp [hmul]
                    _ = exp (log 10) ^ (-(76 : ℝ) / 5) := by
                      simpa using (Real.exp_mul (log 10) (-(76 : ℝ) / 5))
                    _ = exp (log 10) ^ (-( (76:ℝ) / 5)) := by
                      simp [neg_div]
                    _ = (10 : ℝ) ^ (-( (76:ℝ) / 5)) := by
                      have h10 : (0 : ℝ) < 10 := by norm_num
                      simp [Real.exp_log h10]
                    _ = (1/10 : ℝ) ^ ((76:ℝ) / 5) := by
                      simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((76:ℝ) / 5))
                have h3'' : (1/10 : ℝ) ^ ((76:ℝ) / 5) ≤ 6.32e-16 := by
                  have ha : 0 ≤ (1/10 : ℝ) := by norm_num
                  have hc : 0 ≤ (6.32e-16 : ℝ) := by norm_num
                  refine rpow_le_of_pow_le (a:=1/10) (c:=6.32e-16) ha hc (p:=76) (q:=5)
                    (by norm_num) ?_
                  norm_num
                calc
                  exp (-4 * (19 * log 10) / 5) = (1/10 : ℝ) ^ ((76:ℝ) / 5) := h3'
                  _ ≤ 6.32e-16 := h3''
              have hbound : (1.9339e-8 : ℝ) + RS_prime.c₀ * (3.17e-10 + 2.16e-13 + 6.32e-16) ≤ 1.9667e-8 * table_14_margin := by
                norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
              exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
            · rcases h_table with h_table | h_table
              · rcases h_table with ⟨rfl, rfl, rfl⟩
                have hb : (20 : ℝ) ≤ 45 := by norm_num
                have hrow : BKLNW_app.table_8_ε 45 ≤ 1.0908e-8 :=
                  BKLNW_app.table_8_ε_le_of_row (b₀ := 45) (ε := 1.0908e-8) (BKLNW_app.table_8_mem_45) (by exact le_rfl)
                have h_epsM : (1.0908e-8 : ℝ) ≤ 1.0907e-8 * table_14_margin := by norm_num [table_14_margin]
                have h1 : exp (-45 / 2) ≤ 1.70e-10 := by
                  have h1' : exp (-45 / 2) ≤ exp_neg_one_ub ^ ((45:ℝ) / 2) := by
                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_rpow' (x:=45/2) (by norm_num))
                  have h1'' : exp_neg_one_ub ^ ((45:ℝ) / 2) ≤ 1.70e-10 := by
                    refine rpow_le_of_pow_le (by positivity) (by norm_num) (p:=45) (q:=2) (by norm_num) ?_
                    norm_num [exp_neg_one_ub]
                  exact h1'.trans h1''
                have h2 : exp (-2 * 45 / 3) ≤ exp_neg_one_ub ^ 30 := by
                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=30) (x:=2*45/3) (by norm_num))
                have h3 : exp (-4 * 45 / 5) ≤ exp_neg_one_ub ^ 36 := by
                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=36) (x:=4*45/5) (by norm_num))
                have hbound : (1.0908e-8 : ℝ) + RS_prime.c₀ * (1.70e-10 + exp_neg_one_ub ^ 30 + exp_neg_one_ub ^ 36) ≤ 1.1084e-8 * table_14_margin := by
                  norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
              · rcases h_table with h_table | h_table
                · rcases h_table with ⟨rfl, rfl, rfl⟩
                  have hb : (20 : ℝ) ≤ 50 := by norm_num
                  have hrow : BKLNW_app.table_8_ε 50 ≤ 1.1200e-9 :=
                    BKLNW_app.table_8_ε_le_of_row (b₀ := 50) (ε := 1.1200e-9) (BKLNW_app.table_8_mem_50) (by exact le_rfl)
                  have h_epsM : (1.1200e-9 : ℝ) ≤ 1.1199e-9 * table_14_margin := by norm_num [table_14_margin]
                  have h1 : exp (-50 / 2) ≤ exp_neg_one_ub ^ 25 := by
                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=25) (x:=50/2) (by norm_num))
                  have h2 : exp (-2 * 50 / 3) ≤ exp_neg_one_ub ^ 33 := by
                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=33) (x:=2*50/3) (by norm_num))
                  have h3 : exp (-4 * 50 / 5) ≤ exp_neg_one_ub ^ 40 := by
                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=40) (x:=4*50/5) (by norm_num))
                  have hbound : (1.1200e-9 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 25 + exp_neg_one_ub ^ 33 + exp_neg_one_ub ^ 40) ≤ 1.1344e-9 * table_14_margin := by
                    norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                  exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                · rcases h_table with h_table | h_table
                  · rcases h_table with ⟨rfl, rfl, rfl⟩
                    have hb : (20 : ℝ) ≤ 60 := by norm_num
                    have hrow : BKLNW_app.table_8_ε 60 ≤ 1.2216e-11 :=
                      BKLNW_app.table_8_ε_le_of_row (b₀ := 60) (ε := 1.2216e-11) (BKLNW_app.table_8_mem_60) (by exact le_rfl)
                    have h_epsM : (1.2216e-11 : ℝ) ≤ 1.2215e-11 * table_14_margin := by norm_num [table_14_margin]
                    have h1 : exp (-60 / 2) ≤ exp_neg_one_ub ^ 30 := by
                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=30) (x:=60/2) (by norm_num))
                    have h2 : exp (-2 * 60 / 3) ≤ exp_neg_one_ub ^ 40 := by
                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=40) (x:=2*60/3) (by norm_num))
                    have h3 : exp (-4 * 60 / 5) ≤ exp_neg_one_ub ^ 48 := by
                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=48) (x:=4*60/5) (by norm_num))
                    have hbound : (1.2216e-11 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 30 + exp_neg_one_ub ^ 40 + exp_neg_one_ub ^ 48) ≤ 1.2312e-11 * table_14_margin := by
                      norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                    exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                  · rcases h_table with h_table | h_table
                    · rcases h_table with ⟨rfl, rfl, rfl⟩
                      have hb : (20 : ℝ) ≤ 70 := by norm_num
                      have hrow : BKLNW_app.table_8_ε 70 ≤ 2.7924e-12 :=
                        BKLNW_app.table_8_ε_le_of_row (b₀ := 70) (ε := 2.7924e-12) (BKLNW_app.table_8_mem_70) (by exact le_rfl)
                      have h_epsM : (2.7924e-12 : ℝ) ≤ 2.7923e-12 * table_14_margin := by norm_num [table_14_margin]
                      have h1 : exp (-70 / 2) ≤ exp_neg_one_ub ^ 35 := by
                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=35) (x:=70/2) (by norm_num))
                      have h2 : exp (-2 * 70 / 3) ≤ exp_neg_one_ub ^ 46 := by
                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=46) (x:=2*70/3) (by norm_num))
                      have h3 : exp (-4 * 70 / 5) ≤ exp_neg_one_ub ^ 56 := by
                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=56) (x:=4*70/5) (by norm_num))
                      have hbound : (2.7924e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 35 + exp_neg_one_ub ^ 46 + exp_neg_one_ub ^ 56) ≤ 2.7930e-12 * table_14_margin := by
                        norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                      exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                    · rcases h_table with h_table | h_table
                      · rcases h_table with ⟨rfl, rfl, rfl⟩
                        have hb : (20 : ℝ) ≤ 80 := by norm_num
                        have hrow : BKLNW_app.table_8_ε 80 ≤ 2.6109e-12 :=
                          BKLNW_app.table_8_ε_le_of_row (b₀ := 80) (ε := 2.6109e-12) (BKLNW_app.table_8_mem_80) (by exact le_rfl)
                        have h_epsM : (2.6109e-12 : ℝ) ≤ 2.6108e-12 * table_14_margin := by norm_num [table_14_margin]
                        have h1 : exp (-80 / 2) ≤ exp_neg_one_ub ^ 40 := by
                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=40) (x:=80/2) (by norm_num))
                        have h2 : exp (-2 * 80 / 3) ≤ exp_neg_one_ub ^ 53 := by
                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=53) (x:=2*80/3) (by norm_num))
                        have h3 : exp (-4 * 80 / 5) ≤ exp_neg_one_ub ^ 64 := by
                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=64) (x:=4*80/5) (by norm_num))
                        have hbound : (2.6109e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 40 + exp_neg_one_ub ^ 53 + exp_neg_one_ub ^ 64) ≤ 2.6108e-12 * table_14_margin := by
                          norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                        exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                      · rcases h_table with h_table | h_table
                        · rcases h_table with ⟨rfl, rfl, rfl⟩
                          have hb : (20 : ℝ) ≤ 90 := by norm_num
                          have hrow : BKLNW_app.table_8_ε 90 ≤ 2.5214e-12 :=
                            BKLNW_app.table_8_ε_le_of_row (b₀ := 90) (ε := 2.5214e-12) (BKLNW_app.table_8_mem_90) (by exact le_rfl)
                          have h_epsM : (2.5214e-12 : ℝ) ≤ 2.5213e-12 * table_14_margin := by norm_num [table_14_margin]
                          have h1 : exp (-90 / 2) ≤ exp_neg_one_ub ^ 45 := by
                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=45) (x:=90/2) (by norm_num))
                          have h2 : exp (-2 * 90 / 3) ≤ exp_neg_one_ub ^ 60 := by
                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=60) (x:=2*90/3) (by norm_num))
                          have h3 : exp (-4 * 90 / 5) ≤ exp_neg_one_ub ^ 72 := by
                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=72) (x:=4*90/5) (by norm_num))
                          have hbound : (2.5214e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 45 + exp_neg_one_ub ^ 60 + exp_neg_one_ub ^ 72) ≤ 2.5213e-12 * table_14_margin := by
                            norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                          exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                        · rcases h_table with h_table | h_table
                          · rcases h_table with ⟨rfl, rfl, rfl⟩
                            have hb : (20 : ℝ) ≤ 100 := by norm_num
                            have hrow : BKLNW_app.table_8_ε 100 ≤ 2.4531e-12 :=
                              BKLNW_app.table_8_ε_le_of_row (b₀ := 100) (ε := 2.4531e-12) (BKLNW_app.table_8_mem_100) (by exact le_rfl)
                            have h_epsM : (2.4531e-12 : ℝ) ≤ 2.4530e-12 * table_14_margin := by norm_num [table_14_margin]
                            have h1 : exp (-100 / 2) ≤ exp_neg_one_ub ^ 50 := by
                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=50) (x:=100/2) (by norm_num))
                            have h2 : exp (-2 * 100 / 3) ≤ exp_neg_one_ub ^ 66 := by
                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=66) (x:=2*100/3) (by norm_num))
                            have h3 : exp (-4 * 100 / 5) ≤ exp_neg_one_ub ^ 80 := by
                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=80) (x:=4*100/5) (by norm_num))
                            have hbound : (2.4531e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 50 + exp_neg_one_ub ^ 66 + exp_neg_one_ub ^ 80) ≤ 2.4530e-12 * table_14_margin := by
                              norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                            exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                          · rcases h_table with h_table | h_table
                            · rcases h_table with ⟨rfl, rfl, rfl⟩
                              have hb : (20 : ℝ) ≤ 200 := by norm_num
                              have hrow : BKLNW_app.table_8_ε 200 ≤ 2.1816e-12 :=
                                BKLNW_app.table_8_ε_le_of_row (b₀ := 200) (ε := 2.1816e-12) (BKLNW_app.table_8_mem_200) (by exact le_rfl)
                              have h_epsM : (2.1816e-12 : ℝ) ≤ 2.1815e-12 * table_14_margin := by norm_num [table_14_margin]
                              have h1 : exp (-200 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=200/2) (by norm_num))
                              have h2 : exp (-2 * 200 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*200/3) (by norm_num))
                              have h3 : exp (-4 * 200 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*200/5) (by norm_num))
                              have hbound : (2.1816e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 2.1816e-12 * table_14_margin := by
                                norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                              exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                            · rcases h_table with h_table | h_table
                              · rcases h_table with ⟨rfl, rfl, rfl⟩
                                have hb : (20 : ℝ) ≤ 300 := by norm_num
                                have hrow : BKLNW_app.table_8_ε 300 ≤ 2.0903e-12 :=
                                  BKLNW_app.table_8_ε_le_of_row (b₀ := 300) (ε := 2.0903e-12) (BKLNW_app.table_8_mem_300) (by exact le_rfl)
                                have h_epsM : (2.0903e-12 : ℝ) ≤ 2.0902e-12 * table_14_margin := by norm_num [table_14_margin]
                                have h1 : exp (-300 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=300/2) (by norm_num))
                                have h2 : exp (-2 * 300 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*300/3) (by norm_num))
                                have h3 : exp (-4 * 300 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*300/5) (by norm_num))
                                have hbound : (2.0903e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 2.0903e-12 * table_14_margin := by
                                  norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                              · rcases h_table with h_table | h_table
                                · rcases h_table with ⟨rfl, rfl, rfl⟩
                                  have hb : (20 : ℝ) ≤ 400 := by norm_num
                                  have hrow : BKLNW_app.table_8_ε 400 ≤ 2.0399e-12 :=
                                    BKLNW_app.table_8_ε_le_of_row (b₀ := 400) (ε := 2.0399e-12) (BKLNW_app.table_8_mem_400) (by exact le_rfl)
                                  have h_epsM : (2.0399e-12 : ℝ) ≤ 2.0398e-12 * table_14_margin := by norm_num [table_14_margin]
                                  have h1 : exp (-400 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=400/2) (by norm_num))
                                  have h2 : exp (-2 * 400 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*400/3) (by norm_num))
                                  have h3 : exp (-4 * 400 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*400/5) (by norm_num))
                                  have hbound : (2.0399e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 2.0399e-12 * table_14_margin := by
                                    norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                  exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                · rcases h_table with h_table | h_table
                                  · rcases h_table with ⟨rfl, rfl, rfl⟩
                                    have hb : (20 : ℝ) ≤ 500 := by norm_num
                                    have hrow : BKLNW_app.table_8_ε 500 ≤ 1.9999e-12 :=
                                      BKLNW_app.table_8_ε_le_of_row (b₀ := 500) (ε := 1.9999e-12) (BKLNW_app.table_8_mem_500) (by exact le_rfl)
                                    have h_epsM : (1.9999e-12 : ℝ) ≤ 1.9999e-12 * table_14_margin := by norm_num [table_14_margin]
                                    have h1 : exp (-500 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=500/2) (by norm_num))
                                    have h2 : exp (-2 * 500 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*500/3) (by norm_num))
                                    have h3 : exp (-4 * 500 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*500/5) (by norm_num))
                                    have hbound : (1.9999e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 1.9999e-12 * table_14_margin := by
                                      norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                    exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                  · rcases h_table with h_table | h_table
                                    · rcases h_table with ⟨rfl, rfl, rfl⟩
                                      have hb : (20 : ℝ) ≤ 700 := by norm_num
                                      have hrow : BKLNW_app.table_8_ε 700 ≤ 1.9765e-12 :=
                                        BKLNW_app.table_8_ε_le_of_row (b₀ := 700) (ε := 1.9765e-12) (BKLNW_app.table_8_mem_700) (by exact le_rfl)
                                      have h_epsM : (1.9765e-12 : ℝ) ≤ 1.9764e-12 * table_14_margin := by norm_num [table_14_margin]
                                      have h1 : exp (-700 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=700/2) (by norm_num))
                                      have h2 : exp (-2 * 700 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*700/3) (by norm_num))
                                      have h3 : exp (-4 * 700 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*700/5) (by norm_num))
                                      have hbound : (1.9765e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 1.9765e-12 * table_14_margin := by
                                        norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                      exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                    · rcases h_table with h_table | h_table
                                      · rcases h_table with ⟨rfl, rfl, rfl⟩
                                        have hb : (20 : ℝ) ≤ 1000 := by norm_num
                                        have hrow : BKLNW_app.table_8_ε 1000 ≤ 1.9476e-12 :=
                                          BKLNW_app.table_8_ε_le_of_row (b₀ := 1000) (ε := 1.9476e-12) (BKLNW_app.table_8_mem_1000) (by exact le_rfl)
                                        have h_epsM : (1.9476e-12 : ℝ) ≤ 1.9475e-12 * table_14_margin := by norm_num [table_14_margin]
                                        have h1 : exp (-1000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=1000/2) (by norm_num))
                                        have h2 : exp (-2 * 1000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*1000/3) (by norm_num))
                                        have h3 : exp (-4 * 1000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*1000/5) (by norm_num))
                                        have hbound : (1.9476e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 1.9476e-12 * table_14_margin := by
                                          norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                        exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                      · rcases h_table with h_table | h_table
                                        · rcases h_table with ⟨rfl, rfl, rfl⟩
                                          have hb : (20 : ℝ) ≤ 2000 := by norm_num
                                          have hrow : BKLNW_app.table_8_ε 2000 ≤ 1.9229e-12 :=
                                            BKLNW_app.table_8_ε_le_of_row (b₀ := 2000) (ε := 1.9229e-12) (BKLNW_app.table_8_mem_2000) (by exact le_rfl)
                                          have h_epsM : (1.9229e-12 : ℝ) ≤ 1.9228e-12 * table_14_margin := by norm_num [table_14_margin]
                                          have h1 : exp (-2000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2000/2) (by norm_num))
                                          have h2 : exp (-2 * 2000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*2000/3) (by norm_num))
                                          have h3 : exp (-4 * 2000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*2000/5) (by norm_num))
                                          have hbound : (1.9229e-12 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 1.9228e-12 * table_14_margin := by
                                            norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                          exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                        · rcases h_table with h_table | h_table
                                          · rcases h_table with ⟨rfl, rfl, rfl⟩
                                            have hb : (20 : ℝ) ≤ 3000 := by norm_num
                                            have hrow : BKLNW_app.table_8_ε 3000 ≤ 4.5998e-14 :=
                                              BKLNW_app.table_8_ε_le_of_row (b₀ := 3000) (ε := 4.5998e-14) (BKLNW_app.table_8_mem_3000) (by exact le_rfl)
                                            have h_epsM : (4.5998e-14 : ℝ) ≤ 4.5997e-14 * table_14_margin := by norm_num [table_14_margin]
                                            have h1 : exp (-3000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=3000/2) (by norm_num))
                                            have h2 : exp (-2 * 3000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*3000/3) (by norm_num))
                                            have h3 : exp (-4 * 3000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*3000/5) (by norm_num))
                                            have hbound : (4.5998e-14 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 4.5998e-14 * table_14_margin := by
                                              norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                            exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                          · rcases h_table with h_table | h_table
                                            · rcases h_table with ⟨rfl, rfl, rfl⟩
                                              have hb : (20 : ℝ) ≤ 4000 := by norm_num
                                              have hrow : BKLNW_app.table_8_ε 4000 ≤ 1.4264e-16 :=
                                                BKLNW_app.table_8_ε_le_of_row (b₀ := 4000) (ε := 1.4264e-16) (BKLNW_app.table_8_mem_4000) (by exact le_rfl)
                                              have h_epsM : (1.4264e-16 : ℝ) ≤ 1.4263e-16 * table_14_margin := by norm_num [table_14_margin]
                                              have h1 : exp (-4000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4000/2) (by norm_num))
                                              have h2 : exp (-2 * 4000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*4000/3) (by norm_num))
                                              have h3 : exp (-4 * 4000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*4000/5) (by norm_num))
                                              have hbound : (1.4264e-16 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 1.4264e-16 * table_14_margin := by
                                                norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                              exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                            · rcases h_table with h_table | h_table
                                              · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                have hb : (20 : ℝ) ≤ 5000 := by norm_num
                                                have hrow : BKLNW_app.table_8_ε 5000 ≤ 5.6304e-19 :=
                                                  BKLNW_app.table_8_ε_le_of_row (b₀ := 5000) (ε := 5.6304e-19) (BKLNW_app.table_8_mem_5000) (by exact le_rfl)
                                                have h_epsM : (5.6304e-19 : ℝ) ≤ 5.6303e-19 * table_14_margin := by norm_num [table_14_margin]
                                                have h1 : exp (-5000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=5000/2) (by norm_num))
                                                have h2 : exp (-2 * 5000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*5000/3) (by norm_num))
                                                have h3 : exp (-4 * 5000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*5000/5) (by norm_num))
                                                have hbound : (5.6304e-19 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 5.6303e-19 * table_14_margin := by
                                                  norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                              · rcases h_table with h_table | h_table
                                                · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                  have hb : (20 : ℝ) ≤ 7000 := by norm_num
                                                  have hrow : BKLNW_app.table_8_ε 7000 ≤ 2.0766e-23 :=
                                                    BKLNW_app.table_8_ε_le_of_row (b₀ := 7000) (ε := 2.0766e-23) (BKLNW_app.table_8_mem_7000) (by exact le_rfl)
                                                  have h_epsM : (2.0766e-23 : ℝ) ≤ 2.0765e-23 * table_14_margin := by norm_num [table_14_margin]
                                                  have h1 : exp (-7000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=7000/2) (by norm_num))
                                                  have h2 : exp (-2 * 7000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*7000/3) (by norm_num))
                                                  have h3 : exp (-4 * 7000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*7000/5) (by norm_num))
                                                  have hbound : (2.0766e-23 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 2.0766e-23 * table_14_margin := by
                                                    norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                  exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                · rcases h_table with h_table | h_table
                                                  · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                    have hb : (20 : ℝ) ≤ 10000 := by norm_num
                                                    have hrow : BKLNW_app.table_8_ε 10000 ≤ 3.7850e-29 :=
                                                      BKLNW_app.table_8_ε_le_of_row (b₀ := 10000) (ε := 3.7850e-29) (BKLNW_app.table_8_mem_10000) (by exact le_rfl)
                                                    have h_epsM : (3.7850e-29 : ℝ) ≤ 3.7849e-29 * table_14_margin := by norm_num [table_14_margin]
                                                    have h1 : exp (-10000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=10000/2) (by norm_num))
                                                    have h2 : exp (-2 * 10000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*10000/3) (by norm_num))
                                                    have h3 : exp (-4 * 10000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*10000/5) (by norm_num))
                                                    have hbound : (3.7850e-29 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 3.7850e-29 * table_14_margin := by
                                                      norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                    exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                  · rcases h_table with h_table | h_table
                                                    · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                      have hb : (20 : ℝ) ≤ 11000 := by norm_num
                                                      have hrow : BKLNW_app.table_8_ε 11000 ≤ 7.1427e-31 :=
                                                        BKLNW_app.table_8_ε_le_of_row (b₀ := 11000) (ε := 7.1427e-31) (BKLNW_app.table_8_mem_11000) (by exact le_rfl)
                                                      have h_epsM : (7.1427e-31 : ℝ) ≤ 7.1426e-31 * table_14_margin := by norm_num [table_14_margin]
                                                      have h1 : exp (-11000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=11000/2) (by norm_num))
                                                      have h2 : exp (-2 * 11000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*11000/3) (by norm_num))
                                                      have h3 : exp (-4 * 11000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                        simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*11000/5) (by norm_num))
                                                      have hbound : (7.1427e-31 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 7.1427e-31 * table_14_margin := by
                                                        norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                      exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                    · rcases h_table with h_table | h_table
                                                      · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                        have hb : (20 : ℝ) ≤ 12000 := by norm_num
                                                        have hrow : BKLNW_app.table_8_ε 12000 ≤ 1.5976e-32 :=
                                                          BKLNW_app.table_8_ε_le_of_row (b₀ := 12000) (ε := 1.5976e-32) (BKLNW_app.table_8_mem_12000) (by exact le_rfl)
                                                        have h_epsM : (1.5976e-32 : ℝ) ≤ 1.5975e-32 * table_14_margin := by norm_num [table_14_margin]
                                                        have h1 : exp (-12000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=12000/2) (by norm_num))
                                                        have h2 : exp (-2 * 12000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*12000/3) (by norm_num))
                                                        have h3 : exp (-4 * 12000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                          simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*12000/5) (by norm_num))
                                                        have hbound : (1.5976e-32 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 1.5976e-32 * table_14_margin := by
                                                          norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                        exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                      · rcases h_table with h_table | h_table
                                                        · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                          have hb : (20 : ℝ) ≤ 13000 := by norm_num
                                                          have hrow : BKLNW_app.table_8_ε 13000 ≤ 4.1356e-34 :=
                                                            BKLNW_app.table_8_ε_le_of_row (b₀ := 13000) (ε := 4.1356e-34) (BKLNW_app.table_8_mem_13000) (by exact le_rfl)
                                                          have h_epsM : (4.1356e-34 : ℝ) ≤ 4.1355e-34 * table_14_margin := by norm_num [table_14_margin]
                                                          have h1 : exp (-13000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=13000/2) (by norm_num))
                                                          have h2 : exp (-2 * 13000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*13000/3) (by norm_num))
                                                          have h3 : exp (-4 * 13000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                            simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*13000/5) (by norm_num))
                                                          have hbound : (4.1356e-34 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 4.1356e-34 * table_14_margin := by
                                                            norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                          exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                        · rcases h_table with h_table | h_table
                                                          · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                            have hb : (20 : ℝ) ≤ 13800.7464 := by norm_num
                                                            have hrow : BKLNW_app.table_8_ε 13800.7464 ≤ 2.5423e-35 :=
                                                              BKLNW_app.table_8_ε_le_of_row (b₀ := 13800) (ε := 2.5423e-35)
                                                                (BKLNW_app.table_8_mem_13800) (by norm_num)
                                                            have h_epsM : (2.5423e-35 : ℝ) ≤ 2.5423e-35 * table_14_margin := by norm_num [table_14_margin]
                                                            have h1 : exp (-13800.7464 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=13800.7464/2) (by norm_num))
                                                            have h2 : exp (-2 * 13800.7464 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*13800.7464/3) (by norm_num))
                                                            have h3 : exp (-4 * 13800.7464 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                              simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*13800.7464/5) (by norm_num))
                                                            have hbound : (2.5423e-35 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 2.5424e-35 * table_14_margin := by
                                                              norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                            exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                          · rcases h_table with h_table | h_table
                                                            · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                              have hb : (20 : ℝ) ≤ 15000 := by norm_num
                                                              have hrow : BKLNW_app.table_8_ε 15000 ≤ 4.1071e-37 :=
                                                                BKLNW_app.table_8_ε_le_of_row (b₀ := 15000) (ε := 4.1071e-37) (BKLNW_app.table_8_mem_15000) (by exact le_rfl)
                                                              have h_epsM : (4.1071e-37 : ℝ) ≤ 4.1070e-37 * table_14_margin := by norm_num [table_14_margin]
                                                              have h1 : exp (-15000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=15000/2) (by norm_num))
                                                              have h2 : exp (-2 * 15000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*15000/3) (by norm_num))
                                                              have h3 : exp (-4 * 15000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                                simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*15000/5) (by norm_num))
                                                              have hbound : (4.1071e-37 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 4.1070e-37 * table_14_margin := by
                                                                norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                              exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                            · rcases h_table with h_table | h_table
                                                              · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                                have hb : (20 : ℝ) ≤ 17000 := by norm_num
                                                                have hrow : BKLNW_app.table_8_ε 17000 ≤ 6.2041e-40 :=
                                                                  BKLNW_app.table_8_ε_le_of_row (b₀ := 17000) (ε := 6.2041e-40) (BKLNW_app.table_8_mem_17000) (by exact le_rfl)
                                                                have h_epsM : (6.2041e-40 : ℝ) ≤ 6.2040e-40 * table_14_margin := by norm_num [table_14_margin]
                                                                have h1 : exp (-17000 / 2) ≤ exp_neg_one_ub ^ 100 := by
                                                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=17000/2) (by norm_num))
                                                                have h2 : exp (-2 * 17000 / 3) ≤ exp_neg_one_ub ^ 100 := by
                                                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=2*17000/3) (by norm_num))
                                                                have h3 : exp (-4 * 17000 / 5) ≤ exp_neg_one_ub ^ 100 := by
                                                                  simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=100) (x:=4*17000/5) (by norm_num))
                                                                have hbound : (6.2041e-40 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100 + exp_neg_one_ub ^ 100) ≤ 6.2040e-40 * table_14_margin := by
                                                                  norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                                exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                              · rcases h_table with h_table | h_table
                                                                · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                                  have hb : (20 : ℝ) ≤ 20000 := by norm_num
                                                                  have hrow : BKLNW_app.table_8_ε 20000 ≤ 7.1622e-44 :=
                                                                    BKLNW_app.table_8_ε_le_of_row (b₀ := 20000) (ε := 7.1622e-44) (BKLNW_app.table_8_mem_20000) (by exact le_rfl)
                                                                  have h_epsM : (7.1622e-44 : ℝ) ≤ 7.1621e-44 * table_14_margin := by norm_num [table_14_margin]
                                                                  have h1 : exp (-20000 / 2) ≤ exp_neg_one_ub ^ 125 := by
                                                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=20000/2) (by norm_num))
                                                                  have h2 : exp (-2 * 20000 / 3) ≤ exp_neg_one_ub ^ 125 := by
                                                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=2*20000/3) (by norm_num))
                                                                  have h3 : exp (-4 * 20000 / 5) ≤ exp_neg_one_ub ^ 125 := by
                                                                    simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=4*20000/5) (by norm_num))
                                                                  have hbound : (7.1622e-44 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 125 + exp_neg_one_ub ^ 125 + exp_neg_one_ub ^ 125) ≤ 7.1621e-44 * table_14_margin := by
                                                                    norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                                  exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                                · rcases h_table with h_table | h_table
                                                                  · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                                    have hb : (20 : ℝ) ≤ 22000 := by norm_num
                                                                    have hrow : BKLNW_app.table_8_ε 22000 ≤ 2.4393e-46 :=
                                                                      BKLNW_app.table_8_ε_le_of_row (b₀ := 22000) (ε := 2.4393e-46) (BKLNW_app.table_8_mem_22000) (by exact le_rfl)
                                                                    have h_epsM : (2.4393e-46 : ℝ) ≤ 2.4392e-46 * table_14_margin := by norm_num [table_14_margin]
                                                                    have h1 : exp (-22000 / 2) ≤ exp_neg_one_ub ^ 125 := by
                                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=22000/2) (by norm_num))
                                                                    have h2 : exp (-2 * 22000 / 3) ≤ exp_neg_one_ub ^ 125 := by
                                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=2*22000/3) (by norm_num))
                                                                    have h3 : exp (-4 * 22000 / 5) ≤ exp_neg_one_ub ^ 125 := by
                                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=4*22000/5) (by norm_num))
                                                                    have hbound : (2.4393e-46 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 125 + exp_neg_one_ub ^ 125 + exp_neg_one_ub ^ 125) ≤ 2.4392e-46 * table_14_margin := by
                                                                      norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                                    exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound
                                                                  · rcases h_table with ⟨rfl, rfl, rfl⟩
                                                                    have hb : (20 : ℝ) ≤ 25000 := by norm_num
                                                                    have hrow : BKLNW_app.table_8_ε 25000 ≤ 7.5725e-50 :=
                                                                      BKLNW_app.table_8_ε_le_of_row (b₀ := 25000) (ε := 7.5725e-50) (BKLNW_app.table_8_mem_25000) (by exact le_rfl)
                                                                    have h_epsM : (7.5725e-50 : ℝ) ≤ 7.5724e-50 * table_14_margin := by norm_num [table_14_margin]
                                                                    have h1 : exp (-25000 / 2) ≤ exp_neg_one_ub ^ 125 := by
                                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=25000/2) (by norm_num))
                                                                    have h2 : exp (-2 * 25000 / 3) ≤ exp_neg_one_ub ^ 125 := by
                                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=2*25000/3) (by norm_num))
                                                                    have h3 : exp (-4 * 25000 / 5) ≤ exp_neg_one_ub ^ 125 := by
                                                                      simpa [neg_div, neg_mul, mul_assoc, mul_left_comm, mul_comm] using (exp_neg_le_pow' (n:=125) (x:=4*25000/5) (by norm_num))
                                                                    have hbound : (7.5725e-50 : ℝ) + RS_prime.c₀ * (exp_neg_one_ub ^ 125 + exp_neg_one_ub ^ 125 + exp_neg_one_ub ^ 125) ≤ 7.5724e-50 * table_14_margin := by
                                                                      norm_num [table_14_margin, RS_prime.c₀, exp_neg_one_ub]
                                                                    exact check_row_prop_of_bounds hb hrow h_epsM h1 h2 h3 hbound


noncomputable def table_10 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  [
    (20, 1.8077e-3, 3.6154e-2, 7.2309e-1, 1.4462e1, 2.9160e2),
    (21, 1.1458e-3, 2.4062e-2, 5.0530e-1, 1.0611e1, 2.2284e2),
    (22, 7.2527e-4, 1.5956e-2, 3.5103e-1, 7.7226e0, 1.6990e2),
    (23, 4.5848e-4, 1.0545e-2, 2.4254e-1, 5.5783e0, 1.2830e2),
    (24, 2.8945e-4, 6.9468e-3, 1.6672e-1, 4.0013e0, 9.6032e1),
    (25, 1.8251e-4, 4.5626e-3, 1.1407e-1, 2.8516e0, 7.1291e1),
    (26, 1.1493e-4, 2.9882e-3, 7.7694e-2, 2.0200e0, 5.2521e1),
    (27, 7.2293e-5, 1.9519e-3, 5.2702e-2, 1.4229e0, 3.8419e1),
    (28, 4.5421e-5, 1.2718e-3, 3.5610e-2, 9.9708e-1, 2.7918e1),
    (29, 2.8507e-5, 8.2670e-4, 2.3974e-2, 6.9525e-1, 2.0162e1),
    (30, 1.7873e-5, 5.3619e-4, 1.6086e-2, 4.8257e-1, 1.4477e1),
    (43, 8.5986e-7, 3.7618e-5, 1.6458e-3, 7.2000e-2, 3.1500e0),
    (19 * Real.log 10, 8.6315e-7, 3.7978e-5, 1.6711e-3, 7.3526e-2, 3.2352e0),
    (44, 7.8162e-7, 3.5173e-5, 1.5828e-3, 7.1225e-2, 3.2052e0),
    (45, 5.0646e-7, 2.3297e-5, 1.0717e-3, 4.9297e-2, 2.2677e0),
    (46, 3.2935e-7, 1.5479e-5, 7.2752e-4, 3.4194e-2, 1.6071e0),
    (47, 2.1307e-7, 1.0228e-5, 4.9092e-4, 2.3564e-2, 1.1311e0),
    (54, 9.8777e-9, 5.4328e-7, 2.9880e-5, 1.6434e-3, 9.0388e-2),
    (55, 6.3417e-9, 3.5514e-7, 1.9888e-5, 1.1137e-3, 6.2367e-2),
    (56, 4.0668e-9, 2.3181e-7, 1.3213e-5, 7.5315e-4, 4.2929e-2),
    (2275, 4.4153e-9, 1.0155e-5, 2.3357e-2, 5.3721e1, 1.2356e5),
    (2300, 4.4627e-9, 1.0376e-5, 2.4124e-2, 5.6088e1, 1.3040e5),
    (2325, 4.4062e-9, 1.0355e-5, 2.4333e-2, 5.7184e1, 1.3438e5),
    (2350, 4.2245e-9, 1.0033e-5, 2.3829e-2, 5.6593e1, 1.3441e5),
    (2375, 4.0498e-9, 9.7196e-6, 2.3327e-2, 5.5985e1, 1.3436e5),
    (2400, 3.8820e-9, 9.4139e-6, 2.2829e-2, 5.5360e1, 1.3425e5),
    (9800, 8.4841e-25, 8.3992e-21, 8.3152e-17, 8.2321e-13, 8.1497e-9),
    (9900, 5.7395e-25, 5.7395e-21, 5.7395e-17, 5.7395e-13, 5.7395e-9),
    (10000, 3.8228e-25, 3.8610e-21, 3.8996e-17, 3.9386e-13, 3.9780e-9),
    (11100, 5.4156e-27, 6.0654e-23, 6.7933e-19, 7.6085e-15, 8.5215e-11),
    (12000, 1.9330e-28, 2.3390e-24, 2.8302e-20, 3.4245e-16, 4.1436e-12),
    (13000, 5.5830e-30, 7.5370e-26, 1.0175e-21, 1.3736e-17, 1.8544e-13),
    (14000, 1.8398e-31, 2.7597e-27, 4.1396e-23, 6.2094e-19, 9.3141e-15),
    (15000, 6.5711e-33, 1.0514e-28, 1.6822e-24, 2.6915e-20, 4.3065e-16),
    (16000, 2.5738e-34, 4.3755e-30, 7.4384e-26, 1.2645e-21, 2.1497e-17),
    (17000, 1.1167e-35, 2.0101e-31, 3.6182e-27, 6.5127e-23, 1.1723e-18),
    (18000, 5.3738e-37, 1.0210e-32, 1.9400e-28, 3.6859e-24, 7.0032e-20),
    (19000, 2.7357e-38, 5.4714e-34, 1.0943e-29, 2.1886e-25, 4.3771e-21),
    (20000, 1.5040e-39, 3.1585e-35, 6.6328e-31, 1.3929e-26, 2.9251e-22),
    (21000, 9.0605e-41, 1.9933e-36, 4.3853e-32, 9.6476e-28, 2.1225e-23),
    (22000, 5.6101e-42, 1.2903e-37, 2.9677e-33, 6.8258e-29, 1.5699e-24),
    (23000, 3.7554e-43, 9.0129e-39, 2.1631e-34, 5.1914e-30, 1.2460e-25),
    (24000, 2.6755e-44, 6.6888e-40, 1.6722e-35, 4.1805e-31, 1.0451e-26)
  ]

def table_11 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) := [
  (20, 1.6844e-3, 3.3688e-2, 6.7375e-1, 5.7184e1, 1.3441e5),
  (21, 1.0684e-3, 2.2435e-2, 4.7114e-1, 5.7184e1, 1.3441e5),
  (22, 6.7654e-4, 1.4884e-2, 3.2746e-1, 5.7184e1, 1.3441e5),
  (23, 4.2780e-4, 9.8392e-3, 2.2631e-1, 5.7184e1, 1.3441e5),
  (24, 2.7011e-4, 6.4827e-3, 1.5559e-1, 5.7184e1, 1.3441e5),
  (25, 1.7500e-4, 4.3750e-3, 1.0938e-1, 5.7184e1, 1.3441e5),
  (26, 1.1022e-4, 2.8655e-3, 7.4503e-2, 5.7184e1, 1.3441e5),
  (27, 6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5),
  (28, 4.3555e-5, 1.2196e-3, 3.4148e-2, 5.7184e1, 1.3441e5),
  (29, 2.7336e-5, 7.9272e-4, 2.4334e-2, 5.7184e1, 1.3441e5),
  (30, 1.7139e-5, 5.1415e-4, 2.4334e-2, 5.7184e1, 1.3441e5),
  (43, 8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (44, 7.8163e-7, 3.5174e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (45, 5.0646e-7, 2.3298e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (46, 3.2935e-7, 1.5480e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (47, 2.1308e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (54, 9.8778e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (55, 6.3417e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (56, 4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (2275, 4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5),
  (2300, 4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e-1, 1.3441e5),
  (2325, 4.4063e-9, 1.0355e-5, 2.4334e-2, 5.7184e-1, 1.3441e5),
  (2350, 4.2245e-9, 1.0034e-5, 2.3829e-2, 5.6594e-1, 1.3441e5),
  (2375, 4.0499e-9, 9.7196e-6, 2.3328e-2, 5.5985e-1, 1.3437e5),
  (2400, 3.8821e-9, 9.4139e-6, 2.2829e-2, 5.5360e-1, 1.3425e5),
  (9800, 8.4841e-25, 8.3993e-21, 8.3153e-17, 8.2321e-13, 8.1498e-9),
  (9900, 5.7396e-25, 5.7396e-21, 5.7396e-17, 5.7396e-13, 5.7396e-9),
  (10000, 3.8228e-25, 3.8610e-21, 3.8997e-17, 3.9387e-13, 3.9780e-9),
  (11100, 7.9284e-27, 8.8005e-23, 9.7685e-19, 1.0844e-14, 1.2036e-10),
  (12000, 1.9331e-28, 2.3390e-24, 2.8302e-20, 3.4245e-16, 4.1437e-12),
  (13000, 5.5830e-30, 7.5371e-26, 1.0175e-21, 1.3737e-17, 1.8544e-13),
  (14000, 1.8399e-31, 2.7598e-27, 4.1396e-23, 6.2094e-19, 9.3141e-15),
  (15000, 6.5712e-33, 1.0514e-28, 1.6823e-24, 2.6916e-20, 4.3065e-16),
  (16000, 2.5739e-34, 4.3756e-30, 7.4384e-26, 1.2646e-21, 2.1497e-17),
  (17000, 1.1168e-35, 2.0101e-31, 3.6182e-27, 6.5127e-23, 1.1723e-18),
  (18000, 5.3739e-37, 1.0211e-32, 1.9400e-28, 3.6860e-24, 7.0033e-20),
  (19000, 2.7357e-38, 5.4714e-34, 1.0943e-29, 2.1886e-25, 4.3772e-21),
  (20000, 1.5041e-39, 3.1585e-35, 6.6329e-31, 1.3929e-26, 2.9251e-22),
  (21000, 9.0606e-41, 1.9934e-36, 4.3853e-32, 9.6477e-28, 2.1225e-23),
  (22000, 5.6101e-42, 1.2904e-37, 2.9678e-33, 6.8258e-29, 1.5700e-24),
  (23000, 3.7554e-43, 9.0129e-39, 2.1631e-34, 5.1915e-30, 1.2460e-25),
  (24000, 1.3804e-43, 3.4508e-39, 8.6269e-35, 2.1568e-30, 5.3919e-26),
  (25000, 1.3804e-43, 3.4508e-39, 8.6269e-35, 2.1568e-30, 5.3919e-26)
]

/-
\subsubsection{Lower bound for first values of $x \in [e^{J_0},10^{19}]$}
\quad \\
{\footnotesize
\begin{longtable}{ccrrrrrr}
\caption{$\theta(x) -x >  - \frac{\mathcal{C}_{b,k} x}{(\log x)^k}$ for all $x \in [e^b, 10^{19} )$, where $\mathcal{C}_{b,k}$ is defined in \eqref{defn:mathcalCbk}.}
 \label{CkValues}
\\
\hline
\multicolumn{1}{c}{\phantom{}} &
\multicolumn{1}{c}{$b$  } &
\multicolumn{1}{c}{$\mathcal{C}_{b,1}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,2}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,3}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,4}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,5}$ } &
\multicolumn{1}{c}{\phantom{}}
\\ \hline
\endfirsthead
\multicolumn{8}{c}%
{\tablename\ \thetable{} -- continued from previous page} \\
\hline
\multicolumn{1}{c}{\phantom{}} &
\multicolumn{1}{c}{$b$  } &
\multicolumn{1}{c}{$\mathcal{C}_{b,1}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,2}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,3}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,4}$ } &
\multicolumn{1}{c}{$\mathcal{C}_{b,5}$ } &
\multicolumn{1}{c}{\phantom{}}
\\ \hline
\endhead
\hline \multicolumn{8}{r}{Continued on next page} \\ \hline
\endfoot
\hline
\endlastfoot
&&&&&&& \\[-1em]
\multicolumn{8}{c}{Calculated using $c=0.8$, $C=0.81$, each value valid up to $5\cdot10^{10}\simeq e^{24.635}$.}\\ \hline
&&&&&&& \\[-1em]
& $ 20 $ & $ 1.68440 \cdot 10^{-3} $ & $ 3.36880 \cdot 10^{-2} $ & $ 6.73750 \cdot 10^{-1} $ & $ 1.34750 \cdot 10^{1} $ & $ 2.69500 \cdot 10^{2 } $ & \\
& $ 21 $ & $ 1.06840 \cdot 10^{-3} $ & $ 2.24350 \cdot 10^{-2} $ & $ 4.71140 \cdot 10^{-1} $ & $ 9.89390 \cdot 10^{0} $ & $ 2.07780 \cdot 10^{2 } $ & \\
& $ 22 $ & $ 6.76540 \cdot 10^{-4} $ & $ 1.48840 \cdot 10^{-2} $ & $ 3.27450 \cdot 10^{-1} $ & $ 7.20380 \cdot 10^{0} $ & $ 1.58490 \cdot 10^{2 } $ & \\
& $ 23 $ & $ 4.27800 \cdot 10^{-4} $ & $ 9.83920 \cdot 10^{-3} $ & $ 2.26310 \cdot 10^{-1} $ & $ 5.20500 \cdot 10^{0} $ & $ 1.19720 \cdot 10^{2 } $ & \\
& $ 24 $ & $ 2.70120 \cdot 10^{-4} $ & $ 6.48290 \cdot 10^{-3} $ & $ 1.55590 \cdot 10^{-1} $ & $ 3.73410 \cdot 10^{0} $ & $ 8.96190 \cdot 10^{1 } $ & \\
\hline
&&&&&&& \\[-1em]
\multicolumn{8}{c}{Calculated using $c=0.88$, $C=0.86$, each value valid up to $32\cdot10^{12}\simeq e^{31.097}$.}\\ \hline
&&&&&&& \\[-1em]
& $ \log(5\cdot 10^{10}) $ & $ 2.01560 \cdot 10^{-4} $ & $ 4.96540 \cdot 10^{-3} $ & $ 1.22330 \cdot 10^{-1} $ & $ 3.01350 \cdot 10^{0} $ & $ 7.42380 \cdot 10^{1 } $ & \\
& $ 25 $ & $ 1.70330 \cdot 10^{-4}$ &$ 4.25830 \cdot 10^{-3} $ & $ 1.06460 \cdot 10^{-1} $ & $ 2.66140 \cdot 10^{0} $ & $ 6.65350 \cdot 10^{1 } $ & \\
& $ 26 $ & $ 1.10220 \cdot 10^{-4} $ & $ 2.86560 \cdot 10^{-3} $ & $ 7.45050 \cdot 10^{-2} $ & $ 1.93720 \cdot 10^{0} $ & $ 5.03650 \cdot 10^{1 } $ & \\
& $ 27 $ & $ 6.93270 \cdot 10^{-5} $ & $ 1.87190 \cdot 10^{-3} $ & $ 5.05400 \cdot 10^{-2} $ & $ 1.36460 \cdot 10^{0} $ & $ 3.68430 \cdot 10^{1 } $ & \\
& $ 28 $ & $ 4.35580 \cdot 10^{-5} $ & $ 1.21970 \cdot 10^{-3} $ & $ 3.41500 \cdot 10^{-2} $ & $ 9.56180 \cdot 10^{-1} $ & $ 2.67730 \cdot 10^{1 } $ & \\
& $ 29 $ & $ 2.73380 \cdot 10^{-5} $ & $ 7.92780 \cdot 10^{-4} $ & $ 2.29910 \cdot 10^{-2} $ & $ 6.66730 \cdot 10^{-1} $ & $ 1.93360 \cdot 10^{1 } $ & \\
& $ 30 $ & $ 1.71400 \cdot 10^{-5} $ & $ 5.14180 \cdot 10^{-4} $ & $ 1.54260 \cdot 10^{-2} $ & $ 4.62760 \cdot 10^{-1} $ & $ 1.38830 \cdot 10^{1 } $ & \\
& $ 31 $ & $ 1.07350 \cdot 10^{-5} $ & $ 3.32790 \cdot 10^{-4} $ & $ 1.03170 \cdot 10^{-2} $ & $ 3.19810 \cdot 10^{-1} $ & $ 9.91400 \cdot 10^{0 } $ & \\
\hline
&&&&&&& \\[-1em]
\multicolumn{8}{c}{Calculated using $c=C=0.94$, each value valid up to $10^{19}\simeq e^{43.749}$.}\\ \hline
&&&&&&& \\[-1em]
& $ \log(3.2\cdot10^{13}) $ & $ 1.02600 \cdot 10^{-5} $ & $ 3.19040 \cdot 10^{-4} $ & $ 9.92090 \cdot 10^{-3} $ & $ 3.08510 \cdot 10^{-1} $ & $ 9.59360 \cdot 10^{0 } $ & \\
& $ 32 $ & $ 6.71750 \cdot 10^{-6} $ & $ 2.14960 \cdot 10^{-4} $ & $ 6.87870 \cdot 10^{-3} $ & $ 2.20120 \cdot 10^{-1} $ & $ 7.04380 \cdot 10^{0 } $ & \\
& $ 33 $ & $ 4.38000 \cdot 10^{-6} $ & $ 1.44540 \cdot 10^{-4} $ & $ 4.76990 \cdot 10^{-3} $ & $ 1.57410 \cdot 10^{-1} $ & $ 5.19440 \cdot 10^{0 } $ & \\
& $ 34 $ & $ 2.73610 \cdot 10^{-6} $ & $ 9.30270 \cdot 10^{-5} $ & $ 3.16300 \cdot 10^{-3} $ & $ 1.07540 \cdot 10^{-1} $ & $ 3.65640 \cdot 10^{0 } $ & \\
& $ 35 $ & $ 1.70780 \cdot 10^{-6} $ & $ 5.97730 \cdot 10^{-5} $ & $ 2.09210 \cdot 10^{-3} $ & $ 7.32220 \cdot 10^{-2} $ & $ 2.56280 \cdot 10^{0 } $ & \\
& $ 36 $ & $ 1.06520 \cdot 10^{-6} $ & $ 3.83460 \cdot 10^{-5} $ & $ 1.38050 \cdot 10^{-3} $ & $ 4.96960 \cdot 10^{-2} $ & $ 1.78910 \cdot 10^{0 } $ & \\
& $ 37 $ & $ 6.63850 \cdot 10^{-7} $ & $ 2.45630 \cdot 10^{-5} $ & $ 9.08810 \cdot 10^{-4} $ & $ 3.36260 \cdot 10^{-2} $ & $ 1.24420 \cdot 10^{0 } $ & \\
& $ 38 $ & $ 4.13450 \cdot 10^{-7} $ & $ 1.57120 \cdot 10^{-5} $ & $ 5.97020 \cdot 10^{-4} $ & $ 2.26870 \cdot 10^{-2} $ & $ 8.62100 \cdot 10^{-1 } $ & \\
& $ 39 $ & $ 2.57330 \cdot 10^{-7} $ & $ 1.00360 \cdot 10^{-5} $ & $ 3.91400 \cdot 10^{-4} $ & $ 1.52650 \cdot 10^{-2} $ & $ 5.95320 \cdot 10^{-1 } $ & \\
& $ 40 $ & $ 1.60060 \cdot 10^{-7} $ & $ 6.40240 \cdot 10^{-6} $ & $ 2.56100 \cdot 10^{-4} $ & $ 1.02440 \cdot 10^{-2} $ & $ 4.09750 \cdot 10^{-1 } $ & \\
& $ 41 $ & $ 9.94970 \cdot 10^{-8} $ & $ 4.07940 \cdot 10^{-6} $ & $ 1.67260 \cdot 10^{-4} $ & $ 6.85740 \cdot 10^{-3} $ & $ 2.81160 \cdot 10^{-1 } $ & \\
& $ 42 $ & $ 6.18140 \cdot 10^{-8} $ & $ 2.59620 \cdot 10^{-6} $ & $ 1.09040 \cdot 10^{-4} $ & $ 4.57970 \cdot 10^{-3} $ & $ 1.92350 \cdot 10^{-1 } $ & \\
& $ 43 $ & $ 3.83820 \cdot 10^{-8} $ & $ 1.65050 \cdot 10^{-6} $ & $ 7.09680 \cdot 10^{-5} $ & $ 3.05170 \cdot 10^{-3} $ & $ 1.31220 \cdot 10^{-1 } $ & \\
\hline
\end{longtable}
}-/

noncomputable def table_12 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ) := [
  (20, 1.68440e-3, 3.36880e-2, 6.73750e-1, 1.34750e1, 2.69500e2, 0.8, 0.81, 5e10),
  (21, 1.06840e-3, 2.24350e-2, 4.71140e-1, 9.89390e0, 2.07780e2, 0.8, 0.81, 5e10),
  (22, 6.76540e-4, 1.48840e-2, 3.27450e-1, 7.20380e0, 1.58490e2, 0.8, 0.81, 5e10),
  (23, 4.27800e-4, 9.83920e-3, 2.26310e-1, 5.20500e0, 1.19720e2, 0.8, 0.81, 5e10),
  (24, 2.70120e-4, 6.48290e-3, 1.55590e-1, 3.73410e0, 8.96190e1, 0.8, 0.81, 5e10),
  (Real.log 5e10, 2.01560e-4, 4.96540e-3, 1.22330e-1, 3.01350e0, 7.42380e1, 0.88, 0.86, 32e12),
  (25, 1.70330e-4, 4.25830e-3, 1.06460e-1, 2.66140e0, 6.65350e1, 0.88, 0.86, 32e12),
  (26, 1.10220e-4, 2.86560e-3, 7.45050e-2, 1.93720e0, 5.03650e1, 0.88, 0.86, 32e12),
  (27, 6.93270e-5, 1.87190e-3, 5.05400e-2, 1.36460e0, 3.68430e1, 0.88, 0.86, 32e12),
  (28, 4.35580e-5, 1.21970e-3, 3.41500e-2, 9.56180e-1, 2.67730e1, 0.88, 0.86, 32e12),
  (29, 2.73380e-5, 7.92780e-4, 2.29910e-2, 6.66730e-1, 1.93360e1, 0.88, 0.86, 32e12),
  (30, 1.71400e-5, 5.14180e-4, 1.54260e-2, 4.62760e-1, 1.38830e1, 0.88, 0.86, 32e12),
  (31, 1.07350e-5, 3.32790e-4, 1.03170e-2, 3.19810e-1, 9.91400e0, 0.88, 0.86, 32e12),
  (Real.log (32e12), 1.02600e-5, 3.19040e-4, 9.92090e-3, 3.08510e-1, 9.59360e0, 0.94, 0.94, 1e19),
  (32, 6.71750e-6, 2.14960e-4, 6.87870e-3, 2.20120e-1, 7.04380e0, 0.94, 0.94, 1e19),
  (33, 4.38000e-6, 1.44540e-4, 4.76990e-3, 1.57410e-1, 5.19440e0, 0.94, 0.94, 1e19),
  (34, 2.73610e-6, 9.30270e-5, 3.16300e-3, 1.07540e-1, 3.65640e0, 0.94, 0.94, 1e19),
  (35, 1.70780e-6, 5.97730e-5, 2.09210e-3, 7.32220e-2, 2.56280e0, 0.94, 0.94, 1e19),
  (36, 1.06520e-6, 3.83460e-5, 1.38050e-3, 4.96960e-2, 1.78910e0, 0.94, 0.94, 1e19),
  (37, 6.63850e-7, 2.45630e-5, 9.08810e-4, 3.36260e-2, 1.24420e0, 0.94, 0.94, 1e19),
  (38, 4.13450e-7, 1.57120e-5, 5.97020e-4, 2.26870e-2, 8.62100e-1, 0.94, 0.94, 1e19),
  (39, 2.57330e-7, 1.00360e-5, 3.91400e-4, 1.52650e-2, 5.95320e-1, 0.94, 0.94, 1e19),
  (40, 1.60060e-7, 6.40240e-6, 2.56100e-4, 1.02440e-2, 4.09750e-1, 0.94, 0.94, 1e19),
  (41, 9.94970e-8, 4.07940e-6, 1.67260e-4, 6.85740e-3, 2.81160e-1, 0.94, 0.94, 1e19),
  (42, 6.18140e-8, 2.59620e-6, 1.09040e-4, 4.57970e-3, 1.92350e-1, 0.94, 0.94, 1e19),
  (43,3.83820e-8 ,1.65050e-6 ,7.09680e-5 ,3.05170e-3 ,1.31220e-1, 0.94, 0.94, 1e19)
]

end BKLNW
