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
              have h_log_approx : 43 < 19 * log 10 ∧ 19 * log 10 < 44 := by
                rw [← log_rpow, lt_log_iff_exp_lt, log_lt_iff_lt_exp] <;> norm_num
                refine ⟨?_, ?_⟩
                · have := exp_one_lt_d9.le
                  rw [show exp 43 = (exp 1) ^ 43 by rw [← exp_nat_mul]; norm_num]
                  exact (pow_le_pow_left₀ (by positivity) this _).trans_lt <| by norm_num
                · have := exp_one_gt_d9.le
                  rw [show exp 44 = (exp 1) ^ 44 by rw [← exp_nat_mul]; norm_num]
                  exact lt_of_lt_of_le (by norm_num) <| pow_le_pow_left₀ (by positivity) this _
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


end BKLNW
