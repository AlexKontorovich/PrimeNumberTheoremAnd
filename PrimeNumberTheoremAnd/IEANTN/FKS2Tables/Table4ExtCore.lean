import PrimeNumberTheoremAnd.IEANTN.SecondaryDefinitions
import LeanCert.ANT.Asymp

/-!
# Extended Table 4 cell certificates (FKS2, towards Corollary 22)

Machinery for verifying the Corollary 22 interpolation over the extended
ancillary tables of FKS2 (arXiv 2206.12557, anc/PrimeCountingTables.pdf).

Each `Cell` records one grid interval `[exp b, exp b']` together with the
table value `ε = ε_{π,num}(e^b)` and rational enclosures `slo ≤ √b`,
`√b' ≤ shi`. The boolean `checkCell` verifies, by dyadic interval
arithmetic in the variable `s = √(log x)`, that

  `exp (C·s) ≤ (A/ε)·s³`  on `[slo, shi]`,

which transports to the continuous inequality

  `ε ≤ admissible_bound A (3/2) C 1 x`  for all `x ∈ [exp b, exp b']`.

The exponential is evaluated as `(exp (C·s/64))^64` so the dyadic kernel
only sees arguments of order one, and the tiny table values `ε` enter only
through the exact rational constant `A/ε` (constants below the dyadic grid
resolution must not appear in checked expressions).
-/

namespace FKS2
namespace Table4Ext

open Real LeanCert.Core LeanCert.ANT.Asymp

/-- Corollary 22 curve constant `A = 9.2211`. -/
def Aq : ℚ := 92211 / 10000

/-- Corollary 22 curve constant `C = 0.8476`. -/
def Cq : ℚ := 2119 / 2500

/-- `C / 64`, the split-exponential kernel coefficient. -/
def Cq64 : ℚ := 2119 / 160000

/-- Expression-level squaring. -/
def sqE (e : Expr) : Expr := Expr.mul e e

/-- `(exp (C·s/64))^64` as an expression in `s = Expr.var 0`. -/
def expSplit : Expr :=
  sqE (sqE (sqE (sqE (sqE (sqE
    (Expr.exp (Expr.mul (Expr.const Cq64) (Expr.var 0))))))))

/-- `q·s³` as an expression in `s = Expr.var 0`. -/
def cubeRhs (q : ℚ) : Expr :=
  Expr.mul (Expr.const q)
    (Expr.mul (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.var 0))

/-- One interpolation cell. Proof-free data: rows are generated from the
extended ancillary table and checked by `native_decide`. -/
structure Cell where
  /-- Left endpoint of the cell in log space. -/
  b : ℕ
  /-- Right endpoint of the cell in log space. -/
  b' : ℕ
  /-- Table value `ε_{π,num}(e^b)`. -/
  eps : ℚ
  /-- Rational lower enclosure of `√b`. -/
  slo : ℚ
  /-- Rational upper enclosure of `√b'`. -/
  shi : ℚ
  deriving Repr, DecidableEq

/-- Boolean verification of one cell: side conditions plus the dyadic slab
check of `exp(C·s) ≤ (A/ε)·s³` on `[slo, shi]`. -/
def checkCell (c : Cell) : Bool :=
  if h : c.slo ≤ c.shi then
    decide (0 < c.eps) && decide (0 ≤ c.slo) &&
    decide (c.slo * c.slo ≤ (c.b : ℚ)) &&
    decide ((c.b' : ℚ) ≤ c.shi * c.shi) &&
    checkExprLeOnIntervalDyadic expSplit (cubeRhs (Aq / c.eps))
      ⟨c.slo, c.shi, h⟩ (-50) 8
  else false

lemma expSplit_supported (q : ℚ) :
    ExprSupportedWithInv (Expr.sub expSplit (cubeRhs q)) := by
  simp only [Expr.sub, expSplit, cubeRhs, sqE]
  repeat constructor

lemma eval_sqE (ρ : ℕ → ℝ) (e : Expr) :
    Expr.eval ρ (sqE e) = (Expr.eval ρ e) ^ (2 : ℕ) := by
  simp [sqE, Expr.eval_mul, sq]

lemma eval_expSplit (s : ℝ) :
    Expr.eval (fun _ => s) expSplit = exp ((Cq64 : ℝ) * s) ^ (64 : ℕ) := by
  simp only [expSplit, eval_sqE, Expr.eval_exp, Expr.eval_mul,
    Expr.eval_const, Expr.eval_var, ← pow_mul]

lemma eval_cubeRhs (q : ℚ) (s : ℝ) :
    Expr.eval (fun _ => s) (cubeRhs q) = (q : ℝ) * s ^ (3 : ℕ) := by
  simp only [cubeRhs, Expr.eval_mul, Expr.eval_const, Expr.eval_var]
  ring

set_option maxHeartbeats 1000000 in
-- One long transport declaration; every step is cheap but the default
-- budget is exceeded cumulatively.
/-- Transport: a checked cell dominates the table value by the Corollary 22
curve on the whole cell `[exp b, exp b']`. -/
theorem cell_eps_le_admissible (c : Cell) (hc : checkCell c = true) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      (c.eps : ℝ) ≤ admissible_bound (Aq : ℝ) (3 / 2) (Cq : ℝ) 1 x := by
  -- unpack the boolean
  unfold checkCell at hc
  split at hc
  case isFalse => simp at hc
  case isTrue hle =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨heps, hslo0⟩, hslo⟩, hshi⟩, hcheck⟩ := hc
    -- the slab inequality, semantically
    have hslab := verify_expr_le_on_interval_dyadic expSplit
      (cubeRhs (Aq / c.eps)) ⟨c.slo, c.shi, hle⟩ (-50) 8
      (expSplit_supported _) (by norm_num) hcheck
    intro x hx
    obtain ⟨hx_lo, hx_hi⟩ := hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (exp_pos _) hx_lo
    -- log x ∈ [b, b']
    have hb_le : (c.b : ℝ) ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxpos).mpr hx_lo
    have hb'_ge : Real.log x ≤ (c.b' : ℝ) :=
      (Real.log_le_iff_le_exp hxpos).mpr hx_hi
    have hlog_nonneg : (0 : ℝ) ≤ Real.log x :=
      le_trans (Nat.cast_nonneg _) hb_le
    -- s = √(log x) ∈ [slo, shi]
    set s : ℝ := Real.sqrt (Real.log x) with hs_def
    have h0lo : (0 : ℝ) ≤ (c.slo : ℝ) := by exact_mod_cast hslo0
    have h0hi : (0 : ℝ) ≤ (c.shi : ℝ) := by
      have : ((c.slo : ℚ) : ℝ) ≤ ((c.shi : ℚ) : ℝ) := by exact_mod_cast hle
      linarith
    have hs_lo : (c.slo : ℝ) ≤ s := by
      have h1 : ((c.slo : ℝ)) ^ 2 ≤ Real.log x := by
        have hq : ((c.slo : ℝ)) * ((c.slo : ℝ)) ≤ ((c.b : ℕ) : ℝ) := by
          exact_mod_cast hslo
        calc ((c.slo : ℝ)) ^ 2 = ((c.slo : ℝ)) * ((c.slo : ℝ)) := pow_two _
          _ ≤ ((c.b : ℕ) : ℝ) := hq
          _ ≤ Real.log x := hb_le
      calc (c.slo : ℝ) = Real.sqrt (((c.slo : ℝ)) ^ 2) :=
            (Real.sqrt_sq h0lo).symm
        _ ≤ s := Real.sqrt_le_sqrt h1
    have hs_hi : s ≤ (c.shi : ℝ) := by
      have h1 : Real.log x ≤ ((c.shi : ℝ)) ^ 2 := by
        have hq : ((c.b' : ℕ) : ℝ) ≤ ((c.shi : ℝ)) * ((c.shi : ℝ)) := by
          exact_mod_cast hshi
        calc Real.log x ≤ ((c.b' : ℕ) : ℝ) := hb'_ge
          _ ≤ ((c.shi : ℝ)) * ((c.shi : ℝ)) := hq
          _ = ((c.shi : ℝ)) ^ 2 := (pow_two _).symm
      calc s ≤ Real.sqrt (((c.shi : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (c.shi : ℝ) := Real.sqrt_sq h0hi
    -- instantiate the slab inequality at s
    have hineq := hslab s ⟨hs_lo, hs_hi⟩
    rw [eval_expSplit, eval_cubeRhs] at hineq
    -- (exp (C/64·s))^64 = exp (C·s)
    have hCC : ((Cq64 : ℚ) : ℝ) * 64 = ((Cq : ℚ) : ℝ) := by
      simp only [Cq64, Cq]
      push_cast
      norm_num
    have hexp64 : exp ((Cq64 : ℝ) * s) ^ (64 : ℕ) = exp ((Cq : ℝ) * s) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [← hCC]
      ring
    rw [hexp64] at hineq
    -- divide back: exp(C·s) ≤ (A/ε)·s³  →  ε·exp(C·s) ≤ A·s³
    have heps_pos : (0 : ℝ) < (c.eps : ℝ) := by exact_mod_cast heps
    have hexp_pos : (0 : ℝ) < exp ((Cq : ℝ) * s) := exp_pos _
    have hdiv : ((Aq / c.eps : ℚ) : ℝ) = (Aq : ℝ) / (c.eps : ℝ) := by
      push_cast
      ring
    rw [hdiv] at hineq
    have h2 : (c.eps : ℝ) * exp ((Cq : ℝ) * s) ≤ (Aq : ℝ) * s ^ (3 : ℕ) := by
      have h3 := mul_le_mul_of_nonneg_left hineq (le_of_lt heps_pos)
      calc (c.eps : ℝ) * exp ((Cq : ℝ) * s)
          ≤ (c.eps : ℝ) * ((Aq : ℝ) / (c.eps : ℝ) * s ^ (3 : ℕ)) := h3
        _ = (Aq : ℝ) * s ^ (3 : ℕ) := by field_simp
    -- ε ≤ A·s³·exp(−C·s)
    have key : (c.eps : ℝ) ≤ (Aq : ℝ) * s ^ (3 : ℕ) * exp (-((Cq : ℝ) * s)) := by
      have h4 := mul_le_mul_of_nonneg_right h2
        (le_of_lt (inv_pos.mpr hexp_pos))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hexp_pos), mul_one] at h4
      rw [Real.exp_neg]
      exact h4
    -- identify the curve: admissible_bound A (3/2) C 1 x = A·s³·exp(−C·s)
    have hs_rpow : s = Real.log x ^ ((1 : ℝ) / 2) := by
      rw [hs_def, Real.sqrt_eq_rpow]
    have h32 : Real.log x ^ ((3 : ℝ) / 2) = s ^ (3 : ℕ) := by
      rw [hs_rpow, ← Real.rpow_natCast (Real.log x ^ ((1 : ℝ) / 2)) 3,
        ← Real.rpow_mul hlog_nonneg]
      norm_num
    have hcurve : admissible_bound (Aq : ℝ) (3 / 2) (Cq : ℝ) 1 x
        = (Aq : ℝ) * s ^ (3 : ℕ) * exp (-((Cq : ℝ) * s)) := by
      unfold admissible_bound
      rw [div_one, show ((3 : ℝ) / 2) = (3 : ℝ) / 2 from rfl, h32,
        ← hs_rpow, neg_mul]
    rw [hcurve]
    exact key

/-- A checked cell together with its trusted row bound gives the Corollary 22
curve bound for `Eπ` on the cell. -/
theorem cell_Epi_le_admissible (c : Cell) (hc : checkCell c = true)
    (hrow : Eπ.bound (c.eps : ℝ) (exp (c.b : ℝ))) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      Eπ x ≤ admissible_bound (Aq : ℝ) (3 / 2) (Cq : ℝ) 1 x := by
  intro x hx
  exact le_trans (hrow x hx.1) (cell_eps_le_admissible c hc x hx)

end Table4Ext
end FKS2
