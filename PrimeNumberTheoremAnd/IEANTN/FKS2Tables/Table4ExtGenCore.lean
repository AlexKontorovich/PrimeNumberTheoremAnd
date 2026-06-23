import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtCore

/-!
# Generalized extended-Table-4 cell transport (FKS2, towards Corollary 23)

`Table4ExtCore` proves `eps ≤ admissible_bound` for the **Corollary 22** curve
only (hardcoded `A = 9.2211`, `B = 3/2`, `C = 0.8476`, `R = 1`).  Corollary 23
needs the same numerical-envelope data (`allCells`: `eps, slo, shi`, which are
**curve-independent**) transported to nine *different* admissible curves with
`R = 5.5666305` and integer `2B ∈ {1,2,3,4}`.

This file generalizes the dyadic transport.  For a row `(A,B,C,R)` with
`s = √(log x)` and `k = 2B`,

  `admissible_bound A B C R x = (A/R^B)·s^k·exp(−(C/√R)·s)`,

so `eps ≤ admissible_bound A B C R x` is equivalent to the dyadic check

  `exp((C/√R)·s) ≤ (A/(eps·R^B))·s^k    on [slo, shi].`

We over-estimate the two transcendental constants by rationals — `ĉ ≥ C/√R`
(exp coefficient) and `rB ≥ R^B` (so the polynomial coefficient `A/(eps·rB)`
under-estimates the true `A/(eps·R^B)`).  Both push the checked inequality in
the *stronger* direction, so a passing check implies the true bound.
-/

namespace FKS2
namespace Table4Ext

open Real LeanCert.Core LeanCert.ANT.Asymp

/-- `(exp (c64·s))^64` as an expression in `s = Expr.var 0`, with a *parametric*
exp coefficient `c64` (= `ĉ/64`). -/
def expSplitC (c64 : ℚ) : Expr :=
  sqE (sqE (sqE (sqE (sqE (sqE
    (Expr.exp (Expr.mul (Expr.const c64) (Expr.var 0))))))))

/-- `q·s^k` as an expression in `s = Expr.var 0` (integer power `k = 2B`). -/
def powRhs (q : ℚ) (k : ℕ) : Expr :=
  Expr.mul (Expr.const q) (Expr.pow (Expr.var 0) k)

lemma eval_expSplitC (c64 : ℚ) (s : ℝ) :
    Expr.eval (fun _ => s) (expSplitC c64) = exp ((c64 : ℝ) * s) ^ (64 : ℕ) := by
  simp only [expSplitC, eval_sqE, Expr.eval_exp, Expr.eval_mul,
    Expr.eval_const, Expr.eval_var, ← pow_mul]

lemma eval_powRhs (q : ℚ) (k : ℕ) (s : ℝ) :
    Expr.eval (fun _ => s) (powRhs q k) = (q : ℝ) * s ^ k := by
  simp only [powRhs, Expr.eval_mul, Expr.eval_const, Expr.eval_pow, Expr.eval_var]

/-- Integer powers of a supported expression are supported. -/
lemma pow_supported {e : Expr} (he : ExprSupportedWithInv e) :
    ∀ k, ExprSupportedWithInv (Expr.pow e k)
  | 0 => ExprSupportedWithInv.const 1
  | (n + 1) => ExprSupportedWithInv.mul he (pow_supported he n)

lemma sub_supported (c64 q : ℚ) (k : ℕ) :
    ExprSupportedWithInv (Expr.sub (expSplitC c64) (powRhs q k)) := by
  have hL : ExprSupportedWithInv (expSplitC c64) := by
    simp only [expSplitC, sqE]; repeat constructor
  have hR : ExprSupportedWithInv (powRhs q k) :=
    ExprSupportedWithInv.mul (ExprSupportedWithInv.const q)
      (pow_supported (ExprSupportedWithInv.var 0) k)
  rw [Expr.sub]
  exact ExprSupportedWithInv.add hL (ExprSupportedWithInv.neg hR)

/-- Parameters of a generalized (row) cell check: the rational exp coefficient
`c64 = ĉ/64`, the integer power `k = 2B`, a rational `rB ≥ R^B`, and the row
`Aq = A`. -/
structure CellParams where
  /-- `ĉ/64` where `ĉ ≥ C/√R`. -/
  c64 : ℚ
  /-- `2B` (integer). -/
  k : ℕ
  /-- rational with `R^B ≤ rB`. -/
  rB : ℚ
  /-- row constant `A`. -/
  Aq : ℚ
  deriving Repr

/-- Boolean check of one cell against a row curve: geometry side-conditions plus
the dyadic slab check `exp(ĉ·s) ≤ (Aq/(eps·rB))·s^k` on `[slo, shi]`. -/
def checkCellGen (P : CellParams) (c : Cell) : Bool :=
  if h : c.slo ≤ c.shi then
    decide (0 < c.eps) && decide (0 ≤ c.slo) && decide (0 < P.rB) &&
    decide (c.slo * c.slo ≤ (c.b : ℚ)) &&
    decide ((c.b' : ℚ) ≤ c.shi * c.shi) &&
    checkExprLeOnIntervalDyadic (expSplitC P.c64) (powRhs (P.Aq / (c.eps * P.rB)) P.k)
      ⟨c.slo, c.shi, h⟩ (-50) 8
  else false

set_option maxHeartbeats 1000000 in
/-- Transport: a checked cell dominates its table value by the row admissible
curve on the whole cell `[exp b, exp b']`.  The two transcendental constants are
supplied as rational over-estimates (`hCge`, `hrB`). -/
theorem cell_eps_le_admissible_gen
    (P : CellParams) (A B C R : ℝ)
    (hk : (P.k : ℝ) = 2 * B) (hB : 0 ≤ B) (hRpos : 0 < R) (hAnn : 0 ≤ A)
    (hAq : ((P.Aq : ℚ) : ℝ) = A)
    (hCge : C / Real.sqrt R ≤ ((P.c64 * 64 : ℚ) : ℝ))
    (hrB : R ^ B ≤ ((P.rB : ℚ) : ℝ))
    (c : Cell) (hc : checkCellGen P c = true) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      (c.eps : ℝ) ≤ admissible_bound A B C R x := by
  unfold checkCellGen at hc
  split at hc
  case isFalse => simp at hc
  case isTrue hle =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨heps, hslo0⟩, hrBpos⟩, hslo⟩, hshi⟩, hcheck⟩ := hc
    have hslab := verify_expr_le_on_interval_dyadic (expSplitC P.c64)
      (powRhs (P.Aq / (c.eps * P.rB)) P.k) ⟨c.slo, c.shi, hle⟩ (-50) 8
      (sub_supported _ _ _) (by norm_num) hcheck
    intro x hx
    obtain ⟨hx_lo, hx_hi⟩ := hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (exp_pos _) hx_lo
    have hb_le : (c.b : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx_lo
    have hb'_ge : Real.log x ≤ (c.b' : ℝ) := (Real.log_le_iff_le_exp hxpos).mpr hx_hi
    have hlog_nonneg : (0 : ℝ) ≤ Real.log x := le_trans (Nat.cast_nonneg _) hb_le
    set s : ℝ := Real.sqrt (Real.log x) with hs_def
    have h0lo : (0 : ℝ) ≤ (c.slo : ℝ) := by exact_mod_cast hslo0
    have h0hi : (0 : ℝ) ≤ (c.shi : ℝ) := by
      have : ((c.slo : ℚ) : ℝ) ≤ ((c.shi : ℚ) : ℝ) := by exact_mod_cast hle
      linarith
    have hs_lo : (c.slo : ℝ) ≤ s := by
      have h1 : ((c.slo : ℝ)) ^ 2 ≤ Real.log x := by
        have hq : ((c.slo : ℝ)) * ((c.slo : ℝ)) ≤ ((c.b : ℕ) : ℝ) := by exact_mod_cast hslo
        calc ((c.slo : ℝ)) ^ 2 = ((c.slo : ℝ)) * ((c.slo : ℝ)) := pow_two _
          _ ≤ ((c.b : ℕ) : ℝ) := hq
          _ ≤ Real.log x := hb_le
      calc (c.slo : ℝ) = Real.sqrt (((c.slo : ℝ)) ^ 2) := (Real.sqrt_sq h0lo).symm
        _ ≤ s := Real.sqrt_le_sqrt h1
    have hs_hi : s ≤ (c.shi : ℝ) := by
      have h1 : Real.log x ≤ ((c.shi : ℝ)) ^ 2 := by
        have hq : ((c.b' : ℕ) : ℝ) ≤ ((c.shi : ℝ)) * ((c.shi : ℝ)) := by exact_mod_cast hshi
        calc Real.log x ≤ ((c.b' : ℕ) : ℝ) := hb'_ge
          _ ≤ ((c.shi : ℝ)) * ((c.shi : ℝ)) := hq
          _ = ((c.shi : ℝ)) ^ 2 := (pow_two _).symm
      calc s ≤ Real.sqrt (((c.shi : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (c.shi : ℝ) := Real.sqrt_sq h0hi
    -- instantiate the slab inequality at s and rewrite evals
    have hineq := hslab s ⟨hs_lo, hs_hi⟩
    rw [eval_expSplitC, eval_powRhs] at hineq
    -- collapse (exp (c64·s))^64 = exp ((c64·64)·s)
    have hexp64 : exp ((P.c64 : ℝ) * s) ^ (64 : ℕ) = exp (((P.c64 * 64 : ℚ) : ℝ) * s) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hexp64] at hineq
    have heps_pos : (0 : ℝ) < (c.eps : ℝ) := by exact_mod_cast heps
    have hrBpos' : (0 : ℝ) < (P.rB : ℝ) := by exact_mod_cast hrBpos
    have hs_nonneg : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
    -- LHS: bound true exp by the checked (over-estimated) exp
    have hCs : C / Real.sqrt R * s ≤ ((P.c64 * 64 : ℚ) : ℝ) * s :=
      mul_le_mul_of_nonneg_right hCge hs_nonneg
    have hLHS : exp (C / Real.sqrt R * s) ≤ exp (((P.c64 * 64 : ℚ) : ℝ) * s) :=
      Real.exp_le_exp.mpr hCs
    -- RHS coefficient: q = Aq/(eps·rB) ≤ A/(eps·R^B)
    have hRBpos : (0 : ℝ) < R ^ B := Real.rpow_pos_of_pos hRpos _
    have hqle : ((P.Aq / (c.eps * P.rB) : ℚ) : ℝ) ≤ A / ((c.eps : ℝ) * R ^ B) := by
      rw [show ((P.Aq / (c.eps * P.rB) : ℚ) : ℝ) = A / ((c.eps : ℝ) * (P.rB : ℝ)) by
        push_cast [hAq]; ring]
      exact div_le_div_of_nonneg_left hAnn (mul_pos heps_pos hRBpos)
        (mul_le_mul_of_nonneg_left hrB heps_pos.le)
    -- chain: exp(C/√R·s) ≤ exp(ĉ·s) ≤ q·s^k ≤ (A/(eps·R^B))·s^k
    have hsk_nonneg : (0 : ℝ) ≤ s ^ P.k := pow_nonneg hs_nonneg _
    have hchain : exp (C / Real.sqrt R * s) ≤ (A / ((c.eps : ℝ) * R ^ B)) * s ^ P.k := by
      calc exp (C / Real.sqrt R * s)
          ≤ exp (((P.c64 * 64 : ℚ) : ℝ) * s) := hLHS
        _ ≤ ((P.Aq / (c.eps * P.rB) : ℚ) : ℝ) * s ^ P.k := hineq
        _ ≤ (A / ((c.eps : ℝ) * R ^ B)) * s ^ P.k :=
            mul_le_mul_of_nonneg_right hqle hsk_nonneg
    -- multiply by eps, divide by exp, identify the curve
    have hexp_pos : (0 : ℝ) < exp (C / Real.sqrt R * s) := exp_pos _
    have h2 : (c.eps : ℝ) * exp (C / Real.sqrt R * s) ≤ (A / R ^ B) * s ^ P.k := by
      have := mul_le_mul_of_nonneg_left hchain heps_pos.le
      calc (c.eps : ℝ) * exp (C / Real.sqrt R * s)
          ≤ (c.eps : ℝ) * ((A / ((c.eps : ℝ) * R ^ B)) * s ^ P.k) := this
        _ = (A / R ^ B) * s ^ P.k := by field_simp
    have key : (c.eps : ℝ) ≤ (A / R ^ B) * s ^ P.k * exp (-(C / Real.sqrt R * s)) := by
      have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt (inv_pos.mpr hexp_pos))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hexp_pos), mul_one] at h4
      rw [Real.exp_neg]; exact h4
    -- curve identity: admissible_bound A B C R x = (A/R^B)·s^k·exp(−(C/√R)·s)
    have hs_rpow : s = Real.log x ^ ((1 : ℝ) / 2) := by rw [hs_def, Real.sqrt_eq_rpow]
    have hsqrtR : Real.sqrt R = R ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow R
    have hRnn : (0 : ℝ) ≤ R := hRpos.le
    have hpowk : Real.log x ^ B = s ^ P.k := by
      rw [hs_rpow, ← Real.rpow_natCast (Real.log x ^ ((1 : ℝ) / 2)) P.k,
        ← Real.rpow_mul hlog_nonneg]
      rw [show (1 : ℝ) / 2 * (P.k : ℝ) = B by rw [hk]; ring]
    have hcurve : admissible_bound A B C R x
        = (A / R ^ B) * s ^ P.k * exp (-(C / Real.sqrt R * s)) := by
      unfold admissible_bound
      have e1 : (Real.log x / R) ^ B = s ^ P.k / R ^ B := by
        rw [Real.div_rpow hlog_nonneg hRnn, hpowk]
      have e2 : (Real.log x / R) ^ ((1 : ℝ) / 2) = s / Real.sqrt R := by
        rw [Real.div_rpow hlog_nonneg hRnn, ← hs_rpow, hsqrtR]
      rw [e1, e2]
      rw [show C / Real.sqrt R * s = C * (s / Real.sqrt R) by ring]
      ring
    rw [hcurve]
    exact key

/-- A checked cell with its trusted row bound gives the row admissible-curve
bound for `Eπ` on the cell. -/
theorem cell_Epi_le_admissible_gen
    (P : CellParams) (A B C R : ℝ)
    (hk : (P.k : ℝ) = 2 * B) (hB : 0 ≤ B) (hRpos : 0 < R) (hAnn : 0 ≤ A)
    (hAq : ((P.Aq : ℚ) : ℝ) = A)
    (hCge : C / Real.sqrt R ≤ ((P.c64 * 64 : ℚ) : ℝ))
    (hrB : R ^ B ≤ ((P.rB : ℚ) : ℝ))
    (c : Cell) (hc : checkCellGen P c = true)
    (hrow : Eπ.bound (c.eps : ℝ) (exp (c.b : ℝ))) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      Eπ x ≤ admissible_bound A B C R x := by
  intro x hx
  exact le_trans (hrow x hx.1)
    (cell_eps_le_admissible_gen P A B C R hk hB hRpos hAnn hAq hCge hrB c hc x hx)

end Table4Ext
end FKS2
