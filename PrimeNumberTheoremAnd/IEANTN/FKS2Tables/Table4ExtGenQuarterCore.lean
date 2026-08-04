import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtGenCore

/-!
# Quarter (`B = 1/4`) extended-Table-4 cell transport (FKS2 Corollary 23, rows 1/2)

`Table4ExtGenCore` transports the `allCells` envelope to row curves with **integer**
`2B`.  Rows 1/2 of Table 6 have `B = 1/4`, so `2B = 1/2` is not an integer and the
curve carries a half-power `s^{1/2} = √s` (`s = √(log x)`), which the dyadic kernel
cannot enclose tightly (its `Real.sqrt` is bounded only by `[0, max(hi,1)]`).

Fix: keep the kernel on **integer powers of `s`** by checking the **square** of the
target.  `eps ≤ (A/R^{1/4})·√s·exp(−(C/√R)·s)` ⟺ `exp((C/√R)·s) ≤ (A/(eps·R^{1/4}))·√s`,
whose square is `exp(2(C/√R)·s) ≤ (A²/(eps²·√R))·s` — an `exp(linear) ≤ const·s¹`
check (`checkCellGenQuarter`), identical in shape to the integer `k=1` case.  The
square root is taken **outside** the kernel (`Real.sqrt` monotonicity) to recover
the half-power curve.  Cell geometry/intervals are reused (still in `s`, rational).
-/

namespace FKS2
namespace Table4Ext
open Real LeanCert.Core LeanCert.ANT.Asymp

/-- Cell check for a `B = 1/4` row: the SQUARED dyadic check `exp(ĉ_sq·s) ≤
(Aq²/(eps²·rB))·s` (integer power `s¹`, rational interval — the square of the
true `exp(C/√R·s) ≤ (Aq/(eps·R^{1/4}))·√s`). -/
def checkCellGenQuarter (P : CellParams) (c : Cell) : Bool :=
  if h : c.slo ≤ c.shi then
    decide (0 < c.eps) && decide (0 ≤ c.slo) && decide (0 < P.rB) &&
    decide (c.slo * c.slo ≤ (c.b : ℚ)) &&
    decide ((c.b' : ℚ) ≤ c.shi * c.shi) &&
    checkExprLeOnIntervalDyadic (expSplitC P.c64)
      (powRhs (P.Aq * P.Aq / (c.eps * c.eps * P.rB)) 1)
      ⟨c.slo, c.shi, h⟩ (-50) 8
  else false

set_option maxHeartbeats 1000000 in
/-- Transport for a `B = 1/4` row via the squared check.  `hCge` carries the
DOUBLED rate `2·(C/√R)`, `hrB` carries `√R = R^{1/2} ≤ rB`.  Recovers the
half-power curve by taking square roots outside the kernel. -/
theorem cell_eps_le_admissible_quarter
    (P : CellParams) (A C R : ℝ)
    (hRpos : 0 < R) (hApos : 0 < A)
    (hAq : ((P.Aq : ℚ) : ℝ) = A)
    (hCge : 2 * (C / Real.sqrt R) ≤ ((P.c64 * 64 : ℚ) : ℝ))
    (hrB : Real.sqrt R ≤ ((P.rB : ℚ) : ℝ))
    (c : Cell) (hc : checkCellGenQuarter P c = true) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      (c.eps : ℝ) ≤ admissible_bound A 0.25 C R x := by
  unfold checkCellGenQuarter at hc
  split at hc
  case isFalse => simp at hc
  case isTrue hle =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨heps, hslo0⟩, hrBpos⟩, hslo⟩, hshi⟩, hcheck⟩ := hc
    have hslab := verify_expr_le_on_interval_dyadic (expSplitC P.c64)
      (powRhs (P.Aq * P.Aq / (c.eps * c.eps * P.rB)) 1) ⟨c.slo, c.shi, hle⟩ (-50) 8
      (by norm_num) hcheck
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
    have hineq := hslab s ⟨hs_lo, hs_hi⟩
    rw [eval_expSplitC, eval_powRhs] at hineq
    have hexp64 : exp ((P.c64 : ℝ) * s) ^ (64 : ℕ) = exp (((P.c64 * 64 : ℚ) : ℝ) * s) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hexp64] at hineq
    have heps_pos : (0 : ℝ) < (c.eps : ℝ) := by exact_mod_cast heps
    have hrBpos' : (0 : ℝ) < (P.rB : ℝ) := by exact_mod_cast hrBpos
    have hs_nonneg : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
    have hsqrtR_pos : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos.mpr hRpos
    -- pow 1 simplification
    rw [pow_one] at hineq
    -- LHS: exp(2(C/√R)·s) ≤ exp((c64·64)·s)
    have hCs : 2 * (C / Real.sqrt R) * s ≤ ((P.c64 * 64 : ℚ) : ℝ) * s :=
      mul_le_mul_of_nonneg_right hCge hs_nonneg
    have hLHS : exp (2 * (C / Real.sqrt R) * s) ≤ exp (((P.c64 * 64 : ℚ) : ℝ) * s) :=
      Real.exp_le_exp.mpr hCs
    -- RHS coefficient: Aq²/(eps²·rB) ≤ A²/(eps²·√R)
    have hqle : ((P.Aq * P.Aq / (c.eps * c.eps * P.rB) : ℚ) : ℝ)
        ≤ A * A / ((c.eps : ℝ) * (c.eps : ℝ) * Real.sqrt R) := by
      rw [show ((P.Aq * P.Aq / (c.eps * c.eps * P.rB) : ℚ) : ℝ)
            = A * A / ((c.eps : ℝ) * (c.eps : ℝ) * (P.rB : ℝ)) by push_cast [hAq]; ring]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hrB (by positivity)
    -- squared chain: exp(2(C/√R)s) ≤ (A²/(eps²·√R))·s
    have hsq_chain : exp (2 * (C / Real.sqrt R) * s)
        ≤ (A * A / ((c.eps : ℝ) * (c.eps : ℝ) * Real.sqrt R)) * s := by
      calc exp (2 * (C / Real.sqrt R) * s)
          ≤ exp (((P.c64 * 64 : ℚ) : ℝ) * s) := hLHS
        _ ≤ ((P.Aq * P.Aq / (c.eps * c.eps * P.rB) : ℚ) : ℝ) * s := hineq
        _ ≤ (A * A / ((c.eps : ℝ) * (c.eps : ℝ) * Real.sqrt R)) * s :=
            mul_le_mul_of_nonneg_right hqle hs_nonneg
    -- take square roots: exp((C/√R)s) ≤ (A/(eps·R^{1/4}))·√s
    have hRq_pos : (0:ℝ) < R ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hRpos _
    have hR14sq : (R ^ ((1:ℝ)/4)) ^ 2 = Real.sqrt R := by
      rw [← Real.rpow_natCast (R ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hRpos.le,
        Real.sqrt_eq_rpow]; norm_num
    have hsqrt_step : exp (C / Real.sqrt R * s)
        ≤ (A / ((c.eps : ℝ) * R ^ ((1:ℝ)/4))) * Real.sqrt s := by
      have hlhs_sq : Real.sqrt (exp (2 * (C / Real.sqrt R) * s)) = exp (C / Real.sqrt R * s) := by
        rw [show 2 * (C / Real.sqrt R) * s = (C / Real.sqrt R * s) + (C / Real.sqrt R * s) by ring,
          Real.exp_add, Real.sqrt_mul_self (exp_nonneg _)]
      have hZnn : (0:ℝ) ≤ A * A / ((c.eps : ℝ) * (c.eps : ℝ) * Real.sqrt R) := by positivity
      have hmono := Real.sqrt_le_sqrt hsq_chain
      rw [hlhs_sq, Real.sqrt_mul hZnn] at hmono
      have hsqrtZ : Real.sqrt (A * A / ((c.eps : ℝ) * (c.eps : ℝ) * Real.sqrt R))
          = A / ((c.eps : ℝ) * R ^ ((1:ℝ)/4)) := by
        rw [show A * A / ((c.eps : ℝ) * (c.eps : ℝ) * Real.sqrt R)
              = (A / ((c.eps : ℝ) * R ^ ((1:ℝ)/4))) ^ 2 by
            rw [div_pow, mul_pow, hR14sq]; ring]
        exact Real.sqrt_sq (by positivity)
      rw [hsqrtZ] at hmono
      exact hmono
    -- curve identity for B = 1/4: admissible = (A/R^{1/4})·√s·exp(−(C/√R)·s)
    have hs_rpow : s = Real.log x ^ ((1:ℝ)/2) := by rw [hs_def, Real.sqrt_eq_rpow]
    have hsqrts : Real.sqrt s = Real.log x ^ ((1:ℝ)/4) := by
      rw [hs_def, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hlog_nonneg]; norm_num
    have hcurve : admissible_bound A 0.25 C R x
        = (A / R ^ ((1:ℝ)/4)) * Real.sqrt s * exp (-(C / Real.sqrt R * s)) := by
      unfold admissible_bound
      have e1 : (Real.log x / R) ^ (0.25:ℝ) = Real.sqrt s / R ^ ((1:ℝ)/4) := by
        rw [show (0.25:ℝ) = (1:ℝ)/4 by norm_num, Real.div_rpow hlog_nonneg hRpos.le, ← hsqrts]
      have e2 : (Real.log x / R) ^ ((1:ℝ)/2) = s / Real.sqrt R := by
        rw [Real.div_rpow hlog_nonneg hRpos.le, Real.sqrt_eq_rpow R, ← hs_rpow]
      rw [e1, e2, show -C * (s / Real.sqrt R) = -(C / Real.sqrt R * s) by ring]
      ring
    -- assemble: eps ≤ (A/R^{1/4})·√s·exp(−(C/√R)s)
    rw [hcurve, Real.exp_neg]
    have hstep2 : (c.eps : ℝ) * exp (C / Real.sqrt R * s) ≤ (A / R ^ ((1:ℝ)/4)) * Real.sqrt s := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt_step heps_pos.le
      calc (c.eps : ℝ) * exp (C / Real.sqrt R * s)
          ≤ (c.eps : ℝ) * ((A / ((c.eps : ℝ) * R ^ ((1:ℝ)/4))) * Real.sqrt s) := hmul
        _ = (A / R ^ ((1:ℝ)/4)) * Real.sqrt s := by field_simp
    have hexp_pos : (0:ℝ) < exp (C / Real.sqrt R * s) := exp_pos _
    have h4 := mul_le_mul_of_nonneg_right hstep2 (le_of_lt (inv_pos.mpr hexp_pos))
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hexp_pos), mul_one] at h4
    exact h4

/-- `Eπ` version: a checked `B=1/4` cell with its trusted row bound gives the
admissible-curve bound for `Eπ` on the cell. -/
theorem cell_Epi_le_admissible_quarter
    (P : CellParams) (A C R : ℝ)
    (hRpos : 0 < R) (hApos : 0 < A)
    (hAq : ((P.Aq : ℚ) : ℝ) = A)
    (hCge : 2 * (C / Real.sqrt R) ≤ ((P.c64 * 64 : ℚ) : ℝ))
    (hrB : Real.sqrt R ≤ ((P.rB : ℚ) : ℝ))
    (c : Cell) (hc : checkCellGenQuarter P c = true)
    (hrow : Eπ.bound (c.eps : ℝ) (exp (c.b : ℝ))) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      Eπ x ≤ admissible_bound A 0.25 C R x := by
  intro x hx
  exact le_trans (hrow x hx.1)
    (cell_eps_le_admissible_quarter P A C R hRpos hApos hAq hCge hrB c hc x hx)

end Table4Ext
end FKS2
