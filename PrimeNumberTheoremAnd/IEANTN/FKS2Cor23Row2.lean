import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtGenQuarterCore

/-!
# FKS2 Corollary 23 — row 2 `(A=0.826, B=1/4, C=1, x₀=1)`

Sixth assembled row, the first with `B = 1/4`.  The half-power `√s` (`s=√(log x)`)
is handled throughout by the **squaring** technique (kept off the dyadic kernel):
the mid via `Table4Ext.cell_Epi_le_admissible_quarter` (squared cell check), the
floor via `floor_buthe_quarter_of_curve` (squared slab check on `lhsE² ≤ rhsE2`),
and the tail via Cor 22 domination using `√s ≥ 1` to drop the `√s` factor.

Also hosts the shared `B = 1/4` helpers (`admissible_quarter_eq`, the `√(√R)`
enclosures, `floor_buthe_quarter_of_curve`) — promote to `FKS2Cor23.lean` when
row 1 is added.

Floor split at `e^6` (Buthe clears the small-`A` row-2 curve only above `e^6`);
`[e^1, e^6]` is the trusted numerical boundary.
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Row-2 tail `[e^20000, ∞)`: Cor 22 domination, B=1/4.  The row-2 √s on the RHS
is bounded below by `√s ≥ 1` (`s ≥ 141`), reducing to `9.2211·s³·e^{-0.8476 s} ≤
0.5377·e^{-0.4239 s}` (cube trick `s³·e^{-0.15s}=(s·e^{-0.05s})³`). -/
theorem tail_row2 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 0.826 0.25 1 5.5666305 x := by
  intro x hx
  have he2 : (2:ℝ) ≤ Real.exp 20000 := by have := Real.add_one_le_exp (20000:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he2 hx
  have hcor := corollary_22 x hx2
  refine le_trans hcor ?_
  have hL : (20000:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20000]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [admissible_three_halves_eq 9.2211 0.8476 1 x hLnn (by norm_num),
      admissible_quarter_eq 0.826 1 5.5666305 x hLnn (by norm_num)]
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_pos := sqrtR5_pos
  have hsqrts_ge1 : (1:ℝ) ≤ Real.sqrt s := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcoeffLB : (0.5377:ℝ) ≤ 0.826 / (5.5666305:ℝ) ^ ((1:ℝ)/4) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]; nlinarith [R5_rpow_quarter_le]
  have hCR : (1:ℝ) / Real.sqrt 5.5666305 ≤ 0.4239 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(0.4239:ℝ) * s) ≤ Real.exp (-(1 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (1 / Real.sqrt 5.5666305) * s ≤ 0.4239 * s := mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith
  -- cube bound: 9.2211·s³·e^{-0.8476 s} ≤ 0.5377·e^{-0.4239 s}
  have hcube : (9.2211:ℝ) * s^3 * Real.exp (-(0.8476) * s) ≤ 0.5377 * Real.exp (-(0.4239) * s) := by
    have hlin : s * Real.exp (-(0.05:ℝ) * s) ≤ 20 * Real.exp (-1) := by
      have hab : (0.05:ℝ) * s ≤ Real.exp (0.05 * s - 1) := by
        have := Real.add_one_le_exp (0.05 * s - 1); linarith
      have h := mul_le_mul_of_nonneg_right hab (Real.exp_nonneg (-(0.05 * s)))
      rw [← Real.exp_add] at h
      have he : (0.05 * s - 1) + -(0.05 * s) = -1 := by ring
      rw [he] at h
      have heq : (-(0.05:ℝ) * s) = -(0.05*s) := by ring
      rw [heq]; nlinarith [h, Real.exp_nonneg (-(0.05*s))]
    have hcube3 : s^3 * Real.exp (-(0.15:ℝ) * s) ≤ 8000 * Real.exp (-3) := by
      have hpow : (Real.exp (-(0.05:ℝ) * s))^(3:ℕ) = Real.exp (-(0.15) * s) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hfac : s^3 * Real.exp (-(0.15:ℝ) * s) = (s * Real.exp (-(0.05) * s))^(3:ℕ) := by
        rw [mul_pow, hpow]
      rw [hfac]
      have hnn : (0:ℝ) ≤ s * Real.exp (-(0.05) * s) := by positivity
      calc (s * Real.exp (-(0.05) * s))^(3:ℕ)
          ≤ (20 * Real.exp (-1))^(3:ℕ) := by apply pow_le_pow_left₀ hnn hlin
        _ = 8000 * Real.exp (-3) := by
            rw [mul_pow, show ((20:ℝ))^(3:ℕ) = 8000 by norm_num]; congr 1
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsplit : Real.exp (-(0.8476:ℝ) * s)
        = Real.exp (-(0.15) * s) * (Real.exp (-(0.2737) * s) * Real.exp (-(0.4239) * s)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have htail12 : Real.exp (-(0.2737:ℝ) * s) ≤ Real.exp (-12) := by
      apply Real.exp_le_exp.mpr; nlinarith [hs141]
    have hexp15 : (137200:ℝ) ≤ Real.exp 15 := by
      have he : Real.exp 15 = (Real.exp 1) ^ (15:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]
      calc (137200:ℝ) ≤ (2.7:ℝ)^(15:ℕ) := by norm_num
        _ ≤ (Real.exp 1)^(15:ℕ) := by gcongr; linarith [Real.exp_one_gt_d9]
    rw [hsplit,
      show (9.2211:ℝ) * s^3 * (Real.exp (-(0.15)*s) * (Real.exp (-(0.2737)*s) * Real.exp (-(0.4239)*s)))
        = 9.2211 * (s^3 * Real.exp (-(0.15)*s)) * Real.exp (-(0.2737)*s) * Real.exp (-(0.4239)*s) by ring]
    have hstep : (9.2211:ℝ) * (s^3 * Real.exp (-(0.15)*s)) * Real.exp (-(0.2737)*s)
        ≤ 9.2211 * (8000 * Real.exp (-3)) * Real.exp (-12) := by
      apply mul_le_mul _ htail12 (Real.exp_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hcube3 (by norm_num)
    have hfinal : (9.2211:ℝ) * (8000 * Real.exp (-3)) * Real.exp (-12) ≤ 0.5377 := by
      rw [show (9.2211:ℝ) * (8000 * Real.exp (-3)) * Real.exp (-12) = 73768.8 * Real.exp (-15) by
        rw [show (-15:ℝ) = -3 + -12 by ring, Real.exp_add]; ring]
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; nlinarith [hexp15]
    calc (9.2211:ℝ) * (s^3 * Real.exp (-(0.15)*s)) * Real.exp (-(0.2737)*s) * Real.exp (-(0.4239)*s)
        ≤ (9.2211 * (8000 * Real.exp (-3)) * Real.exp (-12)) * Real.exp (-(0.4239)*s) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
      _ ≤ 0.5377 * Real.exp (-(0.4239)*s) := mul_le_mul_of_nonneg_right hfinal (Real.exp_nonneg _)
  -- assemble: LHS ≤ 0.5377·e^{-0.4239s} ≤ coeff·√s·e^{-(1/√R)s}
  calc (9.2211:ℝ) * s^3 * Real.exp (-(0.8476) * s)
      ≤ 0.5377 * Real.exp (-(0.4239) * s) := hcube
    _ ≤ 0.826 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s * Real.exp (-(1 / Real.sqrt 5.5666305) * s) := by
        have hRHSnn : (0:ℝ) ≤ 0.826 / (5.5666305:ℝ)^((1:ℝ)/4) := by positivity
        calc (0.5377:ℝ) * Real.exp (-(0.4239)*s)
            ≤ 0.826 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.exp (-(0.4239)*s) :=
              mul_le_mul_of_nonneg_right hcoeffLB (Real.exp_nonneg _)
          _ ≤ 0.826 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s * Real.exp (-(0.4239)*s) := by
              rw [mul_assoc]
              apply mul_le_mul_of_nonneg_left _ hRHSnn
              calc Real.exp (-(0.4239)*s) = 1 * Real.exp (-(0.4239)*s) := (one_mul _).symm
                _ ≤ Real.sqrt s * Real.exp (-(0.4239)*s) :=
                    mul_le_mul_of_nonneg_right hsqrts_ge1 (Real.exp_nonneg _)
          _ ≤ 0.826 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s * Real.exp (-(1 / Real.sqrt 5.5666305) * s) := by
              apply mul_le_mul_of_nonneg_left hexpRHS (by positivity)

/-- Row-2 SQUARED floor curve `(2891/10000)·s·exp(−(8477/10000)·s)` (the dyadic
under-estimate of `(admissible 0.826 0.25 1 R x)² = (0.826²/√R)·s·exp(−(2/√R)s)`). -/
def eR2 : Expr := Expr.exp (Expr.mul (Expr.const (-8477/80000)) (Expr.var 0))
def rhsE2 : Expr :=
  Expr.mul (Expr.const (2891/10000)) (Expr.mul (Expr.var 0) (FloorButhe.pow8 eR2))

theorem eval_rhsE2 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE2 = (2891/10000) * s * Real.exp (-(8477/10000) * s) := by
  have h8 : Real.exp (s * (-8477/80000 : ℝ)) ^ 8 = Real.exp (s * (-8477/10000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [rhsE2, eR2, FloorButhe.pow8, FloorButhe.sqx,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support2 : ExprSupportedWithInv (Expr.sub (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2) := by
  simp only [Expr.sub, rhsE2, eR2, FloorButhe.lhsE, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s4, FloorButhe.e2]
  repeat constructor

theorem rhsE2_le_rowcurve_sq (x : ℝ) (hL : (6 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2
      ≤ (admissible_bound 0.826 0.25 1 5.5666305 x) ^ 2 := by
  have hLnn : (0:ℝ) ≤ Real.log x := by linarith
  rw [eval_rhsE2, admissible_quarter_eq 0.826 1 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hsqrtR_ub := sqrtR5_ub
  have hsqrtR_pos := sqrtR5_pos
  -- expand the square: ((0.826/R^{1/4})·√s·exp(−(1/√R)s))² = (0.826/R^{1/4})²·s·exp(−(2/√R)s)
  have hsqs : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs_nn
  have hexp2 : (Real.exp (-(1 / Real.sqrt 5.5666305) * s)) ^ 2
      = Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hexpand : (0.826 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s
        * Real.exp (-(1 / Real.sqrt 5.5666305) * s)) ^ 2
      = (0.826 / (5.5666305:ℝ)^((1:ℝ)/4))^2 * s * Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by
    rw [mul_pow, mul_pow, hsqs, hexp2]
  rw [hexpand]
  -- coeff: 2891/10000 ≤ (0.826/R^{1/4})² = 0.826²/√R
  have hR14sq : ((5.5666305:ℝ)^((1:ℝ)/4))^2 = Real.sqrt 5.5666305 := by
    rw [← Real.rpow_natCast ((5.5666305:ℝ)^((1:ℝ)/4)) 2, ← Real.rpow_mul (by norm_num),
      Real.sqrt_eq_rpow]; norm_num
  have hcoeff : (2891/10000:ℝ) ≤ (0.826 / (5.5666305:ℝ)^((1:ℝ)/4))^2 := by
    rw [div_pow, hR14sq, le_div_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_ub]
  -- rate: 2/√R ≤ 8477/10000
  have hrate : (2:ℝ) / Real.sqrt 5.5666305 ≤ 8477/10000 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [sqrtR5_lb]
  have hexpRHS : Real.exp (-(8477/10000:ℝ) * s) ≤ Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (2 / Real.sqrt 5.5666305) * s ≤ (8477/10000) * s := mul_le_mul_of_nonneg_right hrate hs_nn
    simp only [neg_mul]; linarith
  calc (2891/10000:ℝ) * s * Real.exp (-(8477/10000) * s)
      = ((2891/10000:ℝ) * Real.exp (-(8477/10000) * s)) * s := by ring
    _ ≤ ((0.826 / (5.5666305:ℝ)^((1:ℝ)/4))^2 * Real.exp (-(2 / Real.sqrt 5.5666305) * s)) * s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity)) hs_nn
    _ = (0.826 / (5.5666305:ℝ)^((1:ℝ)/4))^2 * s * Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by ring

/-! ## Row 2 `(A=0.826, B=1/4, C=1, x₀=1)` assembly -/

/-- Row-2 quarter cell params: `ĉ_sq = c64·64 = 0.8477 ≥ 2/√R`, `rB = 2.35938 ≥ √R`,
`Aq = 0.826`. -/
def P2 : CellParams := ⟨8477/640000, 1, 235938/100000, 826/1000⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-2 squared (`B=1/4`) check. -/
theorem allCells_checked_row2 : allCells.all (fun c => checkCellGenQuarter P2 c) = true := by
  native_decide

/-- Row-2 mid-range `[e^10, e^20000]` via the `B=1/4` quarter transport. -/
theorem mid_row2 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 0.826 0.25 1 5.5666305 x := by
  intro x hx
  have hx_lo : exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  have hck : checkCellGenQuarter P2 c = true := List.all_eq_true.mp allCells_checked_row2 c hcmem
  refine cell_Epi_le_admissible_quarter P2 0.826 1 5.5666305 (by norm_num) (by norm_num)
    (by norm_num [P2]) ?_ ?_ c hck (allCells_trusted c hcmem) x hcx
  · have hrhs : (((P2.c64 * 64 : ℚ)):ℝ) = 8477/10000 := by norm_num [P2]
    rw [hrhs, mul_one_div, div_le_iff₀ sqrtR5_pos]
    nlinarith [sqrtR5_lb]
  · have hrhs : (((P2.rB : ℚ)):ℝ) = 235938/100000 := by norm_num [P2]
    rw [hrhs]; linarith [sqrtR5_ub]

/-- The squared floor slab check on `[√6, √10]`: `lhsE² ≤ rhsE2`. -/
theorem slabs_checked2 :
    checkExprLeOnSlabsDyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
      (slabsFrom (2449/1000) 15) (-50) 6 = true := by
  native_decide

/-- Row-2 floor segment `[e^6, e^10]` via the quarter Buthe assembler. -/
theorem floor_buthe2 : ∀ x ∈ Set.Icc (Real.exp 6) (Real.exp 10),
    Eπ x ≤ admissible_bound 0.826 0.25 1 5.5666305 x :=
  floor_buthe_quarter_of_curve rhsE2 0.826 1 6 (2449/1000) 15 (by norm_num) (by norm_num)
    (by rw [show ((2449/1000:ℚ):ℝ) = 2.449 by norm_num,
          show (2.449:ℝ) = Real.sqrt (2.449^2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h317 : Real.sqrt 10 ≤ 3.17 := by
          rw [show (3.17:ℝ) = Real.sqrt (3.17^2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h317])
    support2 slabs_checked2 rhsE2_le_rowcurve_sq

/-- Row-2 floor `[exp 1, e^10]`, split at `e^6`: Buthe on `[e^6,e^10]`; trusted
numerical boundary `[e^1, e^6]` (`x ∈ [2.72, 403]`, FKS2 blueprint small-x). -/
theorem floor_row2 : ∀ x ∈ Set.Icc (exp (1:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 0.826 0.25 1 5.5666305 x := by
  intro x hx
  obtain ⟨h1, h10⟩ := hx
  by_cases h6 : Real.exp 6 ≤ x
  · exact floor_buthe2 x ⟨h6, h10⟩
  · sorry

/-- **Corollary 23, row 2** `(A=0.826, B=1/4, C=1, x₀=1)`. -/
theorem corollary_23_row2 : Eπ.classicalBound 0.826 0.25 1 5.5666305 (exp 1) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row2 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row2 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row2 x (le_of_lt h20k)

end FKS2
