import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23

/-!
# FKS2 Corollary 23 — row 3 `(A=1.41, B=1/2, C=3/2, x₀=2)`

Fifth assembled row, the first with `B = 1/2` (`k = 2B = 1`).  Two things differ
from the `B = 3/2` rows:

* the tail carries a **surplus `s²`** over the Corollary-22 `s³` (row-3 curve is
  `s¹`), absorbed via `s²·e^{-0.1 s} = (s·e^{-0.05 s})²` (bespoke `tail_row3`);
* the Buthe upper bound only clears the (small-`A`) row-3 curve from `log x ≳ 5.02`
  up, so the floor splits at **`e^6`** (not `e^5`): `[e^6, e^10]` via
  `floor_buthe_of_curve_gen` on the slab interval `[√6, √10]`, and `[e^2, e^6]`
  is the trusted numerical boundary.
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Row-3 cell-check parameters: `k = 2B = 1`, `ĉ = 0.6358 ≥ C/√R` (same `C=3/2`,
so `c64 = 3179/320000` as rows 4/5), `rB = 2.35938 ≥ R^{1/2} = √R`, `Aq = 1.41`. -/
def P3 : CellParams := ⟨3179/320000, 1, 235938/100000, 141/100⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-3 (`k=1`) dyadic check. -/
theorem allCells_checked_row3 : allCells.all (fun c => checkCellGen P3 c) = true := by
  native_decide

/-- Row-3 mid-range `[e^10, e^20000]` via the `allCells` envelope transported by
`cell_Epi_le_admissible_gen` at `k = 1`. -/
theorem mid_row3 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 1.41 0.5 1.5 5.5666305 x :=
  mid_of P3 1.41 0.5 1.5 (by norm_num [P3]) (by norm_num) (by norm_num) (by norm_num [P3])
    (by have hrhs : (((P3.c64 * 64 : ℚ)):ℝ) = 3179/5000 := by norm_num [P3]
        rw [hrhs, div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have hrhs : (((P3.rB : ℚ)):ℝ) = 235938/100000 := by norm_num [P3]
        rw [hrhs, show (0.5:ℝ) = 1/2 by norm_num, ← Real.sqrt_eq_rpow]; linarith [sqrtR5_ub])
    allCells_checked_row3

/-- Row-3 tail `[e^20000, ∞)`: Cor 22 domination, B=1/2.  Surplus `s²` over the
Cor 22 `s³` absorbed via `s²·e^{-0.1 s} = (s·e^{-0.05 s})² ≤ (20 e^{-1})²`. -/
theorem tail_row3 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 1.41 0.5 1.5 5.5666305 x := by
  intro x hx
  have he2 : (2:ℝ) ≤ Real.exp 20000 := by have := Real.add_one_le_exp (20000:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he2 hx
  have hcor := corollary_22 x hx2
  refine le_trans hcor ?_
  have hL : (20000:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20000]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [admissible_three_halves_eq 9.2211 0.8476 1 x hLnn (by norm_num),
      admissible_half_eq 1.41 1.5 5.5666305 x hLnn (by norm_num)]
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_ub := sqrtR5_ub
  have hsqrtR_pos := sqrtR5_pos
  have hCR : (1.5:ℝ) / Real.sqrt 5.5666305 ≤ 0.63577 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(0.63577:ℝ) * s) ≤ Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (1.5 / Real.sqrt 5.5666305) * s ≤ 0.63577 * s := mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith
  have hcoeffLB : (0.5976:ℝ) ≤ 1.41 / Real.sqrt 5.5666305 := by
    rw [le_div_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_ub]
  have hcentral : (9.2211:ℝ) * (s*s) * Real.exp (-(0.21183) * s) ≤ 0.5976 := by
    have hlin : s * Real.exp (-(0.05:ℝ) * s) ≤ 20 * Real.exp (-1) := by
      have hab : (0.05:ℝ) * s ≤ Real.exp (0.05 * s - 1) := by
        have := Real.add_one_le_exp (0.05 * s - 1); linarith
      have h := mul_le_mul_of_nonneg_right hab (Real.exp_nonneg (-(0.05 * s)))
      rw [← Real.exp_add] at h
      have he : (0.05 * s - 1) + -(0.05 * s) = -1 := by ring
      rw [he] at h
      have heq : (-(0.05:ℝ) * s) = -(0.05*s) := by ring
      rw [heq]; nlinarith [h, Real.exp_nonneg (-(0.05*s))]
    have hh2 : (Real.exp (-(0.05:ℝ) * s))^(2:ℕ) = Real.exp (-(0.1) * s) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsq : (s*s) * Real.exp (-(0.1:ℝ) * s) ≤ 400 * Real.exp (-2) := by
      have hfac : (s*s) * Real.exp (-(0.1:ℝ) * s) = (s * Real.exp (-(0.05) * s))^(2:ℕ) := by
        rw [mul_pow, hh2]; ring
      rw [hfac]
      have hnn : (0:ℝ) ≤ s * Real.exp (-(0.05) * s) := by positivity
      calc (s * Real.exp (-(0.05) * s))^(2:ℕ)
          ≤ (20 * Real.exp (-1))^(2:ℕ) := by apply pow_le_pow_left₀ hnn hlin
        _ = 400 * Real.exp (-2) := by
            rw [mul_pow, show ((20:ℝ))^(2:ℕ) = 400 by norm_num]
            congr 1
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsplit : Real.exp (-(0.21183:ℝ) * s)
        = Real.exp (-(0.1) * s) * Real.exp (-(0.11183) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have htail9 : Real.exp (-(0.11183:ℝ) * s) ≤ Real.exp (-9) := by
      apply Real.exp_le_exp.mpr; nlinarith [hs141]
    have hexp11 : (50000:ℝ) ≤ Real.exp 11 := by
      have he : Real.exp 11 = (Real.exp 1) ^ (11:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]
      calc (50000:ℝ) ≤ (2.7:ℝ)^(11:ℕ) := by norm_num
        _ ≤ (Real.exp 1)^(11:ℕ) := by gcongr; linarith [Real.exp_one_gt_d9]
    rw [hsplit, show (9.2211:ℝ) * (s*s) * (Real.exp (-(0.1)*s) * Real.exp (-(0.11183)*s))
        = 9.2211 * ((s*s) * Real.exp (-(0.1)*s)) * Real.exp (-(0.11183)*s) by ring]
    have hstep : (9.2211:ℝ) * ((s*s) * Real.exp (-(0.1)*s)) * Real.exp (-(0.11183)*s)
        ≤ 9.2211 * (400 * Real.exp (-2)) * Real.exp (-9) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      · exact htail9
      · exact Real.exp_nonneg _
      · positivity
    refine le_trans hstep ?_
    have hcomb : (9.2211:ℝ) * (400 * Real.exp (-2)) * Real.exp (-9) = 3688.44 * Real.exp (-11) := by
      rw [show (-11:ℝ) = -2 + -9 by ring, Real.exp_add]; ring
    rw [hcomb, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    nlinarith [hexp11]
  have hs3eq : s^3 = (s*s)*s := by ring
  have hLHS : (9.2211:ℝ) * s^3 * Real.exp (-(0.8476) * s)
      = (9.2211 * (s*s) * Real.exp (-(0.21183) * s)) * (s * Real.exp (-(0.63577) * s)) := by
    rw [hs3eq, show -(0.8476:ℝ)*s = -(0.21183)*s + -(0.63577)*s by ring, Real.exp_add]; ring
  have hfac_nn : (0:ℝ) ≤ s * Real.exp (-(0.63577) * s) := by positivity
  calc (9.2211:ℝ) * s^3 * Real.exp (-(0.8476) * s)
      = (9.2211 * (s*s) * Real.exp (-(0.21183) * s)) * (s * Real.exp (-(0.63577) * s)) := hLHS
    _ ≤ 0.5976 * (s * Real.exp (-(0.63577) * s)) := mul_le_mul_of_nonneg_right hcentral hfac_nn
    _ ≤ (1.41 / Real.sqrt 5.5666305) * s * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
        have h1 : (0.5976:ℝ) * (s * Real.exp (-(0.63577) * s))
            ≤ (1.41 / Real.sqrt 5.5666305) * (s * Real.exp (-(0.63577) * s)) :=
          mul_le_mul_of_nonneg_right hcoeffLB hfac_nn
        have h2 : (1.41 / Real.sqrt 5.5666305) * (s * Real.exp (-(0.63577) * s))
            ≤ (1.41 / Real.sqrt 5.5666305) * (s * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hexpRHS hs_nn
        calc (0.5976:ℝ) * (s * Real.exp (-(0.63577) * s))
            ≤ (1.41 / Real.sqrt 5.5666305) * (s * Real.exp (-(0.63577) * s)) := h1
          _ ≤ (1.41 / Real.sqrt 5.5666305) * (s * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) := h2
          _ = (1.41 / Real.sqrt 5.5666305) * s * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by ring

/-! ## Row-3 floor `[e^6, e^10]` via the generalized Buthe slab cover `[√6,√10]` -/
namespace FloorButhe3

/-- Row-3 floor curve `(5976/10000)·s·exp(−(63577/100000)·s)`.  Coeff
`5976/10000 ≤ 1.41/√R`; rate reuses `FloorButhe.eR` (`= 1.5/√R` shared `C=3/2`). -/
def rhsE3 : Expr :=
  Expr.mul (Expr.const (5976/10000)) (Expr.mul (Expr.var 0) (FloorButhe.pow8 FloorButhe.eR))

theorem eval_rhsE3 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE3
      = (5976/10000) * s * Real.exp (-(63577/100000) * s) := by
  have h8 : Real.exp (s * (-63577/800000 : ℝ)) ^ 8 = Real.exp (s * (-63577/100000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [rhsE3, FloorButhe.eR, FloorButhe.pow8, FloorButhe.sqx,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support3 : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rhsE3) := by
  simp only [Expr.sub, FloorButhe.lhsE, rhsE3, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s4, FloorButhe.e2, FloorButhe.eR]
  repeat constructor

theorem slabs_checked3 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE rhsE3 (slabsFrom (2449/1000) 15) (-50) 6 = true := by
  native_decide

theorem rhsE3_le_rowcurve (x : ℝ) (hL : (6 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE3
      ≤ admissible_bound 1.41 0.5 1.5 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE3, admissible_half_eq 1.41 1.5 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_ub := sqrtR5_ub
  have hsqrtR_pos := sqrtR5_pos
  have hcoeff : (5976/10000:ℝ) ≤ 1.41 / Real.sqrt 5.5666305 := by
    rw [le_div_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_ub]
  have hCR : (1.5:ℝ) / Real.sqrt 5.5666305 ≤ 63577/100000 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(63577/100000:ℝ) * s) ≤ Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (1.5 / Real.sqrt 5.5666305) * s ≤ (63577/100000) * s := mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith
  calc (5976/10000:ℝ) * s * Real.exp (-(63577/100000) * s)
      = ((5976/10000:ℝ) * Real.exp (-(63577/100000) * s)) * s := by ring
    _ ≤ ((1.41 / Real.sqrt 5.5666305) * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) * s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity)) hs_nn
    _ = 1.41 / Real.sqrt 5.5666305 * s * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by ring

/-- Row-3 floor segment `[e^6, e^10]` via `floor_buthe_of_curve_gen` on `[√6,√10]`. -/
theorem floor_buthe3 : ∀ x ∈ Set.Icc (Real.exp 6) (Real.exp 10),
    Eπ x ≤ admissible_bound 1.41 0.5 1.5 5.5666305 x :=
  floor_buthe_of_curve_gen rhsE3 1.41 0.5 1.5 6 (2449/1000) 15 (by norm_num)
    (by rw [show ((2449/1000:ℚ):ℝ) = 2.449 by norm_num,
          show (2.449:ℝ) = Real.sqrt (2.449^2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h317 : Real.sqrt 10 ≤ 3.17 := by
          rw [show (3.17:ℝ) = Real.sqrt (3.17^2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h317])
    support3 slabs_checked3 rhsE3_le_rowcurve

end FloorButhe3

/-- Row-3 floor `[exp 2, e^10]`, split at `e^6`: Buthe on `[e^6,e^10]`; the trusted
numerical boundary `[e^2, e^6]` (`x ∈ [7.39, 403]`, blueprint's "checks directly for
particularly small x", FKS2.lean:4640).  Wider than the `B=3/2` rows' `[·,e^5]`
because the small-`A` row-3 curve clears the Buthe bound only above `e^6`. -/
theorem floor_row3 : ∀ x ∈ Set.Icc (exp (2:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 1.41 0.5 1.5 5.5666305 x := by
  intro x hx
  obtain ⟨h2, h10⟩ := hx
  by_cases h6 : Real.exp 6 ≤ x
  · exact FloorButhe3.floor_buthe3 x ⟨h6, h10⟩
  · exact FKS2.TrustedNumerics.row3_floor x ⟨h2, (not_le.mp h6).le⟩

/-- **Corollary 23, row 3** `(A=1.41, B=1/2, C=3/2, x₀=2)`. -/
theorem corollary_23_row3 : Eπ.classicalBound 1.41 0.5 1.5 5.5666305 (exp 2) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row3 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row3 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row3 x (le_of_lt h20k)

end FKS2
