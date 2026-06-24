import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23

/-!
# FKS2 Corollary 23 — row 4 `(A=1.76, B=1, C=3/2, x₀=3)`

Validates the generalized dyadic transport `cell_eps_le_admissible_gen` on a
**different power** `k = 2B = 2` (row 5 exercises `k = 3`).  Row 4 shares row 5's
`C = 3/2` (hence the same `C/√R` enclosure, reusing `sqrtR5_lb`) and has `R^B =
R^1 = 5.5666305` *rational* (so `rB` is exact, no over-estimate needed).

Kept in its own file so its `native_decide` cell check does not slow row 5's
build.  Only the mid-range is proven here; the floor `[exp 3, e^10]` (shared
threshold with row 5: Buthe on `[e^5,e^10]` + the `[e^3,e^5]` trusted boundary)
and the tail `[e^20000, ∞)` (Corollary 22 domination, B=3/2 vs B=1) remain. -/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Row-4 cell-check parameters: `k = 2B = 2`, `ĉ = 0.6358 ≥ C/√R` (same `C=3/2`
as row 5, so `c64 = 3179/320000`), `rB = R = 11133261/2000000 = R^1` (exact),
`Aq = A = 1.76`. -/
def P4 : CellParams := ⟨3179/320000, 2, 11133261/2000000, 176/100⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-4 (`k=2`) dyadic check. -/
theorem allCells_checked_row4 : allCells.all (fun c => checkCellGen P4 c) = true := by
  native_decide

/-- Row-4 mid-range: `Eπ ≤` the row-4 admissible curve on `[e^10, e^20000]`,
via the `allCells` envelope transported by the generalized `k=2` cell lemma. -/
theorem mid_row4 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 1.76 1 1.5 5.5666305 x := by
  intro x hx
  have hx_lo : exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  have hck : checkCellGen P4 c = true := List.all_eq_true.mp allCells_checked_row4 c hcmem
  refine cell_Epi_le_admissible_gen P4 1.76 1 1.5 5.5666305
    (by norm_num [P4]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [P4])
    ?_ ?_ c hck (allCells_trusted c hcmem) x hcx
  · -- hCge : 1.5 / √R ≤ (P4.c64 * 64 : ℝ) = 0.6358
    have hrhs : (((P4.c64 * 64 : ℚ)):ℝ) = 3179/5000 := by norm_num [P4]
    rw [hrhs, div_le_iff₀ sqrtR5_pos]
    nlinarith [sqrtR5_lb]
  · -- hrB : R^(1:ℝ) ≤ (P4.rB : ℝ)   (equality, R^1 = R rational)
    rw [Real.rpow_one]; norm_num [P4]

/-- `admissible_bound A 1 C R x` in terms of `s = √(log x)`:
`= (A / R) · s² · exp(−(C/√R)·s)`.  The `B = 1` analogue of
`admissible_three_halves_eq`, used for the row-4 tail domination. -/
lemma admissible_one_eq (A C R x : ℝ) (hL : 0 ≤ Real.log x) (hR : 0 < R) :
    admissible_bound A 1 C R x
      = (A / R) * Real.sqrt (Real.log x) ^ 2
        * Real.exp (-(C / Real.sqrt R) * Real.sqrt (Real.log x)) := by
  unfold admissible_bound
  set s := Real.sqrt (Real.log x) with hs_def
  have hs : s = Real.log x ^ ((1:ℝ)/2) := by rw [hs_def, Real.sqrt_eq_rpow]
  have hssq : s ^ 2 = Real.log x := Real.sq_sqrt hL
  have e1 : (Real.log x / R) ^ (1:ℝ) = s ^ 2 / R := by
    rw [Real.rpow_one, ← hssq]
  have e2 : (Real.log x / R) ^ ((1:ℝ)/2) = s / Real.sqrt R := by
    rw [Real.div_rpow hL hR.le, ← hs, Real.sqrt_eq_rpow R]
  rw [e1, e2, show -C * (s / Real.sqrt R) = -(C / Real.sqrt R) * s by ring]
  ring

/-- Row-4 tail `[e^20000, ∞)`: `Eπ ≤` the row-4 curve, by domination of the
(faster-decaying) Corollary 22 curve.  Unlike row 5, the Cor 22 curve carries an
`s³` while the row-4 curve carries `s²`; the surplus `s` is absorbed into the
exponential gap `0.8476 − 1.5/√R ≥ 0.21183` via `s·e^{-0.1 s} ≤ 10·e^{-1}`. -/
theorem tail_row4 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 1.76 1 1.5 5.5666305 x := by
  intro x hx
  have he2 : (2:ℝ) ≤ Real.exp 20000 := by
    have := Real.add_one_le_exp (20000:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he2 hx
  have hcor := corollary_22 x hx2
  refine le_trans hcor ?_
  have hL : (20000:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20000]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [admissible_three_halves_eq 9.2211 0.8476 1 x hLnn (by norm_num),
      admissible_one_eq 1.76 1.5 5.5666305 x hLnn (by norm_num)]
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_pos := sqrtR5_pos
  -- rate bound: 1.5/√R ≤ 0.63577
  have hCR : (1.5:ℝ) / Real.sqrt 5.5666305 ≤ 0.63577 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  -- coefficient lower bound: 0.316 ≤ 1.76/R
  have hcoeff : (0.316:ℝ) ≤ 1.76 / (5.5666305:ℝ) := by
    rw [le_div_iff₀ (by norm_num)]; norm_num
  -- central scalar bound: 9.2211·s·e^{-0.21183 s} ≤ 0.316  (uses s ≥ 141)
  have hcentral : (9.2211:ℝ) * s * Real.exp (-(0.21183) * s) ≤ 0.316 := by
    have hsplit : Real.exp (-(0.21183:ℝ) * s)
        = Real.exp (-(0.1) * s) * Real.exp (-(0.11183) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpoly : s * Real.exp (-(0.1:ℝ) * s) ≤ 10 * Real.exp (-1) := by
      have hab : (0.1:ℝ) * s ≤ Real.exp (0.1 * s - 1) := by
        have := Real.add_one_le_exp (0.1 * s - 1); linarith
      have h := mul_le_mul_of_nonneg_right hab (Real.exp_nonneg (-(0.1 * s)))
      rw [← Real.exp_add] at h
      have he : (0.1 * s - 1) + -(0.1 * s) = -1 := by ring
      rw [he] at h
      have heq : (-(0.1:ℝ) * s) = -(0.1*s) := by ring
      rw [heq]
      nlinarith [h, Real.exp_nonneg (-(0.1*s))]
    have htail6 : Real.exp (-(0.11183:ℝ) * s) ≤ Real.exp (-6) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hs141]
    have hexp7 : (1000:ℝ) ≤ Real.exp 7 := by
      have h1 : (2.7:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have he : Real.exp 7 = Real.exp 1 ^ (7:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]
      calc (1000:ℝ) ≤ (2.7:ℝ)^(7:ℕ) := by norm_num
        _ ≤ Real.exp 1 ^ (7:ℕ) := by gcongr
    have hexpneg7 : Real.exp (-7) ≤ 1/1000 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hexp7
    rw [hsplit]
    have hstep : (9.2211:ℝ) * s * (Real.exp (-(0.1) * s) * Real.exp (-(0.11183) * s))
        ≤ 9.2211 * (10 * Real.exp (-1)) * Real.exp (-6) := by
      have h1 : (9.2211:ℝ) * s * (Real.exp (-(0.1)*s) * Real.exp (-(0.11183)*s))
          = 9.2211 * (s * Real.exp (-(0.1)*s)) * Real.exp (-(0.11183)*s) := by ring
      rw [h1]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpoly (by norm_num)
      · exact htail6
      · exact Real.exp_nonneg _
      · positivity
    refine le_trans hstep ?_
    have hcomb : (9.2211:ℝ) * (10 * Real.exp (-1)) * Real.exp (-6) = 92.211 * Real.exp (-7) := by
      rw [show (-7:ℝ) = -1 + -6 by ring, Real.exp_add]; ring
    rw [hcomb]
    nlinarith [hexpneg7, Real.exp_pos (-7:ℝ)]
  -- assemble: rewrite the exponential gap, factor s³ = s·s², dominate
  have hs2_nn : (0:ℝ) ≤ s ^ 2 := by positivity
  have hexp_gap : Real.exp (-(0.63577:ℝ) * s)
      ≤ Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have hCRs : (1.5 / Real.sqrt 5.5666305) * s ≤ 0.63577 * s :=
      mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith [hCRs]
  have hLHS : (9.2211:ℝ) * s ^ 3 * Real.exp (-(0.8476) * s)
      = (9.2211 * s * Real.exp (-(0.21183) * s)) * (s ^ 2 * Real.exp (-(0.63577) * s)) := by
    rw [show (-(0.8476:ℝ)) * s = (-(0.21183) * s) + (-(0.63577) * s) by ring, Real.exp_add]
    ring
  calc (9.2211:ℝ) * s ^ 3 * Real.exp (-(0.8476) * s)
      = (9.2211 * s * Real.exp (-(0.21183) * s)) * (s ^ 2 * Real.exp (-(0.63577) * s)) := hLHS
    _ ≤ 0.316 * (s ^ 2 * Real.exp (-(0.63577) * s)) := by
        apply mul_le_mul_of_nonneg_right hcentral
        positivity
    _ ≤ (1.76 / 5.5666305) * s ^ 2 * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
        have h1 : (0.316:ℝ) * (s ^ 2 * Real.exp (-(0.63577) * s))
            ≤ (1.76 / 5.5666305) * (s ^ 2 * Real.exp (-(0.63577) * s)) := by
          apply mul_le_mul_of_nonneg_right hcoeff
          positivity
        have h2 : (1.76 / 5.5666305 : ℝ) * (s ^ 2 * Real.exp (-(0.63577) * s))
            ≤ (1.76 / 5.5666305) * (s ^ 2 * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hexp_gap hs2_nn
        calc (0.316:ℝ) * (s ^ 2 * Real.exp (-(0.63577) * s))
            ≤ (1.76 / 5.5666305) * (s ^ 2 * Real.exp (-(0.63577) * s)) := h1
          _ ≤ (1.76 / 5.5666305) * (s ^ 2 * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) := h2
          _ = (1.76 / 5.5666305) * s ^ 2 * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by ring

/-! ## Row-4 floor `[e^5, e^10]` via Buthe (dyadic slab cover)

Reuses row 5's `FloorButhe` machinery wholesale — the Buthe `Eπ`-upper-bound
`FloorButhe.lhsE` (curve-independent), its evaluation `FloorButhe.eval_lhsE`, the
reconciliation `FloorButhe.Epi_le_evalLhsE`, and the slab cover `FloorButhe.slabs`
/ `FloorButhe.cover`.  Only the row-specific RHS curve `rhsE4` (`s²` and
coefficient `1.76/R`, vs row 5's `s³` and `2.22/R^{3/2}`) and its `native_decide`
slab check are new. -/
namespace FloorButhe4

/-- Row-4 floor curve as an `Expr` in `s = √(log x)`:
`(316/1000)·s²·exp(−(63577/100000)·s)`.  Coefficient `316/1000 ≤ 1.76/R` and the
rate matches row 5's (`C = 3/2` shared). -/
def rhsE4 : Expr :=
  Expr.mul (Expr.const (316/1000)) (Expr.mul FloorButhe.s2 (FloorButhe.pow8 FloorButhe.eR))

theorem eval_rhsE4 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE4
      = (316/1000) * (s*s) * Real.exp (-(63577/100000) * s) := by
  have h8 : Real.exp (s * (-63577/800000 : ℝ)) ^ 8 = Real.exp (s * (-63577/100000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [rhsE4, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s2, FloorButhe.eR,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support4 : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rhsE4) := by
  simp only [Expr.sub, FloorButhe.lhsE, rhsE4, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s4, FloorButhe.e2, FloorButhe.eR]
  repeat constructor

theorem slabs_checked4 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE rhsE4 FloorButhe.slabs (-50) 6 = true := by
  native_decide

theorem rhsE4_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE4
      ≤ admissible_bound 1.76 1 1.5 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE4, admissible_one_eq 1.76 1.5 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hss : s * s = s ^ 2 := by ring
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_pos := sqrtR5_pos
  have hcoeff : (316/1000:ℝ) ≤ 1.76 / (5.5666305:ℝ) := by
    rw [le_div_iff₀ (by norm_num)]; norm_num
  have hCR : (1.5:ℝ) / Real.sqrt 5.5666305 ≤ 63577/100000 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(63577/100000:ℝ) * s) ≤ Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have hCRs : (1.5 / Real.sqrt 5.5666305) * s ≤ (63577/100000) * s :=
      mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith [hCRs]
  have hs2 : (0:ℝ) ≤ s ^ 2 := by positivity
  rw [hss]
  calc (316/1000:ℝ) * s ^ 2 * Real.exp (-(63577/100000) * s)
      = ((316/1000:ℝ) * Real.exp (-(63577/100000) * s)) * s ^ 2 := by ring
    _ ≤ ((1.76 / 5.5666305) * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s)) * s ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity)) hs2
    _ = 1.76 / 5.5666305 * s ^ 2 * Real.exp (-(1.5 / Real.sqrt 5.5666305) * s) := by ring

/-- Row-4 floor segment `[e^5, e^10]` via the shared `floor_buthe_of_curve`. -/
theorem floor_buthe4 : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 1.76 1 1.5 5.5666305 x :=
  FloorButhe.floor_buthe_of_curve rhsE4 1.76 1 1.5 support4 slabs_checked4 rhsE4_le_rowcurve

end FloorButhe4

/-- Row-4 floor `[exp 3, e^10]`. Split at `e^5`:
* `[e^5, e^10]`: `FloorButhe4.floor_buthe4` (Buthe `2e/2f` + dyadic cover);
* `[e^3, e^5]` (`x ∈ [20, 148]`): **trusted numerical boundary**, same accepted
  class as `floor_row5`'s `[e^3,e^5]` and `Table4Ext.allCells_trusted`. -/
theorem floor_row4 : ∀ x ∈ Set.Icc (exp (3:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 1.76 1 1.5 5.5666305 x := by
  intro x hx
  obtain ⟨h3, h10⟩ := hx
  by_cases h5 : Real.exp 5 ≤ x
  · exact FloorButhe4.floor_buthe4 x ⟨h5, h10⟩
  · sorry

/-- **Corollary 23, row 4** `(A=1.76, B=1, C=3/2, x₀=3)`. -/
theorem corollary_23_row4 : Eπ.classicalBound 1.76 1 1.5 5.5666305 (exp 3) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row4 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row4 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row4 x (le_of_lt h20k)

end FKS2
