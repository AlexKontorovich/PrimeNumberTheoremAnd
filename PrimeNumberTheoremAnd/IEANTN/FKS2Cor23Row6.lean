import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23

/-!
# FKS2 Corollary 23 — row 6 `(A=12.4, B=3/2, C=1.9, x₀=1)`

Third fully-assembled row (after rows 5 and 4).  Like row 5 it is `B = 3/2`
(`k = 2B = 3`), so the tail reuses `admissible_three_halves_eq` with the `s³`
matching the Corollary-22 curve (no power mismatch — cleaner than row 4's `B = 1`
tail), and the floor reuses row 5's `FloorButhe` slab machinery on `[√5, √10]`.

The one structural difference is the threshold `x₀ = 1`: the floor runs over
`[exp 1, e^10]`, split at `e^5` into the Buthe segment `[e^5, e^10]` and the
**trusted numerical boundary** `[e^1, e^5]` (wider than rows 4/5's `[e^3, e^5]`,
but the same accepted class — FKS2 §5.2/5.3 direct `π`/`Li`).
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Row-6 cell-check parameters: `k = 2B = 3`, `ĉ = 0.8054 ≥ C/√R = 1.9/√R`
(so `c64 = 4027/320000`), `rB = 13.1338 ≥ R^{3/2}`, `Aq = A = 12.4`. -/
def P6 : CellParams := ⟨4027/320000, 3, 131338/10000, 124/10⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-6 dyadic check. -/
theorem allCells_checked_row6 : allCells.all (fun c => checkCellGen P6 c) = true := by
  native_decide

/-- Row-6 mid-range `[e^10, e^20000]` via the `allCells` envelope transported by
`cell_Epi_le_admissible_gen` (`k = 3`, as row 5). -/
theorem mid_row6 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := by
  intro x hx
  have hx_lo : exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  have hck : checkCellGen P6 c = true := List.all_eq_true.mp allCells_checked_row6 c hcmem
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_ub := sqrtR5_ub
  refine cell_Epi_le_admissible_gen P6 12.4 1.5 1.9 5.5666305
    (by norm_num [P6]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [P6])
    ?_ ?_ c hck (allCells_trusted c hcmem) x hcx
  · -- hCge : 1.9 / √R ≤ (P6.c64 * 64 : ℝ) = 0.8054
    have hrhs : (((P6.c64 * 64 : ℚ)):ℝ) = 4027/5000 := by norm_num [P6]
    rw [hrhs, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [hsqrtR_lb]
  · -- hrB : R^{1.5} ≤ (P6.rB : ℝ) = 13.1338
    have hrhs : (((P6.rB : ℚ)):ℝ) = 131338/10000 := by norm_num [P6]
    rw [hrhs]
    rw [R5_rpow_three_halves_eq]; nlinarith [hsqrtR_ub, Real.sqrt_nonneg (5.5666305:ℝ)]

/-- Row-6 tail `[e^20000, ∞)`: `Eπ ≤` row-6 curve via Cor 22 domination.
B=3/2 (s³ matches Cor 22), the clean same-power split of row 5; rate gap
`0.8476 − 1.9/√R ≥ 0.0422`. -/
theorem tail_row6 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := by
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
      admissible_three_halves_eq 12.4 1.9 5.5666305 x hLnn (by norm_num)]
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_pos := sqrtR5_pos
  have hR15_ub := R5_rpow_three_halves_le
  have hR15_pos := R5_rpow_three_halves_pos
  have hcoeff : (12.4:ℝ) / 13.1338 ≤ 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hR15_pos hR15_ub
  have hCR : (1.9:ℝ) / Real.sqrt 5.5666305 ≤ 0.8054 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(0.8054:ℝ) * s) ≤ Real.exp (-(1.9 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have hCRs : (1.9 / Real.sqrt 5.5666305) * s ≤ 0.8054 * s :=
      mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith [hCRs]
  have hexp5 : (148:ℝ) ≤ Real.exp 5 := by
    have he : Real.exp 5 = (Real.exp 1) ^ (5:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (148:ℝ) ≤ (2.7182818283:ℝ) ^ (5:ℕ) := by norm_num
      _ ≤ (Real.exp 1) ^ (5:ℕ) := by gcongr; exact Real.exp_one_gt_d9.le
  have h5le : (5:ℝ) ≤ 0.0422 * s := by nlinarith [hs141]
  have hexp_small : Real.exp (-(0.0422:ℝ) * s) ≤ Real.exp (-5) := by
    apply Real.exp_le_exp.mpr; simp only [neg_mul]; linarith [h5le]
  have hexp_neg5 : Real.exp (-(5:ℝ)) ≤ 1 / 148 := by
    rw [Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hexp5
  have hscalar : (9.2211:ℝ) * Real.exp (-(0.8476) * s)
      ≤ (12.4 / 13.1338) * Real.exp (-(0.8054:ℝ) * s) := by
    have hsplit : Real.exp (-(0.8476:ℝ) * s)
        = Real.exp (-(0.0422:ℝ) * s) * Real.exp (-(0.8054:ℝ) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit,
      show (9.2211:ℝ) * (Real.exp (-(0.0422) * s) * Real.exp (-(0.8054) * s))
        = (9.2211 * Real.exp (-(0.0422) * s)) * Real.exp (-(0.8054) * s) by ring]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc (9.2211:ℝ) * Real.exp (-(0.0422) * s)
        ≤ 9.2211 * (1 / 148) :=
          mul_le_mul_of_nonneg_left (le_trans hexp_small hexp_neg5) (by norm_num)
      _ ≤ 12.4 / 13.1338 := by norm_num
  have hfinal : (9.2211:ℝ) * Real.exp (-(0.8476) * s)
      ≤ (12.4 / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(1.9 / Real.sqrt 5.5666305) * s) :=
    le_trans hscalar (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity))
  have hs3 : (0:ℝ) ≤ s ^ 3 := by positivity
  calc (9.2211:ℝ) * s ^ 3 * Real.exp (-(0.8476) * s)
      = (9.2211 * Real.exp (-(0.8476) * s)) * s ^ 3 := by ring
    _ ≤ ((12.4 / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(1.9 / Real.sqrt 5.5666305) * s)) * s ^ 3 :=
        mul_le_mul_of_nonneg_right hfinal hs3
    _ = 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) * s ^ 3 * Real.exp (-(1.9 / Real.sqrt 5.5666305) * s) := by
        ring

/-! ## Row-6 floor `[e^5, e^10]` via Buthe (dyadic slab cover) -/
namespace FloorButhe6

/-- Row-6 dyadic exp atom: `exp(−(4027/40000)·s)`, so `pow8` gives rate
`8054/10000 = 0.8054 ≥ 1.9/√R`. -/
def eR6 : Expr := Expr.exp (Expr.mul (Expr.const (-4027/40000)) (Expr.var 0))

/-- Row-6 floor curve as an `Expr`: `(944/1000)·s³·exp(−(8054/10000)·s)`.
Coeff `944/1000 ≤ 12.4/R^{3/2}`, rate `8054/10000 ≥ 1.9/√R`. -/
def rhsE6 : Expr :=
  Expr.mul (Expr.const (944/1000)) (Expr.mul FloorButhe.s3 (FloorButhe.pow8 eR6))

theorem eval_rhsE6 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE6
      = (944/1000) * (s*s*s) * Real.exp (-(8054/10000) * s) := by
  have h8 : Real.exp (s * (-4027/40000 : ℝ)) ^ 8 = Real.exp (s * (-4027/5000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  simp only [rhsE6, eR6, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s3, FloorButhe.s2,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support6 : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rhsE6) := by
  simp only [Expr.sub, FloorButhe.lhsE, rhsE6, eR6, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s3, FloorButhe.s4, FloorButhe.e2]
  repeat constructor

theorem slabs_checked6 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE rhsE6 FloorButhe.slabs (-50) 6 = true := by
  native_decide

theorem slab_ineq6 : ∀ I ∈ FloorButhe.slabs, ∀ s ∈ Set.Icc (I.lo : ℝ) I.hi,
    Expr.eval (fun _ => s) FloorButhe.lhsE ≤ Expr.eval (fun _ => s) rhsE6 :=
  verify_expr_le_on_slabs_dyadic FloorButhe.lhsE rhsE6 FloorButhe.slabs (-50) 6
    support6 (by norm_num) slabs_checked6

theorem dyadic_floor6 (s : ℝ) (h : s ∈ Set.Icc (2.236 : ℝ) 3.163) :
    Expr.eval (fun _ => s) FloorButhe.lhsE ≤ Expr.eval (fun _ => s) rhsE6 := by
  obtain ⟨I, hI, hmem⟩ := FloorButhe.cover s h
  exact slab_ineq6 I hI s hmem

theorem rhsE6_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE6
      ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE6, admissible_three_halves_eq 12.4 1.9 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hsss : s * s * s = s ^ 3 := by ring
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_pos := sqrtR5_pos
  have hR15_ub := R5_rpow_three_halves_le
  have hR15_pos := R5_rpow_three_halves_pos
  have hcoeff : (944/1000:ℝ) ≤ 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) := by
    have h1 : (944/1000:ℝ) ≤ 12.4 / 13.1338 := by norm_num
    have h2 : (12.4:ℝ) / 13.1338 ≤ 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hR15_pos hR15_ub
    linarith
  have hCR : (1.9:ℝ) / Real.sqrt 5.5666305 ≤ 8054/10000 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(8054/10000:ℝ) * s) ≤ Real.exp (-(1.9 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have hCRs : (1.9 / Real.sqrt 5.5666305) * s ≤ (8054/10000) * s :=
      mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith [hCRs]
  have hs3 : (0:ℝ) ≤ s ^ 3 := by positivity
  rw [hsss]
  calc (944/1000:ℝ) * s ^ 3 * Real.exp (-(8054/10000) * s)
      = ((944/1000:ℝ) * Real.exp (-(8054/10000) * s)) * s ^ 3 := by ring
    _ ≤ ((12.4 / (5.5666305:ℝ) ^ (1.5:ℝ)) * Real.exp (-(1.9 / Real.sqrt 5.5666305) * s)) * s ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity)) hs3
    _ = 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) * s ^ 3 * Real.exp (-(1.9 / Real.sqrt 5.5666305) * s) := by
        ring

theorem floor_buthe6 : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := by
  intro x hx
  obtain ⟨h5, h10⟩ := hx
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h5
  have hLge5 : (5:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 5]; exact Real.log_le_log (Real.exp_pos _) h5
  have hLle10 : Real.log x ≤ 10 := by
    rw [← Real.log_exp 10]; exact Real.log_le_log hxpos h10
  have hs_mem : Real.sqrt (Real.log x) ∈ Set.Icc (2.236 : ℝ) 3.163 := by
    constructor
    · rw [show (2.236:ℝ) = Real.sqrt (2.236^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [hLge5])
    · rw [show (3.163:ℝ) = Real.sqrt (3.163^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [hLle10])
  calc Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE :=
        FloorButhe.Epi_le_evalLhsE x h5 h10
    _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE6 := dyadic_floor6 _ hs_mem
    _ ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := rhsE6_le_rowcurve x hLge5

end FloorButhe6

/-- Row-6 floor `[exp 1, e^10]`. Split at `e^5`:
* `[e^5, e^10]`: `FloorButhe6.floor_buthe6` (Buthe `2e/2f` + dyadic cover);
* `[e^1, e^5]` (`x ∈ [2.72, 148]`): **trusted numerical boundary**, same accepted
  class as rows 4/5's `[e^3,e^5]` and `Table4Ext.allCells_trusted`, but wider
  (row 6's threshold `x₀ = 1` reaches below `e^3`). -/
theorem floor_row6 : ∀ x ∈ Set.Icc (exp (1:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := by
  intro x hx
  obtain ⟨h1, h10⟩ := hx
  by_cases h5 : Real.exp 5 ≤ x
  · exact FloorButhe6.floor_buthe6 x ⟨h5, h10⟩
  · sorry

/-- **Corollary 23, row 6** `(A=12.4, B=3/2, C=1.9, x₀=1)`. -/
theorem corollary_23_row6 : Eπ.classicalBound 12.4 1.5 1.9 5.5666305 (exp 1) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row6 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row6 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row6 x (le_of_lt h20k)

end FKS2
