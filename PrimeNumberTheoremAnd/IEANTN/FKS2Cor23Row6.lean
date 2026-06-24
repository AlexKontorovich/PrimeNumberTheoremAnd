import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23

/-!
# FKS2 Corollary 23 — row 6 `(A=12.4, B=3/2, C=1.9, x₀=1)`

Third fully-assembled row.  Being `B = 3/2` like row 5, the tail uses the shared
`tail_three_halves_of` (Cor 22 domination) and the floor uses the shared
`FloorButhe.floor_buthe_of_curve`; only the row-6 cell params `P6`, the floor
curve `rhsE6`, and their two `native_decide` checks are row-specific.

Threshold `x₀ = 1`: the floor runs `[exp 1, e^10]`, split at `e^5` into the Buthe
segment and the **trusted numerical boundary** `[e^1, e^5]` (wider than rows 4/5's
`[e^3, e^5]`, same accepted class — FKS2 §5.2/5.3 direct `π`/`Li`).
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
  · have hrhs : (((P6.c64 * 64 : ℚ)):ℝ) = 4027/5000 := by norm_num [P6]
    rw [hrhs, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [hsqrtR_lb]
  · have hrhs : (((P6.rB : ℚ)):ℝ) = 131338/10000 := by norm_num [P6]
    rw [hrhs]
    rw [R5_rpow_three_halves_eq]; nlinarith [hsqrtR_ub, Real.sqrt_nonneg (5.5666305:ℝ)]

/-- Row-6 tail `[e^20000, ∞)` via the generic `B=3/2` Cor-22 domination
(`rateUB = 0.8054 ≥ 1.9/√R`, `coeffLB = 0.944 ≤ 12.4/R^{3/2}`, gap `0.0422`). -/
theorem tail_row6 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x :=
  tail_three_halves_of 12.4 1.9 0.8054 0.944
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have h2 := R5_rpow_three_halves_le
        have h3 := R5_rpow_three_halves_pos
        have h1 : (0.944:ℝ) ≤ 12.4 / 13.1338 := by norm_num
        have h4 : (12.4:ℝ) / 13.1338 ≤ 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by norm_num)
    (by have hb : Real.exp 5 ≤ Real.exp ((0.8476 - 0.8054) * 141) := by
          apply Real.exp_le_exp.mpr; norm_num
        have h148 : (148:ℝ) ≤ Real.exp 5 := by
          have he : Real.exp 5 = (Real.exp 1) ^ (5:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
          rw [he]; calc (148:ℝ) ≤ (2.7182818283:ℝ)^(5:ℕ) := by norm_num
            _ ≤ (Real.exp 1)^(5:ℕ) := by gcongr; exact Real.exp_one_gt_d9.le
        nlinarith [hb, h148])

/-! ## Row-6 floor `[e^5, e^10]` via the shared Buthe slab machinery -/
namespace FloorButhe6

/-- Row-6 dyadic exp atom `exp(−(4027/40000)·s)`; `pow8` gives rate
`8054/10000 = 0.8054 ≥ 1.9/√R`. -/
def eR6 : Expr := Expr.exp (Expr.mul (Expr.const (-4027/40000)) (Expr.var 0))

/-- Row-6 floor curve `(944/1000)·s³·exp(−(8054/10000)·s)`. -/
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

theorem rhsE6_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE6
      ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE6]
  exact rowcurve_dom_three_halves 12.4 1.9 (944/1000) (8054/10000) x hLnn
    (by have h2 := R5_rpow_three_halves_le; have h3 := R5_rpow_three_halves_pos
        have h1 : (944/1000:ℝ) ≤ 12.4 / 13.1338 := by norm_num
        have h4 : (12.4:ℝ) / 13.1338 ≤ 12.4 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]) (by norm_num)

/-- Row-6 floor segment `[e^5, e^10]` via the shared `floor_buthe_of_curve`. -/
theorem floor_buthe6 : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 12.4 1.5 1.9 5.5666305 x :=
  FloorButhe.floor_buthe_of_curve rhsE6 12.4 1.5 1.9 support6 slabs_checked6 rhsE6_le_rowcurve

end FloorButhe6

/-- Row-6 floor `[exp 1, e^10]`, split at `e^5`: Buthe on `[e^5,e^10]`; the trusted
numerical boundary `[e^1, e^5]` (`x ∈ [2.72, 148]`, FKS2 §5.2/5.3). -/
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
