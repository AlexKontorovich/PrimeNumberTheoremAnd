import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23

/-!
# FKS2 Corollary 23 — row 7 `(A=38.8, B=3/2, C=1.95, x₀=1)`

Fourth fully-assembled row, structurally identical to row 6 (`B = 3/2`, `x₀ = 1`):
shared `tail_three_halves_of` tail and `FloorButhe.floor_buthe_of_curve` floor,
with row-7 cell params `P7`, floor curve `rhsE7`, and two `native_decide` checks.
Trusted floor boundary `[e^1, e^5]` (FKS2 §5.2/5.3), as row 6.
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Row-7 cell-check parameters: `k = 2B = 3`, `ĉ = 0.8266 ≥ C/√R = 1.95/√R`
(so `c64 = 4133/320000`), `rB = 13.1338 ≥ R^{3/2}`, `Aq = A = 38.8`. -/
def P7 : CellParams := ⟨4133/320000, 3, 131338/10000, 388/10⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-7 dyadic check. -/
theorem allCells_checked_row7 : allCells.all (fun c => checkCellGen P7 c) = true := by
  native_decide

/-- Row-7 mid-range `[e^10, e^20000]` via the `allCells` envelope transported by
`cell_Epi_le_admissible_gen` (`k = 3`). -/
theorem mid_row7 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 38.8 1.5 1.95 5.5666305 x :=
  mid_of P7 38.8 1.5 1.95 (by norm_num [P7]) (by norm_num) (by norm_num) (by norm_num [P7])
    (by have hrhs : (((P7.c64 * 64 : ℚ)):ℝ) = 4133/5000 := by norm_num [P7]
        rw [hrhs, div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have hrhs : (((P7.rB : ℚ)):ℝ) = 131338/10000 := by norm_num [P7]
        rw [hrhs, R5_rpow_three_halves_eq]; nlinarith [sqrtR5_ub, Real.sqrt_nonneg (5.5666305:ℝ)])
    allCells_checked_row7

/-- Row-7 tail `[e^20000, ∞)` via the generic `B=3/2` Cor-22 domination
(`rateUB = 0.8266 ≥ 1.95/√R`, `coeffLB = 2.954 ≤ 38.8/R^{3/2}`, gap `0.021`). -/
theorem tail_row7 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 38.8 1.5 1.95 5.5666305 x :=
  tail_three_halves_of 38.8 1.95 0.8266 2.954
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have h2 := R5_rpow_three_halves_le
        have h3 := R5_rpow_three_halves_pos
        have h1 : (2.954:ℝ) ≤ 38.8 / 13.1338 := by norm_num
        have h4 : (38.8:ℝ) / 13.1338 ≤ 38.8 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by norm_num)
    (by have hb : Real.exp 2 ≤ Real.exp ((0.8476 - 0.8266) * 141) := by
          apply Real.exp_le_exp.mpr; norm_num
        have h7 : (7:ℝ) ≤ Real.exp 2 := by
          have he : Real.exp 2 = (Real.exp 1) ^ (2:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
          rw [he]; calc (7:ℝ) ≤ (2.7182818283:ℝ)^(2:ℕ) := by norm_num
            _ ≤ (Real.exp 1)^(2:ℕ) := by gcongr; exact Real.exp_one_gt_d9.le
        nlinarith [hb, h7])

/-! ## Row-7 floor `[e^5, e^10]` via the shared Buthe slab machinery -/
namespace FloorButhe7

/-- Row-7 dyadic exp atom `exp(−(4133/40000)·s)`; `pow8` gives rate
`8266/10000 = 0.8266 ≥ 1.95/√R`. -/
def eR7 : Expr := Expr.exp (Expr.mul (Expr.const (-4133/40000)) (Expr.var 0))

/-- Row-7 floor curve `(2954/1000)·s³·exp(−(8266/10000)·s)`. -/
def rhsE7 : Expr :=
  Expr.mul (Expr.const (2954/1000)) (Expr.mul FloorButhe.s3 (FloorButhe.pow8 eR7))

theorem eval_rhsE7 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE7
      = (2954/1000) * (s*s*s) * Real.exp (-(8266/10000) * s) := by
  have h8 : Real.exp (s * (-4133/40000 : ℝ)) ^ 8 = Real.exp (s * (-4133/5000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  simp only [rhsE7, eR7, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s3, FloorButhe.s2,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support7 : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rhsE7) := by
  simp only [Expr.sub, FloorButhe.lhsE, rhsE7, eR7, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s3, FloorButhe.s4, FloorButhe.e2]
  repeat constructor

theorem slabs_checked7 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE rhsE7 FloorButhe.slabs (-50) 6 = true := by
  native_decide

theorem rhsE7_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE7
      ≤ admissible_bound 38.8 1.5 1.95 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE7]
  exact rowcurve_dom_three_halves 38.8 1.95 (2954/1000) (8266/10000) x hLnn
    (by have h2 := R5_rpow_three_halves_le; have h3 := R5_rpow_three_halves_pos
        have h1 : (2954/1000:ℝ) ≤ 38.8 / 13.1338 := by norm_num
        have h4 : (38.8:ℝ) / 13.1338 ≤ 38.8 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]) (by norm_num)

/-- Row-7 floor segment `[e^5, e^10]` via the shared `floor_buthe_of_curve`. -/
theorem floor_buthe7 : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 38.8 1.5 1.95 5.5666305 x :=
  FloorButhe.floor_buthe_of_curve rhsE7 38.8 1.5 1.95 support7 slabs_checked7 rhsE7_le_rowcurve

end FloorButhe7

/-- Row-7 floor `[exp 1, e^10]`, split at `e^5`: Buthe on `[e^5,e^10]`; the trusted
numerical boundary `[e^1, e^5]` (`x ∈ [2.72, 148]`, FKS2 §5.2/5.3). -/
theorem floor_row7 : ∀ x ∈ Set.Icc (exp (1:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 38.8 1.5 1.95 5.5666305 x := by
  intro x hx
  obtain ⟨h1, h10⟩ := hx
  by_cases h5 : Real.exp 5 ≤ x
  · exact FloorButhe7.floor_buthe7 x ⟨h5, h10⟩
  · sorry

/-- **Corollary 23, row 7** `(A=38.8, B=3/2, C=1.95, x₀=1)`. -/
theorem corollary_23_row7 : Eπ.classicalBound 38.8 1.5 1.95 5.5666305 (exp 1) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row7 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row7 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row7 x (le_of_lt h20k)

end FKS2
