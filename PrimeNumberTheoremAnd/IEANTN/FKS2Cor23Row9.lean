import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Cor14Tail

/-!
# FKS2 Corollary 23 — row 9 `(A=6.60, B=2, C=2, x₀=3)`

Ninth and last row, the only `B = 2` row.  `C = 2` gives rate `2/√R = 0.847680`.
Hosts the `B = 2` analogues `admissible_two_eq` / `rowcurve_dom_two` (the `s⁴`
versions of the `B = 3/2` helpers).

The earlier scout claimed this row needs an `Eθ` `B = 2` source bound — that is
FALSE.  Because `row9` is `B = 2` (a `log²` power) its curve is LOOSER than a
`B = 3/2` curve at large `x`, so `cor14_tail` (a `B = 3/2`, `C = 2`, rate-matched
`Eπ` bound, `≤ 121.107·s³·…`) DOMINATES the `row9` curve `6.60·s⁴·…` for
`s = √(log x) ≥ 43.29` (i.e. `x ≥ e^1875`), hence on the whole tail `[e^20000, ∞)`.
Mid + floor are the usual envelope (`k = 4`) + Buthe.
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- `admissible_bound A 2 C R x` in terms of `s = √(log x)`:
`= (A/R²)·s⁴·exp(−(C/√R)·s)`.  The `B = 2` analogue of `admissible_three_halves_eq`. -/
lemma admissible_two_eq (A C R x : ℝ) (hL : 0 ≤ Real.log x) (hR : 0 < R) :
    admissible_bound A 2 C R x
      = (A / R ^ (2:ℝ)) * Real.sqrt (Real.log x) ^ 4
        * Real.exp (-(C / Real.sqrt R) * Real.sqrt (Real.log x)) := by
  unfold admissible_bound
  set s := Real.sqrt (Real.log x) with hs_def
  have hs : s = Real.log x ^ ((1:ℝ)/2) := by rw [hs_def, Real.sqrt_eq_rpow]
  have e1 : (Real.log x / R) ^ (2:ℝ) = s ^ 4 / R ^ (2:ℝ) := by
    rw [Real.div_rpow hL hR.le]
    congr 1
    rw [hs, ← Real.rpow_natCast (Real.log x ^ ((1:ℝ)/2)) 4, ← Real.rpow_mul hL]
    norm_num
  have e2 : (Real.log x / R) ^ ((1:ℝ)/2) = s / Real.sqrt R := by
    rw [Real.div_rpow hL hR.le, ← hs, Real.sqrt_eq_rpow R]
  rw [e1, e2, show -C * (s / Real.sqrt R) = -(C / Real.sqrt R) * s by ring]
  ring

/-- `R^{2} = 5.5666305²`. -/
lemma R5_rpow_two_eq : (5.5666305:ℝ) ^ (2:ℝ) = 30.98737512353025 := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num

lemma R5_rpow_two_pos : (0:ℝ) < (5.5666305:ℝ) ^ (2:ℝ) := by positivity

/-- Generic `B = 2` floor-curve domination: `coeff·s⁴·exp(−rate·s) ≤ rowcurve`
when `coeff ≤ A/R²` and `rate ≥ C/√R`.  `s⁴` analogue of `rowcurve_dom_three_halves`. -/
lemma rowcurve_dom_two (A C coeff rate : ℝ) (x : ℝ)
    (hL : (0:ℝ) ≤ Real.log x)
    (hcoeff : coeff ≤ A / (5.5666305:ℝ) ^ (2:ℝ))
    (hrate : C / Real.sqrt 5.5666305 ≤ rate)
    (hcoeffnn : 0 ≤ coeff) :
    coeff * (Real.sqrt (Real.log x) * Real.sqrt (Real.log x) * Real.sqrt (Real.log x)
        * Real.sqrt (Real.log x))
        * Real.exp (-rate * Real.sqrt (Real.log x))
      ≤ admissible_bound A 2 C 5.5666305 x := by
  rw [admissible_two_eq A C 5.5666305 x hL (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hsnn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hssss : s * s * s * s = s ^ 4 := by ring
  have hAnn : (0:ℝ) ≤ A / (5.5666305:ℝ) ^ (2:ℝ) := le_trans hcoeffnn hcoeff
  have hexpRHS : Real.exp (-rate * s) ≤ Real.exp (-(C / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hrate hsnn
    simp only [neg_mul]; linarith
  have hs4 : (0:ℝ) ≤ s ^ 4 := by positivity
  rw [hssss]
  calc coeff * s ^ 4 * Real.exp (-rate * s)
      = (coeff * Real.exp (-rate * s)) * s ^ 4 := by ring
    _ ≤ ((A / (5.5666305:ℝ) ^ (2:ℝ)) * Real.exp (-(C / Real.sqrt 5.5666305) * s)) * s ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) hAnn) hs4
    _ = A / (5.5666305:ℝ) ^ (2:ℝ) * s ^ 4 * Real.exp (-(C / Real.sqrt 5.5666305) * s) := by ring

/-- Row-9 cell-check parameters: `k = 2B = 4`, `ĉ = 0.8478 ≥ C/√R = 2/√R`
(so `c64 = 4239/320000`), `rB = 30.9874 ≥ R²`, `Aq = A = 6.60`. -/
def P9 : CellParams := ⟨4239/320000, 4, 309874/10000, 66/10⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-9 dyadic check. -/
theorem allCells_checked_row9 : allCells.all (fun c => checkCellGen P9 c) = true := by
  native_decide

/-- Row-9 mid-range `[e^10, e^20000]` via the `allCells` envelope (`k = 4`). -/
theorem mid_row9 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 6.60 2 2 5.5666305 x :=
  mid_of P9 6.60 2 2 (by norm_num [P9]) (by norm_num) (by norm_num) (by norm_num [P9])
    (by have hrhs : (((P9.c64 * 64 : ℚ)):ℝ) = 4239/5000 := by norm_num [P9]
        rw [hrhs, div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb])
    (by have hrhs : (((P9.rB : ℚ)):ℝ) = 309874/10000 := by norm_num [P9]
        rw [hrhs, R5_rpow_two_eq]; norm_num)
    allCells_checked_row9

/-! ## Row-9 floor `[e^5, e^10]` via the shared Buthe slab machinery -/
namespace FloorButhe9

/-- Row-9 dyadic exp atom `exp(−(4239/40000)·s)`; `pow8` gives rate `0.8478 ≥ 2/√R`. -/
def eR9 : Expr := Expr.exp (Expr.mul (Expr.const (-4239/40000)) (Expr.var 0))

/-- Row-9 floor curve `(2129/10000)·s⁴·exp(−(8478/10000)·s)`. -/
def rhsE9 : Expr :=
  Expr.mul (Expr.const (2129/10000)) (Expr.mul FloorButhe.s4 (FloorButhe.pow8 eR9))

theorem eval_rhsE9 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE9
      = (2129/10000) * (s*s*s*s) * Real.exp (-(8478/10000) * s) := by
  have h8 : Real.exp (s * (-4239/40000 : ℝ)) ^ 8 = Real.exp (s * (-4239/5000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  simp only [rhsE9, eR9, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s4, FloorButhe.s2,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support9 : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rhsE9) := by
  simp only [Expr.sub, FloorButhe.lhsE, rhsE9, eR9, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s3, FloorButhe.s4, FloorButhe.e2]
  repeat constructor

theorem slabs_checked9 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE rhsE9 FloorButhe.slabs (-50) 6 = true := by
  native_decide

theorem rhsE9_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE9
      ≤ admissible_bound 6.60 2 2 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE9]
  exact rowcurve_dom_two 6.60 2 (2129/10000) (8478/10000) x hLnn
    (by rw [R5_rpow_two_eq]; norm_num)
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]) (by norm_num)

/-- Row-9 floor segment `[e^5, e^10]` via the shared `floor_buthe_of_curve`. -/
theorem floor_buthe9 : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 6.60 2 2 5.5666305 x :=
  FloorButhe.floor_buthe_of_curve rhsE9 6.60 2 2 support9 slabs_checked9 rhsE9_le_rowcurve

end FloorButhe9

/-- Row-9 floor `[exp 3, e^10]`, split at `e^5`: Buthe on `[e^5,e^10]`; trusted
numerical boundary `[e^3, e^5]` (`x ∈ [20, 148]`, FKS2 §5.2/5.3). -/
theorem floor_row9 : ∀ x ∈ Set.Icc (exp (3:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 6.60 2 2 5.5666305 x := by
  intro x hx
  obtain ⟨h3, h10⟩ := hx
  by_cases h5 : Real.exp 5 ≤ x
  · exact FloorButhe9.floor_buthe9 x ⟨h5, h10⟩
  · exact FKS2.TrustedNumerics.row9_floor x ⟨h3, (not_le.mp h5).le⟩

/-- Row-9 tail `[e^20000, ∞)`: `cor14_tail` gives `Eπ ≤ admissible 121.107 (3/2) 2 R`
(a `B=3/2`, rate-`2/√R` curve), which DOMINATES the row-9 `B=2` curve here because
`L^{3/2} ≤ (6.60/121.107·R^{1/2})·L²` for `s = √L ≥ 43.29` (and `s ≥ 141` on this range). -/
theorem tail_row9 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 6.60 2 2 5.5666305 x := by
  intro x hx
  refine le_trans (cor14_tail x hx) ?_
  have hL : (20000:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20000]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [admissible_three_halves_eq 121.107 2 5.5666305 x hLnn (by norm_num),
      admissible_two_eq 6.60 2 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs
  have hsnn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hR15_lo : (13.133:ℝ) ≤ (5.5666305:ℝ) ^ (1.5:ℝ) := by
    rw [R5_rpow_three_halves_eq]; nlinarith [sqrtR5_lb, sqrtR5_pos]
  have hcoef : (121.107:ℝ) / (5.5666305:ℝ) ^ (1.5:ℝ)
      ≤ 6.60 / (5.5666305:ℝ) ^ (2:ℝ) * s := by
    have h1 : (121.107:ℝ) / (5.5666305:ℝ) ^ (1.5:ℝ) ≤ 121.107 / 13.133 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR15_lo
    have h2 : (121.107:ℝ) / 13.133 ≤ 6.60 / (5.5666305:ℝ) ^ (2:ℝ) * 141 := by
      rw [R5_rpow_two_eq]; norm_num
    have h3 : (6.60:ℝ) / (5.5666305:ℝ) ^ (2:ℝ) * 141 ≤ 6.60 / (5.5666305:ℝ) ^ (2:ℝ) * s :=
      mul_le_mul_of_nonneg_left hs141 (by positivity)
    linarith
  have hs3 : (0:ℝ) ≤ s ^ 3 := by positivity
  have key : (121.107:ℝ) / (5.5666305:ℝ) ^ (1.5:ℝ) * s ^ 3
      ≤ 6.60 / (5.5666305:ℝ) ^ (2:ℝ) * s ^ 4 := by
    have he : (6.60:ℝ) / (5.5666305:ℝ) ^ (2:ℝ) * s ^ 4
        = (6.60 / (5.5666305:ℝ) ^ (2:ℝ) * s) * s ^ 3 := by ring
    rw [he]; exact mul_le_mul_of_nonneg_right hcoef hs3
  exact mul_le_mul_of_nonneg_right key (Real.exp_nonneg _)

/-- **Corollary 23, row 9** `(A=6.60, B=2, C=2, x₀=3)`. -/
theorem corollary_23_row9 : Eπ.classicalBound 6.60 2 2 5.5666305 (exp 3) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row9 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row9 x ⟨le_of_lt h10, h20k⟩
    · rw [not_le] at h20k
      exact tail_row9 x (le_of_lt h20k)

end FKS2
