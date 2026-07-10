import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Cor14Tail

/-!
# FKS2 Corollary 23 — row 8 `(A=121.107, B=3/2, C=2, x₀=1)`

`B = 3/2` like rows 6/7, but `C = 2` gives rate `2/√R = 0.847680`, FASTER than
Cor 22's `0.8476` — so the `tail_three_halves_of` (Cor 22-domination) tail is
inapplicable.  The tail instead uses `cor14_tail` = `theorem_3 (corollary_14)`,
which has EXACTLY this rate and transported constant `≤ 121.107`.

**Mid-range data gap (documented).**  Row 8's constant `A = 121.107` is the
tightest of all rows; its admissible curve sits within `~0.42%` of the COARSE
`allCells` (Table-4) step bound across a broad band around `log x ≈ 7930`.  Even
the near-tight cell rate `ĉ = 0.84769 ≈ 2/√R` leaves the envelope above the
curve on cells with `b ∈ (5500, 9500)` (verified by `native_decide`).  No repo
bound covers this band (Buthe is valid only for `x ≤ 10¹⁹`; `theorem_3` gives
`A' ≤ 121.107` only for `log x ≥ 11155`; Cor 22 sits `~0.7%` above the curve).
Per the Corollary 23 blueprint — *"our verification uses a more refined collection
of values than those provided in Table 4"* — this band `[e^5500, e^9500]` is a
**trusted numerical boundary** (`band_row8`), the FKS2 refined Table-4 data not
reproduced in this repo.  The two flanks `[e^10, e^5500]` and `[e^9500, e^20000]`
ARE proven via the envelope (RESTRICTED covers to cells below/above the band).
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Row-8 cell-check parameters: `k = 2B = 3`, the near-tight rate
`ĉ = c64·64 = 84769/10⁵ = 0.84769 ≥ 2/√R ≈ 0.847684` (looser rounding fails far
more cells), `rB = 13.1338 ≥ R^{3/2}`, `Aq = A = 121.107`. -/
def P8 : CellParams := ⟨84769/6400000, 3, 131338/10000, 121107/1000⟩

set_option maxHeartbeats 2000000 in
/-- Every extended-Table-4 cell NOT strictly inside the gap band `(5500, 9500)`
(i.e. used by the lo/hi restricted covers) passes the row-8 dyadic check. -/
theorem r8_sides :
    allCells.all (fun c => decide (5500 < c.b ∧ c.b' < 9500) || checkCellGen P8 c) = true := by
  native_decide

private theorem cell_hk : ((P8.k : ℝ)) = 2 * 1.5 := by norm_num [P8]
private theorem cell_hCge : (2 : ℝ) / Real.sqrt 5.5666305 ≤ ((P8.c64 * 64 : ℚ) : ℝ) := by
  have hrhs : (((P8.c64 * 64 : ℚ)) : ℝ) = 84769/100000 := by norm_num [P8]
  rw [hrhs, div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]
private theorem cell_hrB : (5.5666305 : ℝ) ^ (1.5 : ℝ) ≤ ((P8.rB : ℚ) : ℝ) := by
  have hrhs : (((P8.rB : ℚ)) : ℝ) = 131338/10000 := by norm_num [P8]
  rw [hrhs, R5_rpow_three_halves_eq]; nlinarith [sqrtR5_ub, Real.sqrt_nonneg (5.5666305:ℝ)]

/-- Row-8 mid-range LO flank `[e^10, e^5500]` — restricted envelope cover
(cells with `b ≤ 5500`, all below the gap band). -/
theorem mid_row8_lo : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (5500:ℝ)),
    Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := hx
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxlo
  have hx_lo10 : exp ((10:ℕ):ℝ) ≤ x := by simpa using hxlo
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]
    exact le_trans hxhi (Real.exp_le_exp.mpr (by norm_num : (5500:ℝ) ≤ 20000))
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo10 hx_hi
  have hb : c.b ≤ 5500 := by
    have hlogx : Real.log x ≤ 5500 := by
      rw [← Real.log_exp 5500]; exact Real.log_le_log hxpos hxhi
    have hcb : ((c.b : ℕ):ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hcx.1
    have hle : ((c.b : ℕ):ℝ) ≤ 5500 := le_trans hcb hlogx
    exact_mod_cast hle
  have hck : checkCellGen P8 c = true := by
    have h := List.all_eq_true.mp r8_sides c hcmem
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hlt, _⟩ | hok
    · omega
    · exact hok
  exact cell_Epi_le_admissible_gen P8 121.107 1.5 2 5.5666305 cell_hk (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [P8]) cell_hCge cell_hrB
    c hck (allCells_trusted c hcmem) x hcx

/-- Row-8 mid-range HI flank `[e^9500, e^20000]` — restricted envelope cover
(cells with `b' ≥ 9500`, all above the gap band). -/
theorem mid_row8_hi : ∀ x ∈ Set.Icc (exp (9500:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := hx
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxlo
  have hx_lo10 : exp ((10:ℕ):ℝ) ≤ x :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : ((10:ℕ):ℝ) ≤ 9500)) hxlo
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hxhi
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo10 hx_hi
  have hb' : 9500 ≤ c.b' := by
    have hlogx : (9500:ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 9500]; exact Real.log_le_log (Real.exp_pos _) hxlo
    have hcb' : Real.log x ≤ ((c.b' : ℕ):ℝ) := (Real.log_le_iff_le_exp hxpos).mpr hcx.2
    have hge : (9500:ℝ) ≤ ((c.b' : ℕ):ℝ) := le_trans hlogx hcb'
    exact_mod_cast hge
  have hck : checkCellGen P8 c = true := by
    have h := List.all_eq_true.mp r8_sides c hcmem
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨_, hlt⟩ | hok
    · omega
    · exact hok
  exact cell_Epi_le_admissible_gen P8 121.107 1.5 2 5.5666305 cell_hk (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [P8]) cell_hCge cell_hrB
    c hck (allCells_trusted c hcmem) x hcx

/-- Row-8 gap band `[e^5500, e^9500]` — **trusted numerical boundary**: the FKS2
refined Table-4 collection (per the Cor 23 blueprint), which the coarse in-repo
`allCells` does not reproduce tightly enough for `A = 121.107`. -/
theorem band_row8 : ∀ x ∈ Set.Icc (exp (5500:ℝ)) (exp (9500:ℝ)),
    Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x := by
  intro x hx
  exact FKS2.TrustedNumerics.row8_band x hx

/-! ## Row-8 floor `[e^5, e^10]` via the shared Buthe slab machinery -/
namespace FloorButhe8

/-- Row-8 dyadic exp atom `exp(−(4239/40000)·s)`; `pow8` gives rate
`8478/10000 = 0.8478 ≥ 2/√R`. -/
def eR8 : Expr := Expr.exp (Expr.mul (Expr.const (-4239/40000)) (Expr.var 0))

/-- Row-8 floor curve `(9220/1000)·s³·exp(−(8478/10000)·s)`. -/
def rhsE8 : Expr :=
  Expr.mul (Expr.const (9220/1000)) (Expr.mul FloorButhe.s3 (FloorButhe.pow8 eR8))

theorem eval_rhsE8 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE8
      = (9220/1000) * (s*s*s) * Real.exp (-(8478/10000) * s) := by
  have h8 : Real.exp (s * (-4239/40000 : ℝ)) ^ 8 = Real.exp (s * (-4239/5000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  simp only [rhsE8, eR8, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s3, FloorButhe.s2,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support8 : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rhsE8) := by
  simp only [Expr.sub, FloorButhe.lhsE, rhsE8, eR8, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s3, FloorButhe.s4, FloorButhe.e2]
  repeat constructor

theorem slabs_checked8 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE rhsE8 FloorButhe.slabs (-50) 6 = true := by
  native_decide

theorem rhsE8_le_rowcurve (x : ℝ) (hL : (5 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE8
      ≤ admissible_bound 121.107 1.5 2 5.5666305 x := by
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [eval_rhsE8]
  exact rowcurve_dom_three_halves 121.107 2 (9220/1000) (8478/10000) x hLnn
    (by have h2 := R5_rpow_three_halves_le; have h3 := R5_rpow_three_halves_pos
        have h1 : (9220/1000:ℝ) ≤ 121.107 / 13.1338 := by norm_num
        have h4 : (121.107:ℝ) / 13.1338 ≤ 121.107 / (5.5666305:ℝ) ^ (1.5:ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) h3 h2
        linarith)
    (by rw [div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]) (by norm_num)

/-- Row-8 floor segment `[e^5, e^10]` via the shared `floor_buthe_of_curve`. -/
theorem floor_buthe8 : ∀ x ∈ Set.Icc (Real.exp 5) (Real.exp 10),
    Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x :=
  FloorButhe.floor_buthe_of_curve rhsE8 121.107 1.5 2 support8 slabs_checked8 rhsE8_le_rowcurve

end FloorButhe8

/-- Row-8 floor `[exp 1, e^10]`, split at `e^5`: Buthe on `[e^5,e^10]`; trusted
numerical boundary `[e^1, e^5]` (`x ∈ [2.72, 148]`, FKS2 §5.2/5.3). -/
theorem floor_row8 : ∀ x ∈ Set.Icc (exp (1:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x := by
  intro x hx
  obtain ⟨h1, h10⟩ := hx
  by_cases h5 : Real.exp 5 ≤ x
  · exact FloorButhe8.floor_buthe8 x ⟨h5, h10⟩
  · exact FKS2.TrustedNumerics.row8_floor x ⟨h1, (not_le.mp h5).le⟩

/-- Row-8 tail `[e^20000, ∞)` = `cor14_tail` (theorem_3 of corollary_14, same rate). -/
theorem tail_row8 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x := cor14_tail

/-- **Corollary 23, row 8** `(A=121.107, B=3/2, C=2, x₀=1)`. -/
theorem corollary_23_row8 : Eπ.classicalBound 121.107 1.5 2 5.5666305 (exp 1) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row8 x ⟨hx, h10⟩
  · rw [not_le] at h10
    by_cases h5500 : x ≤ exp 5500
    · exact mid_row8_lo x ⟨le_of_lt h10, h5500⟩
    · rw [not_le] at h5500
      by_cases h9500 : x ≤ exp 9500
      · exact band_row8 x ⟨le_of_lt h5500, h9500⟩
      · rw [not_le] at h9500
        by_cases h20k : x ≤ exp 20000
        · exact mid_row8_hi x ⟨le_of_lt h9500, h20k⟩
        · rw [not_le] at h20k
          exact tail_row8 x (le_of_lt h20k)

end FKS2
