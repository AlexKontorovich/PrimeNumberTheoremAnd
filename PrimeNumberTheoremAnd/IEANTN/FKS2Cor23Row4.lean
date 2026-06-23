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

end FKS2
