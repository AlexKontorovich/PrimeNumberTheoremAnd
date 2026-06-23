import PrimeNumberTheoremAnd.IEANTN.FKS2Floor.Cor22Floor
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtGenCore

/-!
# FKS2 Corollary 23 — per-row proofs

Corollary 23 asserts, for each row `(A,B,C,x₀)` of Table 6, the admissible
classical bound `Eπ.classicalBound A B C 5.5666305 (exp x₀)`.  Each row is
proven by the same three-segment decomposition used for Corollary 22:

* **floor** `[exp x₀, e^10]` — tight small-`x` `Eπ` via Buthe (`theorem_2e/2f`);
* **mid** `[e^10, e^20000]` — the numerical envelope `allCells` transported to
  the row curve by `cell_Epi_le_admissible_gen` (this file's generalized dyadic
  cell transport);
* **tail/loose** `[e^20000, ∞)` — domination by the (looser) Corollary 22 curve,
  or `theorem_3` from `corollary_14` for the rows that stay sharp.

**Template row = row 5** `(A=2.22, B=3/2, C=3/2, x₀=3)`: its curve clears the
envelope on every cell with a ≥46× margin, so the mid is the cleanest.

This file lives downstream of `Cor22Floor` (floor θ-engine) and `Table4ExtGenCore`
(transport); `corollary_23` itself cannot be proven inside `FKS2.lean`, which is
upstream of both — exactly as `corollary_22` lives in `Cor22Floor.lean`.
-/

namespace FKS2
open Real Table4Ext

/-! ## Row 5 (`A=2.22, B=3/2, C=3/2`, threshold `exp 3`) -/

/-- Row-5 cell-check parameters: `k = 2B = 3`, `ĉ = 0.6358 ≥ C/√R = 0.635763`
(so `c64 = ĉ/64`), `rB = 13.1338 ≥ R^{3/2} = 13.133745`, `Aq = A = 2.22`. -/
def P5 : CellParams := ⟨3179/320000, 3, 131338/10000, 222/100⟩

set_option maxHeartbeats 1000000 in
/-- Every extended-Table-4 cell passes the row-5 dyadic check (verified by the
dyadic interval kernel over all 13590 cells). -/
theorem allCells_checked_row5 : allCells.all (fun c => checkCellGen P5 c) = true := by
  native_decide

/-- Row-5 mid-range: `Eπ ≤` the row-5 admissible curve on `[e^10, e^20000]`,
via the envelope `allCells_trusted` transported by `cell_Epi_le_admissible_gen`. -/
theorem mid_row5 : ∀ x ∈ Set.Icc (exp (10:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  intro x hx
  have hx_lo : exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  have hck : checkCellGen P5 c = true := List.all_eq_true.mp allCells_checked_row5 c hcmem
  have hsqrtR_lb : (2.359370:ℝ) ≤ Real.sqrt 5.5666305 := by
    rw [show (2.359370:ℝ) = Real.sqrt (2.359370^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtR_ub : Real.sqrt 5.5666305 ≤ (2.359379:ℝ) := by
    rw [show (2.359379:ℝ) = Real.sqrt (2.359379^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine cell_Epi_le_admissible_gen P5 2.22 1.5 1.5 5.5666305
    (by norm_num [P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [P5])
    ?_ ?_ c hck (allCells_trusted c hcmem) x hcx
  · -- hCge : 1.5 / √R ≤ (P5.c64 * 64 : ℝ) = 0.6358
    have hrhs : (((P5.c64 * 64 : ℚ)):ℝ) = 3179/5000 := by norm_num [P5]
    rw [hrhs, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [hsqrtR_lb]
  · -- hrB : R^{1.5} ≤ (P5.rB : ℝ) = 13.1338
    have hrhs : (((P5.rB : ℚ)):ℝ) = 131338/10000 := by norm_num [P5]
    rw [hrhs]
    have hpow : (5.5666305:ℝ) ^ (1.5:ℝ) = 5.5666305 * Real.sqrt 5.5666305 := by
      rw [show (1.5:ℝ) = 1 + 1/2 by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 5.5666305), Real.rpow_one]
      simp [Real.sqrt_eq_rpow]
    rw [hpow]; nlinarith [hsqrtR_ub, Real.sqrt_nonneg (5.5666305:ℝ)]

/-- Row-5 floor `[exp 3, e^10]`: tight small-`x` `Eπ` bound via Buthe. **WIP.** -/
theorem floor_row5 : ∀ x ∈ Set.Icc (exp (3:ℝ)) (exp (10:ℝ)),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  sorry

/-- Row-5 tail `[e^20000, ∞)`: domination by the Corollary 22 curve. **WIP.** -/
theorem tail_row5 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 2.22 1.5 1.5 5.5666305 x := by
  sorry

/-- **Corollary 23, row 5** `(A=2.22, B=3/2, C=3/2, x₀=3)`. -/
theorem corollary_23_row5 : Eπ.classicalBound 2.22 1.5 1.5 5.5666305 (exp 3) := by
  intro x hx
  by_cases h10 : x ≤ exp 10
  · exact floor_row5 x ⟨hx, h10⟩
  · push_neg at h10
    by_cases h20k : x ≤ exp 20000
    · exact mid_row5 x ⟨le_of_lt h10, h20k⟩
    · push_neg at h20k
      exact tail_row5 x (le_of_lt h20k)

end FKS2
