import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_00
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_01
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_02
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_03
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_04
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_05
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_06
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_07
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_08
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_09
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_10
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_11
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_12
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtData_13

/-!
# Extended Table 4: coverage of the Corollary 22 mid-range

Assembles the generated shards into the interpolation statement: on
`[exp 10, exp 20000]`, `Eπ` is bounded by the Corollary 22 curve, given the
trusted row data of the extended ancillary table
(arXiv 2206.12557, anc/PrimeCountingTables.pdf).
-/

namespace FKS2
namespace Table4Ext

open Real

set_option linter.style.nativeDecide false

/-- All generated cells, in grid order. -/
def allCells : List Cell :=
  cells_00 ++ cells_01 ++ cells_02 ++ cells_03 ++ cells_04 ++ cells_05 ++
  cells_06 ++ cells_07 ++ cells_08 ++ cells_09 ++ cells_10 ++ cells_11 ++
  cells_12 ++ cells_13

theorem allCells_checked : ∀ c ∈ allCells, checkCell c = true := by
  intro c hc
  simp only [allCells, List.mem_append] at hc
  rcases hc with
    ((((((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) |
      hc) | hc) | hc) | hc
  · exact List.all_eq_true.mp cells_00_checked c hc
  · exact List.all_eq_true.mp cells_01_checked c hc
  · exact List.all_eq_true.mp cells_02_checked c hc
  · exact List.all_eq_true.mp cells_03_checked c hc
  · exact List.all_eq_true.mp cells_04_checked c hc
  · exact List.all_eq_true.mp cells_05_checked c hc
  · exact List.all_eq_true.mp cells_06_checked c hc
  · exact List.all_eq_true.mp cells_07_checked c hc
  · exact List.all_eq_true.mp cells_08_checked c hc
  · exact List.all_eq_true.mp cells_09_checked c hc
  · exact List.all_eq_true.mp cells_10_checked c hc
  · exact List.all_eq_true.mp cells_11_checked c hc
  · exact List.all_eq_true.mp cells_12_checked c hc
  · exact List.all_eq_true.mp cells_13_checked c hc

/-- Contiguity check: consecutive cells share endpoints, starting at `lo`. -/
def chainOk : ℕ → List Cell → Bool
  | _, [] => true
  | lo, c :: rest => (c.b == lo) && chainOk c.b' rest

/-- Right endpoint of a chained cell list. -/
def lastB : ℕ → List Cell → ℕ
  | lo, [] => lo
  | _, c :: rest => lastB c.b' rest

/-- A nonempty chained cell list covers its full range: every point of
`[exp lo, exp (lastB lo cells)]` lies in some cell. -/
theorem cover_of_chainOk (cells : List Cell) (lo : ℕ) (hne : cells ≠ [])
    (hchain : chainOk lo cells = true) {x : ℝ}
    (hx_lo : exp (lo : ℝ) ≤ x) (hx_hi : x ≤ exp ((lastB lo cells : ℕ) : ℝ)) :
    ∃ c ∈ cells, x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)) := by
  induction cells generalizing lo with
  | nil => exact absurd rfl hne
  | cons c rest ih =>
      simp only [chainOk, Bool.and_eq_true, beq_iff_eq] at hchain
      obtain ⟨hb, hrest⟩ := hchain
      by_cases hsplit : x ≤ exp ((c.b' : ℕ) : ℝ)
      · refine ⟨c, List.mem_cons_self .., ?_, hsplit⟩
        rw [hb]
        exact hx_lo
      · rw [not_le] at hsplit
        have hx_lo' : exp ((c.b' : ℕ) : ℝ) ≤ x := le_of_lt hsplit
        have hx_hi' : x ≤ exp ((lastB c.b' rest : ℕ) : ℝ) := by
          simpa only [lastB] using hx_hi
        cases rest with
        | nil =>
            exfalso
            simp only [lastB] at hx_hi'
            exact absurd hx_hi' (not_le.mpr hsplit)
        | cons d rest' =>
            obtain ⟨e, he, hxe⟩ :=
              ih c.b' (by simp) hrest hx_lo' hx_hi'
            exact ⟨e, List.mem_cons_of_mem _ he, hxe⟩

/-- The generated grid is contiguous from `b = 10`... -/
theorem allCells_chain : chainOk 10 allCells = true := by native_decide

/-- ...and reaches `b = 20000`. -/
theorem allCells_last : lastB 10 allCells = 20000 := by native_decide

theorem allCells_ne_nil : allCells ≠ [] := by native_decide

/-- Trusted data: each extended-table row `(b, ε)` asserts the numerical
bound `Eπ x ≤ ε` for `x ≥ exp b`.

The values are the `ε_{π,num}(x₁)` entries of Table 4 of the extended
ancillary tables published with FKS2 (arXiv 2206.12557,
`anc/PrimeCountingTables.pdf`), computed there via Corollary 8; the
ancillary document notes the θ-subdivision used is finer than any printed
table. We use the extended tables rather than the abbreviated Table 4
printed in the paper: the printed grid fails the interpolation condition
on 43 of its 207 cells. -/
theorem allCells_trusted :
    ∀ c ∈ allCells, Eπ.bound (c.eps : ℝ) (exp (c.b : ℝ)) := by
  sorry

/-- The Corollary 22 mid-range: on `[exp 10, exp 20000]` the prime counting
error `Eπ` is bounded by the Corollary 22 admissible curve. The trusted
input is `allCells_trusted` (paper table data); everything else is
machine-checked: the cell inequalities by dyadic interval arithmetic
(`allCells_checked`), the grid contiguity by evaluation (`allCells_chain`,
`allCells_last`), and the transport to the curve by
`cell_Epi_le_admissible`. -/
theorem Epi_le_admissible_on_midrange {x : ℝ}
    (hx : x ∈ Set.Icc (exp (10 : ℝ)) (exp (20000 : ℝ))) :
    Eπ x ≤ admissible_bound (Aq : ℝ) (3 / 2) (Cq : ℝ) 1 x := by
  have hx_lo : exp ((10 : ℕ) : ℝ) ≤ x := by
    simpa using hx.1
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ) : ℝ) := by
    rw [allCells_last]
    simpa using hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo hx_hi
  exact cell_Epi_le_admissible c (allCells_checked c hcmem)
    (allCells_trusted c hcmem) x hcx

end Table4Ext
end FKS2
