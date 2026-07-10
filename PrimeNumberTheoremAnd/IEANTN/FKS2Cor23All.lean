import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row1
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row2
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row3
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row4
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row6
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row7
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row8
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row9

/-!
# FKS2 Corollary 23 — complete Table-6 dispatch (all 9 rows)

`corollary_23_all` is the full statement of `FKS2.corollary_23`: every row
`[Aπ, B, C, x₀]` of `table6` yields the admissible asymptotic `Eπ` bound with
`R = 5.5666305`.  It dispatches the 9 rows to `corollary_23_row1 … row9`
(row 5 lives in `FKS2Cor23.lean`; rows 1–4,6–9 in their own files).

(The `FKS2.corollary_23` stub in `FKS2.lean` is declared *upstream* of these
per-row files, so the assembled dispatch necessarily lives here, downstream.)
-/

namespace FKS2
open Real

/-- **FKS2 Corollary 23 (complete).** Every Table-6 row gives an admissible
asymptotic bound for `Eπ` with `R = 5.5666305`. -/
theorem corollary_23_all (Aπ B C x₀ : ℝ) (h : [Aπ, B, C, x₀] ∈ table6) :
    Eπ.classicalBound Aπ B C 5.5666305 (Real.exp x₀) := by
  fin_cases h
  · rw [show (1.00:ℝ) = 1 by norm_num]; exact corollary_23_row1
  · rw [show (1.00:ℝ) = 1 by norm_num, show (1.000:ℝ) = 1 by norm_num]
    exact corollary_23_row2
  · rw [show (0.50:ℝ) = 0.5 by norm_num, show (1.50:ℝ) = 1.5 by norm_num,
        show (2.000:ℝ) = 2 by norm_num]
    exact corollary_23_row3
  · rw [show (1.00:ℝ) = 1 by norm_num, show (1.50:ℝ) = 1.5 by norm_num,
        show (3.000:ℝ) = 3 by norm_num]
    exact corollary_23_row4
  · rw [show (1.50:ℝ) = 1.5 by norm_num, show (3.000:ℝ) = 3 by norm_num]
    exact corollary_23_row5
  · rw [show (1.50:ℝ) = 1.5 by norm_num, show (1.90:ℝ) = 1.9 by norm_num,
        show (1.000:ℝ) = 1 by norm_num]
    exact corollary_23_row6
  · rw [show (1.50:ℝ) = 1.5 by norm_num, show (1.000:ℝ) = 1 by norm_num]
    exact corollary_23_row7
  · rw [show (1.50:ℝ) = 1.5 by norm_num, show (2.00:ℝ) = 2 by norm_num,
        show (1.000:ℝ) = 1 by norm_num]
    exact corollary_23_row8
  · rw [show (2.00:ℝ) = 2 by norm_num, show (3.000:ℝ) = 3 by norm_num]
    exact corollary_23_row9

end FKS2
