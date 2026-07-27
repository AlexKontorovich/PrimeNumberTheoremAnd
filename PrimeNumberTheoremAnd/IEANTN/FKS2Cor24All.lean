import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row1
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row2
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row3
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row4
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row5
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row6
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row7
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row8
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row9
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row10
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row11

/-!
# FKS2 Corollary 24 — complete Table-7 dispatch (all 11 rows)

`corollary_24_all` is the full statement of `FKS2.corollary_24`: every row
`(B, I)` of `table7` yields the pointwise bound `Eπ x ≤ B x` on `log x ∈ I`.
It dispatches the 11 rows to `corollary_24_row1 … row11` (each proved in its own
file `FKS2Cor24Row{1..11}.lean`).

(The `FKS2.corollary_24` stub in `FKS2.lean` is declared *upstream* of these
per-row files, so the assembled dispatch necessarily lives here, downstream.
Mirrors `FKS2Cor23All.lean`'s Table-6 dispatch for Corollary 23.)
-/

namespace FKS2
open Real

/-- **FKS2 Corollary 24 (complete).** Every Table-7 row `(B, I)` gives the
pointwise bound `Eπ x ≤ B x` for all `x` with `log x ∈ I`. -/
theorem corollary_24_all (B : ℝ → ℝ) (I : Set ℝ) (h : (B, I) ∈ table7) :
    ∀ x, Real.log x ∈ I → Eπ x ≤ B x := by
  intro x hx
  simp only [table7, List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
  · exact corollary_24_row1 x hx
  · exact corollary_24_row2 x hx
  · exact corollary_24_row3 x hx
  · exact corollary_24_row4 x hx
  · exact corollary_24_row5 x hx
  · exact corollary_24_row6 x hx
  · exact corollary_24_row7 x hx
  · exact corollary_24_row8 x hx
  · exact corollary_24_row9 x hx
  · exact corollary_24_row10 x hx
  · exact corollary_24_row11 x hx
  · exact absurd h (by simp)

end FKS2
