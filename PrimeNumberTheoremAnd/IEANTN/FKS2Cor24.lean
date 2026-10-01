import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23
import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24TrustedNumerics

/-!
# FKS2 Corollary 24 (#1429) — Table-7 `x^{-1/2}` bounds on `Eπ`

`corollary_24` bounds `Eπ x ≤ B x` for `log x ∈ I`, where `(B, I)` ranges over the
11 rows of `table7` (curves `c·(log x)^k·x^{-1/2}` and `x^{-1/n}` on finite
`log x`-intervals, all with `log x < 20000`).

Blueprint: "Same as in Corollary 23".  Shared building block here:
`Epi_le_xpow_half` — the Buthe `Eπ`-bound (`Buthe.theorem_2e/2f`) reread directly
in `x^{-1/2}` form.  Each row then splits as Buthe `[e^a, e^10]` + envelope
`[e^10, e^b]` (no tail — every interval is inside the `allCells` range).
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/- Guard for the `exact` bridges to `FKS2.Cor24Trusted`: its file-local `Epi` is
definitionally equal to this development's root-namespace `Eπ`.  If `Eπ` (`Defs.lean`)
ever changes, this `rfl` breaks *here* — pointing at the duplicated def — instead of
failing obscurely at each `exact` call site in the row files. -/
example (x : ℝ) : Eπ x = FKS2.Cor24Trusted.Epi x := rfl

/-- **Buthe bound in `x^{-1/2}` form** (shared core for all Table-7 rows): from
`Buthe.theorem_2e/2f` (valid `x ∈ [2, 10^19]`),
`Eπ x ≤ (1.95 + 3.9/log x + 19.5/(log x)²)·x^{-1/2} + 1.0452·(log x)/x`. -/
theorem Epi_le_xpow_half (x : ℝ) (h2 : 2 ≤ x) (h19 : x ≤ (10 : ℝ) ^ 19) :
    Eπ x ≤ (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ 2) * x ^ (-(1:ℝ)/2)
            + 1.0452 * Real.log x / x := by
  have hxpos : (0:ℝ) < x := by linarith
  have hLpos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hLne : Real.log x ≠ 0 := ne_of_gt hLpos
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have h2e := Buthe.theorem_2e h2 h19
  have h2f := Buthe.theorem_2f h2 h19
  have hsub := li.sub_Li x h2
  have hli2 := li.two_approx
  have hpiLi : pi x - Li x = li 2 - (li x - pi x) := by linarith [hsub]
  have habs : |pi x - Li x| ≤ (li x - pi x) + li 2 := by
    rw [hpiLi, abs_le]; constructor <;> linarith [h2f, hli2.1]
  have hEpi_eq : Eπ x = |pi x - Li x| * (Real.log x / x) := by
    unfold Eπ; rw [div_div_eq_mul_div, mul_div_assoc]
  rw [hEpi_eq]
  set C := (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ 2) with hC
  have hfac_nn : (0:ℝ) ≤ Real.log x / x := by positivity
  have hstep : |pi x - Li x| * (Real.log x / x)
      ≤ ((Real.sqrt x / Real.log x) * C + 1.0452) * (Real.log x / x) := by
    apply mul_le_mul_of_nonneg_right _ hfac_nn
    calc |pi x - Li x| ≤ (li x - pi x) + li 2 := habs
      _ ≤ (Real.sqrt x / Real.log x) * C + 1.0452 := by
          apply add_le_add h2e hli2.2
  refine le_trans hstep (le_of_eq ?_)
  have hsqrt_x : Real.sqrt x / x = x ^ (-(1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hxpos]
    norm_num
  rw [show ((Real.sqrt x / Real.log x) * C + 1.0452) * (Real.log x / x)
        = C * (Real.sqrt x / x) + 1.0452 * Real.log x / x by field_simp,
      hsqrt_x]

end FKS2
