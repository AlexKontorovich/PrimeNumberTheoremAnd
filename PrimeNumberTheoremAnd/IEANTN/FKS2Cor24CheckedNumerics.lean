import PrimeNumberTheoremAnd.IEANTN.LeanCertEnclosures

/-!
# Checked small-window numerics for FKS2 Corollary 24

This file replaces the trusted row-11 floor datum by a checked computation using
the reusable PNT+ enclosures registered in `LeanCertEnclosures`.

The calculation deliberately uses the larger rational box `[2, 34]`. LeanCert
subdivides it into width-at-most-one leaves, verifies `Eπ x ≤ 19/20`, and separately
checks that `19/20 ≤ x⁻¹˰⁰` there. Elementary exponential bounds place the FKS2
window `[e, e³·⁵]` inside this box. As with PNT+'s existing finite table checks, the
large decidable certificate uses `native_decide`; the enclosing theorems and analytic
glue are checked by Lean's kernel.
-/

namespace FKS2.Cor24Checked

set_option maxHeartbeats 1000000 in
-- Reifying the 128-panel quadrature certificates needs more than the project default.
/-- The former trusted row-11 floor calculation, discharged by checked interval arithmetic. -/
theorem floor_row11 : ∀ x ∈ Set.Icc (Real.exp (1 : ℝ)) (Real.exp (3.5 : ℝ)),
    Eπ x ≤ x ^ (-(1 : ℝ) / 100) := by
  have hexpLo : (2 : ℝ) ≤ Real.exp 1 := by leancert
  have hexpHi : Real.exp (3.5 : ℝ) ≤ 34 := by leancert
  have hEpi : ∀ x ∈ Set.Icc (2 : ℝ) 34, Eπ x ≤ (19 / 20 : ℚ) := by
    leancert (budget := 10) (subdivisions := 8) (trust := native)
  have hCurve : ∀ x ∈ Set.Icc (2 : ℝ) 34, (19 / 20 : ℚ) ≤
      Real.exp (Real.log x * (-(1 : ℝ) / 100)) := by
    leancert (trust := kernel)
  intro x hx
  have hx' : x ∈ Set.Icc (2 : ℝ) 34 :=
    ⟨hexpLo.trans hx.1, hx.2.trans hexpHi⟩
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx'.1
  calc
    Eπ x ≤ (19 / 20 : ℚ) := hEpi x hx'
    _ ≤ Real.exp (Real.log x * (-(1 : ℝ) / 100)) := hCurve x hx'
    _ = x ^ (-(1 : ℝ) / 100) := by rw [Real.rpow_def_of_pos hxpos]

end FKS2.Cor24Checked
