import PrimeNumberTheoremAnd.IEANTN.LeanCertEnclosures
import LeanCert.Tactic.Enclosure
import LeanCert.Tactic.IntervalAuto

/-!
# Checked small-window numerics for FKS2 Corollary 24

This file replaces trusted small-window floor data by checked computations using
the reusable PNT+ enclosures registered in `LeanCertEnclosures`.

Each calculation enlarges its exponential window to a rational box. LeanCert subdivides
that box into width-at-most-one leaves, verifies an `Eπ` bound, and separately checks the
elementary comparison with the relevant Table-7 curve. As with PNT+'s existing finite
table checks, the large decidable certificates use `native_decide`; the enclosing
theorems and analytic glue are checked by Lean's kernel.
-/

namespace FKS2.Cor24Checked

set_option maxHeartbeats 1000000 in
-- Reifying the 192-panel quadrature certificates needs more than the project default.
/-- The former trusted row-1 floor calculation, discharged by checked interval arithmetic. -/
theorem floor_row1 : ∀ x ∈ Set.Icc (Real.exp (1 : ℝ)) (Real.exp (4 : ℝ)),
    Eπ x ≤ 2 * Real.log x * x ^ (-(1 : ℝ) / 2) := by
  have hexpLo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hexpHi : Real.exp (4 : ℝ) ≤ 58 := by
    interval_decide (trust := kernel)
  have hEpiLow : ∀ x ∈ Set.Icc (2 : ℝ) 34, Eπ x ≤ (19 / 20 : ℝ) := by
    enclosure_bound (subdivisions := 8) (trust := native)
  have hEpiMid : ∀ x ∈ Set.Icc (34 : ℝ) 50, Eπ x ≤ (19 / 20 : ℝ) := by
    enclosure_bound (subdivisions := 8) (trust := native)
  have hEpiHigh : ∀ x ∈ Set.Icc (50 : ℝ) 58, Eπ x ≤ (19 / 20 : ℝ) := by
    enclosure_bound (subdivisions := 8) (trust := native)
  intro x hx
  have hx' : x ∈ Set.Icc (2 : ℝ) 58 :=
    ⟨hexpLo.trans hx.1, hx.2.trans hexpHi⟩
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx'.1
  have hlogLo : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hx.1
  have hlogHi : Real.log x ≤ (4 : ℝ) := by
    rw [← Real.log_exp (4 : ℝ)]
    exact Real.log_le_log hxpos hx.2
  have lowerOn (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ Real.log x) (hb : Real.log x ≤ b)
      (hconst : (19 / 20 : ℝ) ≤ 2 * a * Real.exp (-(b / 2))) :
      (19 / 20 : ℝ) ≤
      2 * Real.log x * Real.exp (Real.log x * (-(1 : ℝ) / 2)) := by
    have hexp : Real.exp (-(b / 2)) ≤
        Real.exp (Real.log x * (-(1 : ℝ) / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hfac : 2 * a ≤ 2 * Real.log x := by linarith
    exact hconst.trans
      (mul_le_mul hfac hexp (Real.exp_pos _).le (mul_nonneg (by norm_num) (ha0.trans ha)))
  have hCurve : (19 / 20 : ℝ) ≤
      2 * Real.log x * Real.exp (Real.log x * (-(1 : ℝ) / 2)) := by
    rcases le_total (Real.log x) (7 / 5 : ℝ) with hlogSevenFifths | hlogSevenFifths
    · apply lowerOn 1 (7 / 5) (by norm_num) hlogLo hlogSevenFifths
      interval_decide (trust := kernel)
    · rcases le_total (Real.log x) 2 with hlogTwo | hlogTwo
      · apply lowerOn (7 / 5) 2 (by norm_num) hlogSevenFifths hlogTwo
        interval_decide (trust := kernel)
      · rcases le_total (Real.log x) (14 / 5 : ℝ) with hlogFourteenFifths | hlogFourteenFifths
        · apply lowerOn 2 (14 / 5) (by norm_num) hlogTwo hlogFourteenFifths
          interval_decide (trust := kernel)
        · rcases le_total (Real.log x) (7 / 2 : ℝ) with hlogThreeHalf | hlogThreeHalf
          · apply lowerOn (14 / 5) (7 / 2) (by norm_num) hlogFourteenFifths hlogThreeHalf
            interval_decide (trust := kernel)
          · rcases le_total (Real.log x) (18 / 5 : ℝ) with hlogEighteenFifths | hlogEighteenFifths
            · apply lowerOn (7 / 2) (18 / 5) (by norm_num) hlogThreeHalf hlogEighteenFifths
              interval_decide (trust := kernel)
            · apply lowerOn (18 / 5) 4 (by norm_num) hlogEighteenFifths hlogHi
              interval_decide (trust := kernel)
  have hEpi : Eπ x ≤ (19 / 20 : ℝ) := by
    rcases le_total x 34 with hx34 | hx34
    · exact hEpiLow x ⟨hx'.1, hx34⟩
    · rcases le_total x 50 with hx50 | hx50
      · exact hEpiMid x ⟨hx34, hx50⟩
      · exact hEpiHigh x ⟨hx50, hx'.2⟩
  calc
    Eπ x ≤ (19 / 20 : ℝ) := hEpi
    _ ≤ 2 * Real.log x * Real.exp (Real.log x * (-(1 : ℝ) / 2)) := hCurve
    _ = 2 * Real.log x * x ^ (-(1 : ℝ) / 2) := by rw [Real.rpow_def_of_pos hxpos]

set_option maxHeartbeats 1000000 in
-- Reifying the 192-panel quadrature certificates needs more than the project default.
/-- The former trusted row-11 floor calculation, discharged by checked interval arithmetic. -/
theorem floor_row11 : ∀ x ∈ Set.Icc (Real.exp (1 : ℝ)) (Real.exp (3.5 : ℝ)),
    Eπ x ≤ x ^ (-(1 : ℝ) / 100) := by
  have hexpLo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hexpHi : Real.exp (3.5 : ℝ) ≤ 34 := by
    interval_decide (trust := kernel)
  have hEpi : ∀ x ∈ Set.Icc (2 : ℝ) 34, Eπ x ≤ (19 / 20 : ℚ) := by
    enclosure_bound (subdivisions := 8) (trust := native)
  have hCurve : ∀ x ∈ Set.Icc (2 : ℝ) 34, (19 / 20 : ℚ) ≤
      Real.exp (Real.log x * (-(1 : ℝ) / 100)) := by
    certify_bound (trust := kernel)
  intro x hx
  have hx' : x ∈ Set.Icc (2 : ℝ) 34 :=
    ⟨hexpLo.trans hx.1, hx.2.trans hexpHi⟩
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx'.1
  calc
    Eπ x ≤ (19 / 20 : ℚ) := hEpi x hx'
    _ ≤ Real.exp (Real.log x * (-(1 : ℝ) / 100)) := hCurve x hx'
    _ = x ^ (-(1 : ℝ) / 100) := by rw [Real.rpow_def_of_pos hxpos]

end FKS2.Cor24Checked
