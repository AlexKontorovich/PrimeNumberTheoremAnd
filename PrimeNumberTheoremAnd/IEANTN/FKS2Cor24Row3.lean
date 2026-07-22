import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row4

/-!
# FKS2 Corollary 24 — row 3 (`(1/(8π))·(log x)²·x^{-1/2}`)

`table7` entry `(x ↦ (1/(8*π)) * (log x)^2 * x^(-1/2), Icc 8 60.8)`.  Clone of row 4
(`FKS2Cor24Row4.lean`), reusing the generic `x^{-1/2}`-curve machinery in
`Table4Ext` (`Epi_le_evalLhsE_wide`, `xhalfCurveE`, `eval_xhalfCurveE`,
`xhalfCurve_sub_supported`, `floor_xhalf_of_check`).

Two features distinguish this row from rows 1/2/4/5:

* the target coefficient `1/(8π)` is irrational, so the dyadic slab machinery (which needs
  a `ℚ` curve coefficient) instead certifies the *rational under-approximation*
  `c = 79/2000` (`0.0395 < 1/(8π) = 0.039789…`), and `hcurve` closes the gap with a
  one-line rational bound `π < 3.15` (`Real.pi_lt_d2`);
* the target interval starts at `log x = 8` (not `1`), so the floor-trusted segment is
  `[e^8, e^9]` and the whole dispatch shifts up.

`Lf = 9` is chosen (rather than `8`, as the naive "same as row 4" guess) because
`√9 = 3` is exactly rational: the slab-cover lower endpoint needs no irrational-sqrt
squeeze, and — empirically — starting the dyadic cover exactly at `s = 3` avoids the
interval-width blowup that made a `299/100`-anchored cover spuriously fail just
below `s = 3` (the mathematical margin there is real, ~13%, but a `0.05`-wide slab
straddling `L = 9` is too coarse for the certified check to resolve it). -/

namespace FKS2

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 3 (`(1/(8π))·(log x)²·x^{-1/2}`, `log x ∈ [8, 60.8]`)

The Table-7 row-3 curve, assembled from three segments split at `e^9`, `e^43`:

* **floor-trusted** `[e^8, e^9]` — direct `π`/`Li` for small `x` (trusted, `sorry`);
* **Buthe floor** `[e^9, e^43]` — `floor_xhalf_of_check` against the rational
  under-approximation `xhalfCurveE (79/2000) 4`, then `hcurve` bridges
  `(79/2000)·(log x)²·x^{-1/2} ≤ (1/(8π))·(log x)²·x^{-1/2}` via `π < 3.15`;
* **trusted band** `[e^43, e^60.8]` — Theorem-6 refined interpolation for
  `log x > log(10^19)` (trusted, `sorry`).
-/

/-- Row-3 floor slab certificate: `FloorButhe.lhsE ≤ xhalfCurveE (79/2000) 4` (the Buthe
`x^{-1/2}` bound `≤ (79/2000)·(log x)²·x^{-1/2}`, a rational under-approximation of the
target `(1/(8π))·(log x)²·x^{-1/2}`) over the 74 width-`0.05` slabs covering `[√9, √43]
= [3, √43]`, verified by the dyadic interval kernel. -/
theorem floor_slab_check_row3 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (xhalfCurveE (79/2000) 4)
      (slabsFrom 3 74) (-50) 8 = true := by native_decide

/-- **Row-3 Buthe floor** `[e^9, e^43]` via `floor_xhalf_of_check`. -/
theorem floor_row3 : ∀ x ∈ Set.Icc (Real.exp (9:ℝ)) (Real.exp (43:ℝ)),
    Eπ x ≤ (1 / (8 * π)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  have hcurve : ∀ y, Real.exp (9:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (xhalfCurveE (79/2000) 4)
        ≤ (1 / (8 * π)) * (Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h9 : (9:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (9:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    have hsq : (Real.sqrt (Real.log y)) ^ 4 = (Real.log y) ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hyL]
    rw [eval_xhalfCurveE (79/2000) 4 y hypos hyL, hsq]
    push_cast
    have hc_le : (79/2000:ℝ) ≤ 1 / (8 * π) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * π)]
      nlinarith [Real.pi_lt_d2]
    have hnn : (0:ℝ) ≤ (Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2) := by positivity
    calc (79/2000:ℝ) * (Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2)
        = (79/2000:ℝ) * ((Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2)) := by ring
      _ ≤ (1 / (8 * π)) * ((Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hc_le hnn
      _ = (1 / (8 * π)) * (Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2) := by ring
  exact floor_xhalf_of_check (xhalfCurveE (79/2000) 4)
    (fun x => (1 / (8 * π)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2)) 9 3 74 (by norm_num)
    (by rw [show ((3:ℚ):ℝ) = 3 by norm_num,
          show (3:ℝ) = Real.sqrt (3 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h656 : Real.sqrt 43 ≤ 6.56 := by
          rw [show (6.56:ℝ) = Real.sqrt (6.56 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h656])
    (xhalfCurve_sub_supported (79/2000) 4) floor_slab_check_row3 hcurve

/-- **Row-3 floor-trusted** `[e^8, e^9]` (`x ∈ [2981, 8103]`): the direct `π`/`Li`
interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`", FKS2.lean:4640).
Same accepted numerical-data trust class as `Table4Ext.allCells_trusted` and
`floor_trusted_row4`. -/
theorem floor_trusted_row3 : ∀ x ∈ Set.Icc (Real.exp (8:ℝ)) (Real.exp (9:ℝ)),
    Eπ x ≤ (1 / (8 * π)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.floor_trusted_row3

/-- **Row-3 trusted band** `[e^43, e^60.8]` (`log x ∈ (log 10^19, 60.8]`): the blueprint's
Theorem-6 interpolation for `log x > log(10^19)` — "one simply proceeds as in
\cite[Lemmas 5.2, 5.3]{FKS} and interpolates the numerical results of Theorem 6"
(FKS2.lean:4640).  Same accepted trust class as `band_row4`. -/
theorem band_row3 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (60.8:ℝ)),
    Eπ x ≤ (1 / (8 * π)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.band_row3

/-- **FKS2 Corollary 24, row 3**
(`table7` entry `(x ↦ (1/(8π))·(log x)²·x^{-1/2}, Icc 8 60.8)`):
`Eπ x ≤ (1/(8π))·(log x)²·x^{-1/2}` whenever `log x ∈ [8, 60.8]`.  For `x > 0` this
splits into the three segments above; for `x < 0` (possible since `log` is even) the
exponent `-(1)/2` gives `cos((-(1)/2)·π) = cos(-π/2) = 0`, so `x^{-1/2} = 0` and the RHS
is `0`, while `Eπ x ≤ 0`. -/
theorem corollary_24_row3 :
    ∀ x, Real.log x ∈ Set.Icc (8:ℝ) 60.8 →
      Eπ x ≤ (1 / (8 * π)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `x^{-1/2} = exp(...)·cos(-π/2) = 0`, so RHS = 0; and `Eπ x ≤ 0`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hxhalf0 : x ^ (-(1:ℝ) / 2) = 0 := by
      rw [Real.rpow_def_of_neg hxneg,
        show (-(1:ℝ) / 2) * π = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
    rw [hxhalf0, mul_zero]
    exact hEle0
  · -- x = 0: `log 0 = 0` contradicts `8 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 9, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 9 with h1 | h1
    · exact floor_trusted_row3 x (cvt 8 9 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row3 x (cvt 9 43 h1 h2)
      · exact band_row3 x (cvt 43 60.8 h2 hhi)

end FKS2
