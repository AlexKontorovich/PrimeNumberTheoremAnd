import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row4

/-!
# FKS2 Corollary 24 — row 1 (`2·log x·x^{-1/2}`)

`table7` entry `(x ↦ 2 * log x * x^(-1/2), Icc 1 57)`.  Clone of row 4
(`FKS2Cor24Row4.lean`), reusing the generic `x^{-1/2}`-curve machinery in
`Table4Ext` (`Epi_le_evalLhsE_wide`, `xhalfCurveE`, `eval_xhalfCurveE`,
`xhalfCurve_sub_supported`, `floor_xhalf_of_check`).

Unlike row 4/5, the Buthe floor threshold `Lf = 3` used by rows 4/5 does **not**
certify here: at `L = 3` the Buthe polynomial (`≈ 6.12`) exceeds `c·L = 2·3 = 6`.
Raised to `Lf = 4` (`√4 = 2` exactly, so the slab-cover lower endpoint needs no
irrational-sqrt bridging lemma), the floor certifies with margin from `L = 4` on.
-/

namespace FKS2

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 1 (`2·log x·x^{-1/2}`, `log x ∈ [1, 57]`)

The Table-7 row-1 curve, assembled from three segments split at `e^4`, `e^43`:

* **floor-trusted** `[e^1, e^4]` — direct `π`/`Li` for small `x` (trusted, `sorry`);
* **Buthe floor** `[e^4, e^43]` — `floor_xhalf_of_check` + a dyadic slab cover of `[√4, √43]
  = [2, √43]` (`slabsFrom 2 93`);
* **trusted band** `[e^43, e^57]` — Theorem-6 refined interpolation for `log x > log(10^19)`
  (trusted, `sorry`).
-/

/-- Row-1 floor slab certificate: `FloorButhe.lhsE ≤ xhalfCurveE 2 2` (the Buthe `x^{-1/2}`
bound `≤ 2·(log x)·x^{-1/2}`) over the 93 width-`0.05` slabs covering `[2, √43]`, verified
by the dyadic interval kernel.  (At `L = 3` the Buthe polynomial `≈ 6.12 > 2·L = 6`, so the
check fails there; from `L = 4` on, `≈ 4.71 ≤ 2·L = 8`, with growing margin.) -/
theorem floor_slab_check_row1 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (xhalfCurveE 2 2)
      (slabsFrom 2 93) (-50) 8 = true := by native_decide

/-- **Row-1 Buthe floor** `[e^4, e^43]` via `floor_xhalf_of_check`. -/
theorem floor_row1 : ∀ x ∈ Set.Icc (Real.exp (4:ℝ)) (Real.exp (43:ℝ)),
    Eπ x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
  have hcurve : ∀ y, Real.exp (4:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (xhalfCurveE 2 2)
        ≤ 2 * Real.log y * y ^ (-(1:ℝ) / 2) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h4 : (4:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (4:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    refine le_of_eq ?_
    rw [eval_xhalfCurveE 2 2 y hypos hyL, Real.sq_sqrt hyL]
    push_cast; ring
  exact floor_xhalf_of_check (xhalfCurveE 2 2)
    (fun x => 2 * Real.log x * x ^ (-(1:ℝ) / 2)) 4 2 93 (by norm_num)
    (by rw [show ((2:ℚ):ℝ) = 2 by norm_num,
          show (2:ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h656 : Real.sqrt 43 ≤ 6.56 := by
          rw [show (6.56:ℝ) = Real.sqrt (6.56 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h656])
    (xhalfCurve_sub_supported 2 2) floor_slab_check_row1 hcurve

/-- **Row-1 floor-trusted** `[e^1, e^4]` (`x ∈ [2.72, 54.6]`): the direct `π`/`Li`
interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`", FKS2.lean:4640).
Same accepted numerical-data trust class as `Table4Ext.allCells_trusted` and
`floor_trusted_row4`. -/
theorem floor_trusted_row1 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (4:ℝ)),
    Eπ x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.floor_trusted_row1

/-- **Row-1 trusted band** `[e^43, e^57]` (`log x ∈ (log 10^19, 57]`): the blueprint's
Theorem-6 interpolation for `log x > log(10^19)` — "one simply proceeds as in
\cite[Lemmas 5.2, 5.3]{FKS} and interpolates the numerical results of Theorem 6"
(FKS2.lean:4640).  Same accepted trust class as `band_row4`. -/
theorem band_row1 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (57:ℝ)),
    Eπ x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.band_row1

/-- **FKS2 Corollary 24, row 1** (`table7` entry `(x ↦ 2·log x·x^{-1/2}, Icc 1 57)`):
`Eπ x ≤ 2·log x·x^{-1/2}` whenever `log x ∈ [1, 57]`.  For `x > 0` this splits into
the three segments above; for `x < 0` (possible since `log` is even) the exponent
`-(1)/2` gives `cos((-(1)/2)·π) = cos(-π/2) = 0`, so `x^{-1/2} = 0` and the RHS is `0`,
while `Eπ x ≤ 0`. -/
theorem corollary_24_row1 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 57 → Eπ x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
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
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the three segments split at `log x = 4, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 4 with h1 | h1
    · exact floor_trusted_row1 x (cvt 1 4 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row1 x (cvt 4 43 h1 h2)
      · exact band_row1 x (cvt 43 57 h2 hhi)

end FKS2
