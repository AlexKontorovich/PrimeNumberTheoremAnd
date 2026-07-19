import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row4

/-!
# FKS2 Corollary 24 — row 2 (`(log x)^{3/2}·x^{-1/2}`)

`table7` entry `(x ↦ (log x)^(3/2) * x^(-1/2), Icc 1 65.65)`.  Clone of row 4
(`FKS2Cor24Row4.lean`), reusing the generic `x^{-1/2}`-curve machinery in
`Table4Ext` (`Epi_le_evalLhsE_wide`, `xhalfCurveE`, `eval_xhalfCurveE`,
`xhalfCurve_sub_supported`, `floor_xhalf_of_check`).

The exponent `3/2` here is stated as `Real.rpow` (`(3/2 : ℝ)`), matching the
mathematical Table-7 entry: `(log x)^{3/2}` (a fractional power, not the `Nat`
power that a bare `(log x)^(3/2)` literal would silently elaborate to via
`Nat` division `3/2 = 1`).  The bridge from the curve machinery's `(√(log x))^3`
(a `Monoid.npow`) to `(log x)^(3/2 : ℝ)` (an `Real.rpow`) goes through
`Real.sqrt_eq_rpow`, `Real.rpow_natCast` and `Real.rpow_mul`.
-/

namespace FKS2

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 2 (`(log x)^{3/2}·x^{-1/2}`, `log x ∈ [1, 65.65]`)

The Table-7 row-2 curve, assembled from three segments split at `e^8`, `e^43`:

* **floor-trusted** `[e^1, e^8]` — direct `π`/`Li` for small `x` (trusted, `sorry`);
* **Buthe floor** `[e^8, e^43]` — `floor_xhalf_of_check` + a dyadic slab cover of
  `[√8, √43] ≈ [2.83, 6.56]` (`slabsFrom (282/100) 76`);
* **trusted band** `[e^43, e^65.65]` — Theorem-6 refined interpolation for
  `log x > log(10^19)` (trusted, `sorry`).
-/

/-- Row-2 floor slab certificate: `FloorButhe.lhsE ≤ xhalfCurveE 1 3` (the Buthe `x^{-1/2}`
bound `≤ (log x)^{3/2}·x^{-1/2}`) over the 76 width-`0.05` slabs covering `[√8, √43]`,
verified by the dyadic interval kernel. -/
theorem floor_slab_check_row2 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (xhalfCurveE 1 3)
      (slabsFrom (282/100) 76) (-50) 8 = true := by native_decide

/-- **Row-2 Buthe floor** `[e^8, e^43]` via `floor_xhalf_of_check`. -/
theorem floor_row2 : ∀ x ∈ Set.Icc (Real.exp (8:ℝ)) (Real.exp (43:ℝ)),
    Eπ x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
  have hcurve : ∀ y, Real.exp (8:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (xhalfCurveE 1 3)
        ≤ (Real.log y) ^ (3/2 : ℝ) * y ^ (-(1:ℝ) / 2) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h8 : (8:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (8:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    refine le_of_eq ?_
    have hsq : (Real.sqrt (Real.log y)) ^ 3 = (Real.log y) ^ (3/2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((Real.log y) ^ (1/2 : ℝ)) 3,
        ← Real.rpow_mul hyL]
      congr 1
      norm_num
    rw [eval_xhalfCurveE 1 3 y hypos hyL, hsq]
    push_cast; ring
  exact floor_xhalf_of_check (xhalfCurveE 1 3)
    (fun x => (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2)) 8 (282/100) 76 (by norm_num)
    (by rw [show ((282/100:ℚ):ℝ) = 2.82 by norm_num,
          show (2.82:ℝ) = Real.sqrt (2.82 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h656 : Real.sqrt 43 ≤ 6.56 := by
          rw [show (6.56:ℝ) = Real.sqrt (6.56 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h656])
    (xhalfCurve_sub_supported 1 3) floor_slab_check_row2 hcurve

/-- **Row-2 floor-trusted** `[e^1, e^8]` (`x ∈ [2.72, 2981]`): the direct `π`/`Li`
interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`", FKS2.lean:4640).
Wider than row 4's `[e^1,e^3]` since the Buthe floor for the `(log x)^{3/2}` curve only
certifies from `L = 8` on.  Same accepted numerical-data trust class as
`Table4Ext.allCells_trusted` and `floor_trusted_row4`. -/
theorem floor_trusted_row2 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (8:ℝ)),
    Eπ x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.floor_trusted_row2

/-- **Row-2 trusted band** `[e^43, e^65.65]` (`log x ∈ (log 10^19, 65.65]`): the blueprint's
Theorem-6 interpolation for `log x > log(10^19)` — "one simply proceeds as in
\cite[Lemmas 5.2, 5.3]{FKS} and interpolates the numerical results of Theorem 6"
(FKS2.lean:4640).  Same accepted trust class as `band_row4`. -/
theorem band_row2 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (65.65:ℝ)),
    Eπ x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.band_row2

/-- **FKS2 Corollary 24, row 2** (`table7` entry `(x ↦ (log x)^{3/2}·x^{-1/2}, Icc 1 65.65)`):
`Eπ x ≤ (log x)^{3/2}·x^{-1/2}` whenever `log x ∈ [1, 65.65]`.  For `x > 0` this splits into
the three segments above; for `x < 0` (possible since `log` is even) the exponent
`-(1)/2` gives `cos((-(1)/2)·π) = cos(-π/2) = 0`, so `x^{-1/2} = 0` and the RHS is `0`,
while `Eπ x ≤ 0`. -/
theorem corollary_24_row2 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 65.65 →
      Eπ x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
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
  · -- x > 0: dispatch to the three segments split at `log x = 8, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 8 with h1 | h1
    · exact floor_trusted_row2 x (cvt 1 8 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row2 x (cvt 8 43 h1 h2)
      · exact band_row2 x (cvt 43 65.65 h2 hhi)

end FKS2
