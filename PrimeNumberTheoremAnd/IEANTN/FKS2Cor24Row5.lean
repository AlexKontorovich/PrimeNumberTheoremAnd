import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row4

/-!
# FKS2 Corollary 24 — row 5 (`(log x)³·x^{-1/2}`)

`table7` entry `(x ↦ (log x)^3 * x^(-1/2), Icc 1 80)`.  Clone of row 4
(`FKS2Cor24Row4.lean`), reusing the generic `x^{-1/2}`-curve machinery in
`Table4Ext` (`Epi_le_evalLhsE_wide`, `xhalfCurveE`, `eval_xhalfCurveE`,
`xhalfCurve_sub_supported`, `floor_xhalf_of_check`).  Same three-segment split
at `e^3`, `e^43` as row 4; only the top of the trusted band moves to `e^80`
and the bridge exponent moves from `(√L)^4 = L^2` to `(√L)^6 = L^3`.
-/

namespace FKS2

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 5 (`(log x)³·x^{-1/2}`, `log x ∈ [1, 80]`)

The Table-7 row-5 curve, assembled from three segments split at `e^3`, `e^43`:

* **floor-trusted** `[e^1, e^3]` — direct `π`/`Li` for small `x` (trusted, `sorry`);
* **Buthe floor** `[e^3, e^43]` — `floor_xhalf_of_check` + a dyadic slab cover of `[√3, √43]`
  (identical cover to row 4: `slabsFrom (173/100) 97`);
* **trusted band** `[e^43, e^80]` — Theorem-6 refined interpolation for `log x > log(10^19)`
  (trusted, `sorry`).
-/

/-- Row-5 floor slab certificate: `FloorButhe.lhsE ≤ xhalfCurveE 1 6` (the Buthe `x^{-1/2}`
bound `≤ (log x)³·x^{-1/2}`) over the 97 width-`0.05` slabs covering `[√3, √43]`, verified
by the dyadic interval kernel.  (`c·L³` dominates the Buthe polynomial even more easily than
row 4's `L²` from `L = 3` on, so the same cover works verbatim.) -/
theorem floor_slab_check_row5 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (xhalfCurveE 1 6)
      (slabsFrom (173/100) 97) (-50) 8 = true := by native_decide

/-- **Row-5 Buthe floor** `[e^3, e^43]` via `floor_xhalf_of_check`.  (Named `floor_xhalf_row5`,
not `floor_row5`, since `FKS2.floor_row5` is already taken by Corollary 23's row 5 in the
imported `FKS2Cor23.lean` base file — unrelated corollary, same row index.) -/
theorem floor_xhalf_row5 : ∀ x ∈ Set.Icc (Real.exp (3:ℝ)) (Real.exp (43:ℝ)),
    Eπ x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
  have hcurve : ∀ y, Real.exp (3:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (xhalfCurveE 1 6)
        ≤ (Real.log y) ^ 3 * y ^ (-(1:ℝ) / 2) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h3 : (3:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (3:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    refine le_of_eq ?_
    have hsq : (Real.sqrt (Real.log y)) ^ 6 = (Real.log y) ^ 3 := by
      rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hyL]
    rw [eval_xhalfCurveE 1 6 y hypos hyL, hsq]
    push_cast; ring
  exact floor_xhalf_of_check (xhalfCurveE 1 6)
    (fun x => (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2)) 3 (173/100) 97 (by norm_num)
    (by rw [show ((173/100:ℚ):ℝ) = 1.73 by norm_num,
          show (1.73:ℝ) = Real.sqrt (1.73 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h656 : Real.sqrt 43 ≤ 6.56 := by
          rw [show (6.56:ℝ) = Real.sqrt (6.56 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h656])
    (xhalfCurve_sub_supported 1 6) floor_slab_check_row5 hcurve

/-- **Row-5 floor-trusted** `[e^1, e^3]` (`x ∈ [2.72, 20.1]`): the direct `π`/`Li`
interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`", FKS2.lean:4640).
Same accepted numerical-data trust class as `Table4Ext.allCells_trusted` and
`floor_trusted_row4`. -/
theorem floor_trusted_row5 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (3:ℝ)),
    Eπ x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.floor_trusted_row5

/-- **Row-5 trusted band** `[e^43, e^80]` (`log x ∈ (log 10^19, 80]`): the blueprint's
Theorem-6 interpolation for `log x > log(10^19)` — "one simply proceeds as in
\cite[Lemmas 5.2, 5.3]{FKS} and interpolates the numerical results of Theorem 6"
(FKS2.lean:4640).  Same accepted trust class as `band_row4`. -/
theorem band_row5 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (80:ℝ)),
    Eπ x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.band_row5

/-- **FKS2 Corollary 24, row 5** (`table7` entry `(x ↦ (log x)³·x^{-1/2}, Icc 1 80)`):
`Eπ x ≤ (log x)³·x^{-1/2}` whenever `log x ∈ [1, 80]`.  For `x > 0` this splits into
the three segments above; for `x < 0` (possible since `log` is even) the exponent
`-(1)/2` gives `cos((-(1)/2)·π) = cos(-π/2) = 0`, so `x^{-1/2} = 0` and the RHS is `0`,
while `Eπ x ≤ 0`. -/
theorem corollary_24_row5 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 80 → Eπ x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
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
  · -- x > 0: dispatch to the three segments split at `log x = 3, 43`
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 3 with h1 | h1
    · exact floor_trusted_row5 x (cvt 1 3 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_xhalf_row5 x (cvt 3 43 h1 h2)
      · exact band_row5 x (cvt 43 80 h2 hhi)

end FKS2
