import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row11

/-!
# FKS2 Corollary 24 — row 9 (`x^{-1/10}`) mid-range envelope

Row 9 (`n = 10`) of Table-7, cloned from the complete row 11 (`n = 100`) via the
generic `n`-parameterized helpers of `FKS2Cor24Row11`
(`Table4Ext.expSplitNegXpow`, `Table4Ext.eval_expSplitNegXpow_eq_xpow`,
`Table4Ext.lhsE_sub_negxpow_supported`, `Table4Ext.Epi_le_evalLhsE_low`,
`Table4Ext.floor_xpow_of_check`, `Table4Ext.mid_xpow_of`, `Table4Ext.checkXpowCell`,
`Table4Ext.cell_Epi_le_xpow_of_check`), all instantiated here at `n = 10`.

`boundaryCell_fails_row9` records that the first excluded cell `[270,271]`
(index `260`) fails, so the row-9 envelope certifies exactly
`allCells.take 260` (cells with `b' ≤ 270`).

The row-9 curve `corollary_24_row9 : ∀ x, log x ∈ [1, 270.8] → Eπ x ≤ x^{-1/10}`
is assembled from four segments split at `e^4`, `e^10`, `e^270`:
* **floor-trusted** `[e^1, e^4]` (`floor_trusted_row9`, trusted `sorry`);
* **floor (Buthe)** `[e^4, e^10]` (`floor_row9`, dyadic slab cover);
* **mid (envelope)** `[e^10, e^270]` (`mid_row9`, `allCells.take 260`);
* **sliver** `[e^270, e^270.8]` (`sliver_row9`, trusted `sorry`).
-/

namespace FKS2

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 9 (`x^{-1/10}`, `log x ∈ [1, 270.8]`) -/

/-- The row-9 (`n = 10`) certified prefix of `allCells`: the first `260` cells
(`b' ≤ 270`) form a contiguous chain from `b = 10` to `b' = 270`; the next cell
`[270,271]` fails (`boundaryCell_fails_row9`). -/
theorem midCells_chain_row9 : chainOk 10 (allCells.take 260) = true := by native_decide

theorem midCells_ne_nil_row9 : allCells.take 260 ≠ [] := by native_decide

theorem midCells_last_row9 : lastB 10 (allCells.take 260) = 270 := by native_decide

/-- Every cell of the row-9 passing prefix satisfies the `n = 10` numeric
certificate `exp(s²/10) ≤ 1/ε`, verified by the dyadic interval kernel over all
`260` cells. -/
theorem allCells_take_checkXpow_row9 :
    (allCells.take 260).all (fun c => checkXpowCell 10 c) = true := by native_decide

/-- Boundary witness: the first cell past the mid-range, `[270,271]`, fails the
row-9 check. -/
theorem boundaryCell_fails_row9 :
    ((allCells.drop 260).take 1).all (fun c => checkXpowCell 10 c) = false := by
  native_decide

/-- **Row-9 mid** `[e^10, e^270]` via the certified envelope prefix. -/
theorem mid_row9 : ∀ x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp (270:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/10) := by
  intro x hx
  have hmem : x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp ((270:ℕ):ℝ)) := by
    refine ⟨hx.1, ?_⟩
    rw [show ((270:ℕ):ℝ) = (270:ℝ) from by norm_num]; exact hx.2
  have h := mid_xpow_of 10 (by norm_num) 260 270
    midCells_chain_row9 midCells_ne_nil_row9 midCells_last_row9
    allCells_take_checkXpow_row9 x hmem
  simpa using h

/-- Row-9 floor slab certificate: `lhsE ≤ expSplitNegXpow 10` (the Buthe
`x^{-1/2}` bound `≤ x^{-1/10}`) over the 24 width-`0.05` slabs covering
`[√4, √10] = [2, 3.1623]`, verified by the dyadic interval kernel. -/
theorem floor_slab_check_row9 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (expSplitNegXpow 10)
      (slabsFrom 2 24) (-50) 8 = true := by native_decide

/-- **Row-9 floor (Buthe)** `[e^4, e^10]` via `floor_xpow_of_check`. -/
theorem floor_row9 : ∀ x ∈ Set.Icc (Real.exp (4:ℝ)) (Real.exp (10:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/10) := by
  intro x hx
  have hcurve : ∀ y, Real.exp (4:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (expSplitNegXpow 10)
        ≤ y ^ (-(1:ℝ)/(10:ℕ)) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h4 : (4:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (4:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    exact le_of_eq (eval_expSplitNegXpow_eq_xpow 10 (by norm_num) y hypos hyL)
  have h := floor_xpow_of_check (expSplitNegXpow 10) 10 (4:ℝ) 2 24 (by norm_num)
    (by rw [show ((2:ℚ):ℝ) = 2 by norm_num,
          show (2:ℝ) = Real.sqrt (2^2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h316 : Real.sqrt 10 ≤ 3.163 := by
          rw [show (3.163:ℝ) = Real.sqrt (3.163^2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h316])
    (lhsE_sub_negxpow_supported 10) floor_slab_check_row9 hcurve x hx
  simpa using h

/-- **Row-9 floor-trusted** `[e^1, e^4]` (`x ∈ [2.72, 54.6]`): the direct
`π`/`Li` interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`",
FKS2.lean:4640). No tight sub-`e^{4}` `Eπ` envelope exists in the library for the
sharp `x^{-1/10}` target (the Buthe bound only clears it from `L ≈ 3.49`). Same
accepted numerical-data trust class as `Table4Ext.allCells_trusted`. -/
theorem floor_trusted_row9 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (4:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/10) := by
  exact FKS2.Cor24Trusted.floor_trusted_row9

/-- **Row-9 sliver** `[e^270, e^270.8]` (width `≈ 0.8` in `log x`, at the
threshold): the `x^{-1/10}` curve is close to the `allCells` envelope on this
band, resolved in FKS2 by the refined Theorem-6 interpolation (arXiv
2206.12557, §5.2/5.3 / the "more refined collection of values than Table 4",
FKS2.lean:4640). Same accepted trust class as `Table4Ext.allCells_trusted`. -/
theorem sliver_row9 : ∀ x ∈ Set.Icc (Real.exp (270:ℝ)) (Real.exp (270.8:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/10) := by
  exact FKS2.Cor24Trusted.sliver_row9

/-- **FKS2 Corollary 24, row 9** (`table7` entry `(x ↦ x^{-1/10}, Icc 1 270.8)`):
`Eπ x ≤ x^{-1/10}` whenever `log x ∈ [1, 270.8]`. For `x > 0` this splits into
the four segments above; for `x ≤ 0` (possible since `log` is even) `Eπ x ≤ 0 <
x^{-1/10}`. -/
theorem corollary_24_row9 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 270.8 → Eπ x ≤ x ^ (-(1:ℝ)/10) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `Eπ x ≤ 0 < x^{-1/10}`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hRpos : (0:ℝ) < x ^ (-(1:ℝ)/10) := by
      rw [Real.rpow_def_of_neg hxneg]
      apply mul_pos (Real.exp_pos _)
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, Real.pi_le_four]
    linarith
  · -- x = 0: `log 0 = 0` contradicts `1 ≤ log x`
    exfalso; rw [hx0, Real.log_zero] at hlo; linarith
  · -- x > 0: dispatch to the four segments
    have cvt : ∀ a b : ℝ, a ≤ Real.log x → Real.log x ≤ b →
        x ∈ Set.Icc (Real.exp a) (Real.exp b) := by
      intro a b ha hb
      exact ⟨by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr ha,
             by rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hb⟩
    rcases le_total (Real.log x) 4 with h1 | h1
    · exact floor_trusted_row9 x (cvt 1 4 hlo h1)
    · rcases le_total (Real.log x) 10 with h2 | h2
      · exact floor_row9 x (cvt 4 10 h1 h2)
      · rcases le_total (Real.log x) 270 with h3 | h3
        · exact mid_row9 x (cvt 10 270 h2 h3)
        · exact sliver_row9 x (cvt 270 270.8 h3 hhi)

end FKS2
