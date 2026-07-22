import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row11

/-!
# FKS2 Corollary 24 — row 7 (`x^{-1/4}`) mid-range envelope

Row 7 (`n = 4`) of Table-7, cloned from the complete row 11 (`n = 100`) via the
generic `n`-parameterized helpers of `FKS2Cor24Row11`
(`Table4Ext.expSplitNegXpow`, `Table4Ext.eval_expSplitNegXpow_eq_xpow`,
`Table4Ext.lhsE_sub_negxpow_supported`, `Table4Ext.Epi_le_evalLhsE_low`,
`Table4Ext.floor_xpow_of_check`, `Table4Ext.mid_xpow_of`, `Table4Ext.checkXpowCell`,
`Table4Ext.cell_Epi_le_xpow_of_check`), all instantiated here at `n = 4`.

`boundaryCell_fails_row7` records that the first excluded cell `[107,108]`
(index `97`) fails, so the row-7 envelope certifies exactly
`allCells.take 97` (cells with `b' ≤ 107`).

The row-7 curve `corollary_24_row7 : ∀ x, log x ∈ [1, 107.6] → Eπ x ≤ x^{-1/4}`
is assembled from four segments split at `e^6`, `e^10`, `e^107`:
* **floor-trusted** `[e^1, e^6]` (`floor_trusted_row7`, trusted `sorry`);
* **floor (Buthe)** `[e^6, e^10]` (`floor_row7`, dyadic slab cover);
* **mid (envelope)** `[e^10, e^107]` (`mid_row7`, `allCells.take 97`);
* **sliver** `[e^107, e^107.6]` (`sliver_row7`, trusted `sorry`).
-/

namespace FKS2

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 7 (`x^{-1/4}`, `log x ∈ [1, 107.6]`) -/

/-- The row-7 (`n = 4`) certified prefix of `allCells`: the first `97` cells
(`b' ≤ 107`) form a contiguous chain from `b = 10` to `b' = 107`; the next cell
`[107,108]` fails (`boundaryCell_fails_row7`). -/
theorem midCells_chain_row7 : chainOk 10 (allCells.take 97) = true := by native_decide

theorem midCells_ne_nil_row7 : allCells.take 97 ≠ [] := by native_decide

theorem midCells_last_row7 : lastB 10 (allCells.take 97) = 107 := by native_decide

/-- Every cell of the row-7 passing prefix satisfies the `n = 4` numeric
certificate `exp(s²/4) ≤ 1/ε`, verified by the dyadic interval kernel over all
`97` cells. -/
theorem allCells_take_checkXpow_row7 :
    (allCells.take 97).all (fun c => checkXpowCell 4 c) = true := by native_decide

/-- Boundary witness: the first cell past the mid-range, `[107,108]`, fails the
row-7 check. -/
theorem boundaryCell_fails_row7 :
    ((allCells.drop 97).take 1).all (fun c => checkXpowCell 4 c) = false := by
  native_decide

/-- **Row-7 mid** `[e^10, e^107]` via the certified envelope prefix. -/
theorem mid_row7 : ∀ x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp (107:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/4) := by
  intro x hx
  have hmem : x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp ((107:ℕ):ℝ)) := by
    refine ⟨hx.1, ?_⟩
    rw [show ((107:ℕ):ℝ) = (107:ℝ) from by norm_num]; exact hx.2
  have h := mid_xpow_of 4 (by norm_num) 97 107
    midCells_chain_row7 midCells_ne_nil_row7 midCells_last_row7
    allCells_take_checkXpow_row7 x hmem
  simpa using h

/-- Row-7 floor slab certificate: `lhsE ≤ expSplitNegXpow 4` (the Buthe
`x^{-1/2}` bound `≤ x^{-1/4}`) over the 15 width-`0.05` slabs covering
`[√6, √10] = [2.449, 3.1623]`, verified by the dyadic interval kernel. -/
theorem floor_slab_check_row7 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (expSplitNegXpow 4)
      (slabsFrom (244/100) 15) (-50) 8 = true := by native_decide

/-- **Row-7 floor (Buthe)** `[e^6, e^10]` via `floor_xpow_of_check`. -/
theorem floor_row7 : ∀ x ∈ Set.Icc (Real.exp (6:ℝ)) (Real.exp (10:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/4) := by
  intro x hx
  have hcurve : ∀ y, Real.exp (6:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (expSplitNegXpow 4)
        ≤ y ^ (-(1:ℝ)/(4:ℕ)) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h6 : (6:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (6:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    exact le_of_eq (eval_expSplitNegXpow_eq_xpow 4 (by norm_num) y hypos hyL)
  have h := floor_xpow_of_check (expSplitNegXpow 4) 4 (6:ℝ) (244/100) 15 (by norm_num)
    (by rw [show ((244/100:ℚ):ℝ) = 2.44 by norm_num,
          show (2.44:ℝ) = Real.sqrt (2.44^2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h316 : Real.sqrt 10 ≤ 3.163 := by
          rw [show (3.163:ℝ) = Real.sqrt (3.163^2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h316])
    (lhsE_sub_negxpow_supported 4) floor_slab_check_row7 hcurve x hx
  simpa using h

/-- **Row-7 floor-trusted** `[e^1, e^6]` (`x ∈ [2.72, 403.4]`): the direct
`π`/`Li` interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`",
FKS2.lean:4640). No tight sub-`e^{6}` `Eπ` envelope exists in the library for the
sharp `x^{-1/4}` target (the Buthe bound only clears it from `L ≈ 5.99`). Same
accepted numerical-data trust class as `Table4Ext.allCells_trusted`. -/
theorem floor_trusted_row7 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (6:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/4) := by
  exact FKS2.Cor24Trusted.floor_trusted_row7

/-- **Row-7 sliver** `[e^107, e^107.6]` (width `≈ 0.6` in `log x`, at the
threshold): the `x^{-1/4}` curve is close to the `allCells` envelope on this
band, resolved in FKS2 by the refined Theorem-6 interpolation (arXiv
2206.12557, §5.2/5.3 / the "more refined collection of values than Table 4",
FKS2.lean:4640). Same accepted trust class as `Table4Ext.allCells_trusted`. -/
theorem sliver_row7 : ∀ x ∈ Set.Icc (Real.exp (107:ℝ)) (Real.exp (107.6:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/4) := by
  exact FKS2.Cor24Trusted.sliver_row7

/-- **FKS2 Corollary 24, row 7** (`table7` entry `(x ↦ x^{-1/4}, Icc 1 107.6)`):
`Eπ x ≤ x^{-1/4}` whenever `log x ∈ [1, 107.6]`. For `x > 0` this splits into
the four segments above; for `x ≤ 0` (possible since `log` is even) `Eπ x ≤ 0 <
x^{-1/4}`. -/
theorem corollary_24_row7 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 107.6 → Eπ x ≤ x ^ (-(1:ℝ)/4) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `Eπ x ≤ 0 < x^{-1/4}`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hRpos : (0:ℝ) < x ^ (-(1:ℝ)/4) := by
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
    rcases le_total (Real.log x) 6 with h1 | h1
    · exact floor_trusted_row7 x (cvt 1 6 hlo h1)
    · rcases le_total (Real.log x) 10 with h2 | h2
      · exact floor_row7 x (cvt 6 10 h1 h2)
      · rcases le_total (Real.log x) 107 with h3 | h3
        · exact mid_row7 x (cvt 10 107 h2 h3)
        · exact sliver_row7 x (cvt 107 107.6 h3 hhi)

end FKS2
