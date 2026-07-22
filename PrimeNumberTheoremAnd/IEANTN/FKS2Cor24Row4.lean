import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24Row11

/-!
# FKS2 Corollary 24 — row 4 (`(log x)²·x^{-1/2}`) and the `x^{-1/2}`-curve floor machinery

Rows 1–5 of `table7` are the *sharp* `c·(log x)^K·x^{-1/2}` curves.  Unlike the
`x^{-1/n}` rows (6–11), the `allCells` numerical envelope does **not** fit under
these curves (the envelope's `ε ≈ exp(-√L)`-scale is `≫ x^{-1/2} = exp(-L/2)`), so
there is **no envelope mid segment**.  Each `x^{-1/2}` row instead splits into three
segments:

1. **floor-trusted** `[e^1, e^{Lf}]` — small-`x` direct `π`/`Li` check (trusted `sorry`,
   FKS §5.2/5.3);
2. **Buthe floor** `[e^{Lf}, e^43]` — PROVABLE.  The committed Buthe `x^{-1/2}` bound
   `FloorButhe.lhsE` (valid `x ∈ [2, 10^19]`, i.e. `log x ≤ 43.7`) is `≤ c·(log x)^K·x^{-1/2}`
   because `c·L^K` eventually dominates the Buthe polynomial `1.95 + 3.9/L + 19.5/L²`;
   certified by a dyadic slab cover of `[√Lf, √43]`;
3. **trusted band** `[e^43, e^b]` (`b ≤ 80`) — the blueprint's "interpolate the numerical
   results of Theorem 6" step for `log x > log(10^19)` (trusted `sorry`, the big authorized
   region for `x^{-1/2}` rows; same accepted trust class as `Table4Ext.allCells_trusted`
   and the Cor 23 row-8 band).

## Generic (`c`/`K`-parameterized) machinery, reusable for rows 1/2/3/5

* `Epi_le_evalLhsE_wide` — the Buthe `Eπ`-bound reread as `eval FloorButhe.lhsE (√(log x))`
  on the FULL `[2, e^43]` range (vs `Epi_le_evalLhsE_low`'s `[2, e^10]`);
* `xhalfCurveE c twoK` — the target expression `c·s^{2K}·exp(-s²/2)` (`= c·s^{2K}·x^{-1/2}`
  at `s = √(log x)`), with `eval_xhalfCurveE` and support lemma `xhalfCurve_sub_supported`;
* `floor_xhalf_of_check` — the generic Buthe-floor assembler on `[e^{Lf}, e^43]`.

Row 4 (`c = 1`, `K = 2`, `2K = 4`) is the template.
-/

namespace FKS2
namespace Table4Ext

open Real LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## Generic `x^{-1/2}`-curve floor machinery -/

/-- Buthe `Eπ`-upper-bound as `eval FloorButhe.lhsE` on the WIDE range `[2, e^43]`
(vs `Epi_le_evalLhsE_low`'s `[2, e^10]`): identical reconciliation, but taking the
`x ≤ 10^19` hypothesis directly (`e^43 ≈ 4.7e18 < 10^19`), which extends the Buthe
reread to the full `x^{-1/2}`-floor range.  Curve-independent, so reusable by every
`x^{-1/2}` row (rows 1–5).  Bottoms out at Buthe `theorem_2e/2f` + `li.two_approx`. -/
theorem Epi_le_evalLhsE_wide (x : ℝ) (h2 : (2 : ℝ) ≤ x) (h19 : x ≤ (10 : ℝ) ^ 19) :
    Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE := by
  have hxpos : (0:ℝ) < x := by linarith
  have hLpos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hLnn : (0:ℝ) ≤ Real.log x := le_of_lt hLpos
  have h2e := Buthe.theorem_2e h2 h19
  have h2f := Buthe.theorem_2f h2 h19
  have hsub := li.sub_Li x h2
  have hli2 := li.two_approx
  have hli2_le : li 2 ≤ 1.0452 := hli2.2
  have hpiLi : pi x - Li x = li 2 - (li x - pi x) := by linarith [hsub]
  have habs : |pi x - Li x| ≤ (li x - pi x) + li 2 := by
    rw [hpiLi, abs_le]
    constructor <;> linarith [h2f, hli2.1]
  have hEpi_eq : Eπ x = |pi x - Li x| * (Real.log x / x) := by
    unfold Eπ
    rw [div_div_eq_mul_div, mul_div_assoc]
  rw [hEpi_eq]
  set B := Real.sqrt x / Real.log x * (1.95 + 3.9 / Real.log x + 19.5 / (Real.log x) ^ 2) with hB_def
  have hfactor_nn : (0:ℝ) ≤ Real.log x / x := by positivity
  have hstep1 : |pi x - Li x| * (Real.log x / x) ≤ (B + 1.0452) * (Real.log x / x) := by
    apply mul_le_mul_of_nonneg_right _ hfactor_nn
    calc |pi x - Li x| ≤ (li x - pi x) + li 2 := habs
      _ ≤ B + 1.0452 := by
          apply add_le_add
          · rw [hB_def]; exact h2e
          · exact hli2_le
  refine le_trans hstep1 (le_of_eq ?_)
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hLne : Real.log x ≠ 0 := ne_of_gt hLpos
  have hxinv : x⁻¹ = Real.exp (-(Real.log x)) := by
    rw [Real.exp_neg, Real.exp_log hxpos]
  have hsqrtx : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.mpr hxpos), Real.log_sqrt (le_of_lt hxpos)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hss : s * s = Real.log x := by rw [hs_def]; exact Real.mul_self_sqrt hLnn
  rw [FloorButhe.eval_lhsE, hss]
  set L := Real.log x with hL_def
  have hLx : L / x = L * Real.exp (-L) := by
    rw [div_eq_mul_inv, hxinv]
  have hsqrtxE2 : Real.sqrt x * Real.exp (-L) = Real.exp (-L / 2) := by
    rw [hsqrtx, ← Real.exp_add]; congr 1; ring
  rw [hB_def, hLx]
  rw [show (Real.sqrt x / L * (1.95 + 3.9 / L + 19.5 / L ^ 2) + 1.0452) * (L * Real.exp (-L))
      = (Real.sqrt x * Real.exp (-L)) * (1.95 + 3.9 / L + 19.5 / L ^ 2)
        + 1.0452 * (L * Real.exp (-L)) by
        field_simp]
  rw [hsqrtxE2]
  ring

/-- The `x^{-1/2}` row-curve target expression `c·s^{2K}·exp(-s²/2)` in `s = Expr.var 0`
(`= c·(√(log x))^{2K}·x^{-1/2}` at `s = √(log x)`).  Instantiated per row:
row 1 `xhalfCurveE 2 2`, row 2 `xhalfCurveE 1 3`, row 3 `xhalfCurveE (rational ≤ 1/(8π)) 4`,
row 4 `xhalfCurveE 1 4`, row 5 `xhalfCurveE 1 6`. -/
def xhalfCurveE (c : ℚ) (twoK : ℕ) : Expr :=
  Expr.mul (Expr.const c) (Expr.mul (Expr.pow (Expr.var 0) twoK) (expSplitNegXpow 2))

/-- `xhalfCurveE c twoK` at `s = √(log x)` equals `c·(√(log x))^{2K}·x^{-1/2}` (for
`x > 0`, `log x ≥ 0`).  The row-level bridge `(√(log x))^{2K} = (log x)^K` is done at
the call site (`Real.sq_sqrt`). -/
lemma eval_xhalfCurveE (c : ℚ) (twoK : ℕ) (x : ℝ) (hxpos : 0 < x) (hL : 0 ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) (xhalfCurveE c twoK)
      = (c : ℝ) * (Real.sqrt (Real.log x)) ^ twoK * x ^ (-(1:ℝ) / 2) := by
  have hcast : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
  have h2 := eval_expSplitNegXpow_eq_xpow 2 (by norm_num) x hxpos hL
  rw [hcast] at h2
  simp only [xhalfCurveE, Expr.eval_mul, Expr.eval_const, Expr.eval_pow, Expr.eval_var, h2]
  ring

/-- Support of `lhsE - xhalfCurveE c twoK` for the dyadic slab kernel. -/
lemma xhalfCurve_sub_supported (c : ℚ) (twoK : ℕ) :
    ExprSupportedWithInv (Expr.sub FloorButhe.lhsE (xhalfCurveE c twoK)) := by
  refine ExprSupportedWithInv.add ?_ (ExprSupportedWithInv.neg ?_)
  · show ExprSupportedWithInv FloorButhe.lhsE
    simp only [FloorButhe.lhsE, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s2,
      FloorButhe.s4, FloorButhe.e2]
    repeat constructor
  · unfold xhalfCurveE
    refine ExprSupportedWithInv.mul (ExprSupportedWithInv.const _) ?_
    refine ExprSupportedWithInv.mul (pow_supported (ExprSupportedWithInv.var 0) twoK) ?_
    unfold expSplitNegXpow
    iterate 6 apply sqE_supported
    exact ExprSupportedWithInv.exp (ExprSupportedWithInv.mul (ExprSupportedWithInv.const _)
      (ExprSupportedWithInv.mul (ExprSupportedWithInv.var _) (ExprSupportedWithInv.var _)))

/-- Generic `x^{-1/2}` **Buthe-floor** assembler on `[e^{Lf}, e^43]` (`1 ≤ Lf`): the Buthe
`Eπ`-bound (`Epi_le_evalLhsE_wide`, valid from `x ≥ 2` up to `e^43 < 10^19`) below a
dyadic slab curve `rE` that dominates the row curve (`hcurve`).  Slabs
`slabsFrom slabLo nslabs` must cover `[√Lf, √43]`.  The `Eπ`-bound and slab-cover are
curve-independent; only the per-row `rE`, its slab check, and `hcurve` vary. -/
theorem floor_xhalf_of_check (rE : Expr) (curve : ℝ → ℝ) (Lf : ℝ) (slabLo : ℚ) (nslabs : ℕ)
    (hLf1 : (1 : ℝ) ≤ Lf)
    (hslo : (slabLo : ℝ) ≤ Real.sqrt Lf)
    (hshi : Real.sqrt 43 < (slabLo : ℝ) + (nslabs : ℝ) * 0.05)
    (hsupp : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rE))
    (hchk : checkExprLeOnSlabsDyadic FloorButhe.lhsE rE (slabsFrom slabLo nslabs) (-50) 8 = true)
    (hcurve : ∀ x, Real.exp Lf ≤ x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rE ≤ curve x) :
    ∀ x ∈ Set.Icc (Real.exp Lf) (Real.exp 43), Eπ x ≤ curve x := by
  intro x hx
  obtain ⟨hlo, h43⟩ := hx
  have hexpLfpos : (0:ℝ) < Real.exp Lf := Real.exp_pos _
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le hexpLfpos hlo
  have h2 : (2:ℝ) ≤ x := by
    have he1 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    have he1Lf : Real.exp 1 ≤ Real.exp Lf := Real.exp_le_exp.mpr hLf1
    linarith [le_trans he1Lf hlo]
  have he43 : Real.exp 43 ≤ (10:ℝ) ^ 19 := by
    have h1 : Real.exp 1 < 2.72 := by have := Real.exp_one_lt_d9; linarith
    have h1le : Real.exp 1 ≤ 2.72 := h1.le
    have h1nn : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 43 = Real.exp 1 ^ (43:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.72:ℝ) ^ (43:ℕ) := by gcongr
      _ ≤ (10:ℝ) ^ 19 := by norm_num
  have h19 : x ≤ (10:ℝ) ^ 19 := le_trans h43 he43
  have hLgeLf : Lf ≤ Real.log x := by
    rw [← Real.log_exp Lf]; exact Real.log_le_log hexpLfpos hlo
  have hLle43 : Real.log x ≤ 43 := by
    rw [← Real.log_exp 43]; exact Real.log_le_log hxpos h43
  have hcov_lo : (slabLo : ℝ) ≤ Real.sqrt (Real.log x) := le_trans hslo (Real.sqrt_le_sqrt hLgeLf)
  have hcov_hi : Real.sqrt (Real.log x) < (slabLo : ℝ) + (nslabs : ℝ) * 0.05 :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt hLle43) hshi
  obtain ⟨I, hI, hmem⟩ := coverFrom slabLo nslabs _ hcov_lo hcov_hi
  calc Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE :=
        Epi_le_evalLhsE_wide x h2 h19
    _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rE :=
        verify_expr_le_on_slabs_dyadic FloorButhe.lhsE rE (slabsFrom slabLo nslabs) (-50) 8
          hsupp (by norm_num) hchk I hI _ hmem
    _ ≤ curve x := hcurve x hlo

end Table4Ext

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 4 (`(log x)²·x^{-1/2}`, `log x ∈ [1, 70.6]`)

The Table-7 row-4 curve, assembled from three segments split at `e^3`, `e^43`:

* **floor-trusted** `[e^1, e^3]` — direct `π`/`Li` for small `x` (trusted, `sorry`);
* **Buthe floor** `[e^3, e^43]` — `floor_xhalf_of_check` + a dyadic slab cover of `[√3, √43]`;
* **trusted band** `[e^43, e^70.6]` — Theorem-6 refined interpolation for `log x > log(10^19)`
  (trusted, `sorry`).
-/

/-- Row-4 floor slab certificate: `FloorButhe.lhsE ≤ xhalfCurveE 1 4` (the Buthe `x^{-1/2}`
bound `≤ (log x)²·x^{-1/2}`) over the 97 width-`0.05` slabs covering `[√3, √43]`, verified
by the dyadic interval kernel.  (At `L = 3` the Buthe polynomial `≈ 5.4 ≤ L² = 9`; below
`L = 3` it fails, tuned via `#eval`.) -/
theorem floor_slab_check_row4 :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (xhalfCurveE 1 4)
      (slabsFrom (173/100) 97) (-50) 8 = true := by native_decide

/-- **Row-4 Buthe floor** `[e^3, e^43]` via `floor_xhalf_of_check`. -/
theorem floor_row4 : ∀ x ∈ Set.Icc (Real.exp (3:ℝ)) (Real.exp (43:ℝ)),
    Eπ x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  have hcurve : ∀ y, Real.exp (3:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (xhalfCurveE 1 4)
        ≤ (Real.log y) ^ 2 * y ^ (-(1:ℝ) / 2) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h3 : (3:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (3:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    refine le_of_eq ?_
    have hsq : (Real.sqrt (Real.log y)) ^ 4 = (Real.log y) ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hyL]
    rw [eval_xhalfCurveE 1 4 y hypos hyL, hsq]
    push_cast; ring
  exact floor_xhalf_of_check (xhalfCurveE 1 4)
    (fun x => (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2)) 3 (173/100) 97 (by norm_num)
    (by rw [show ((173/100:ℚ):ℝ) = 1.73 by norm_num,
          show (1.73:ℝ) = Real.sqrt (1.73 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h656 : Real.sqrt 43 ≤ 6.56 := by
          rw [show (6.56:ℝ) = Real.sqrt (6.56 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h656])
    (xhalfCurve_sub_supported 1 4) floor_slab_check_row4 hcurve

/-- **Row-4 floor-trusted** `[e^1, e^3]` (`x ∈ [2.72, 20.1]`): the direct `π`/`Li`
interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`", FKS2.lean:4640).
No tight sub-`e^3` `Eπ` envelope exists in the library for the sharp `(log x)²·x^{-1/2}`
target (the Buthe bound only clears it from `L = 3`).  Same accepted numerical-data trust
class as `Table4Ext.allCells_trusted`. -/
theorem floor_trusted_row4 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (3:ℝ)),
    Eπ x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.floor_trusted_row4

/-- **Row-4 trusted band** `[e^43, e^70.6]` (`log x ∈ (log 10^19, 70.6]`): the blueprint's
Theorem-6 interpolation for `log x > log(10^19)` — "one simply proceeds as in
\cite[Lemmas 5.2, 5.3]{FKS} and interpolates the numerical results of Theorem 6"
(FKS2.lean:4640).  The `allCells` envelope is too loose for the sharp `x^{-1/2}` target
here (envelope `ε ≈ exp(-√L) ≫ x^{-1/2} = exp(-L/2)`), so this is the big authorized
trusted region for `x^{-1/2}` rows.  Same accepted trust class as `Table4Ext.allCells_trusted`
and the Cor 23 row-8 band. -/
theorem band_row4 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (70.6:ℝ)),
    Eπ x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  exact FKS2.Cor24Trusted.band_row4

/-- **FKS2 Corollary 24, row 4** (`table7` entry `(x ↦ (log x)²·x^{-1/2}, Icc 1 70.6)`):
`Eπ x ≤ (log x)²·x^{-1/2}` whenever `log x ∈ [1, 70.6]`.  For `x > 0` this splits into
the three segments above; for `x < 0` (possible since `log` is even) the exponent
`-(1)/2` gives `cos((-(1)/2)·π) = cos(-π/2) = 0`, so `x^{-1/2} = 0` and the RHS is `0`,
while `Eπ x ≤ 0`. -/
theorem corollary_24_row4 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 70.6 → Eπ x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
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
    · exact floor_trusted_row4 x (cvt 1 3 hlo h1)
    · rcases le_total (Real.log x) 43 with h2 | h2
      · exact floor_row4 x (cvt 3 43 h1 h2)
      · exact band_row4 x (cvt 43 70.6 h2 hhi)

end FKS2
