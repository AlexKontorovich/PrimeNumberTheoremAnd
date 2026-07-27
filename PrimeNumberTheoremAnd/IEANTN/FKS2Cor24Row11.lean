import PrimeNumberTheoremAnd.IEANTN.FKS2Cor24
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4Ext

/-!
# FKS2 Corollary 24 — row 11 (`x^{-1/100}`) mid-range envelope

Machinery certifying the row-11 Table-7 curve `x^{-1/n}` (here `n = 100`) over
the `allCells` numerical envelope of the extended ancillary Table 4.

* `cell_Epi_le_xpow` — the mathematical transport: a cell whose trusted table
  value `ε` satisfies `ε ≤ exp(-b'/n)` yields `Eπ x ≤ x^{-1/n}` on `[e^b, e^b']`.
* `checkXpowCell` / `checkXpowCell_sound` — a per-cell boolean certificate for
  the numeric hypothesis `ε ≤ exp(-b'/n)`, discharged by the dyadic interval
  kernel and mirroring `checkCell` / `cell_eps_le_admissible`.

The check certifies the *large-value* form `exp(s²/n) ≤ 1/ε` on the slab
`s ∈ [slo, shi]` (`s² = log x ∈ [b, b']`); `exp(s²/n)` is increasing, so its max
is at `s = shi` (`s² = shi² ≥ b'`), giving `exp(b'/n) ≤ exp(shi²/n) ≤ 1/ε`,
i.e. `ε ≤ exp(-b'/n)`.  Keeping the `exp` on the large side (`1/ε` rather than
the tiny `ε`) is what lets the dyadic grid resolve the ≈0.1% margins near the top
of row 11.

`sampleCells_checkXpow` validates the check on a 40-cell sample and
`boundaryCell_fails` records that the first excluded cell `[3756,3757]` fails, so
the row-11 envelope certifies exactly `allCells.take 3746` (cells with `b' ≤ 3756`).

The row-11 curve `corollary_24_row11 : ∀ x, log x ∈ [1, 3757.6] → Eπ x ≤ x^{-1/100}`
is assembled from four segments split at `e^3.5`, `e^10`, `e^3756`:
* **floor-trusted** `[e^1, e^3.5]` (`floor_trusted_row11`, trusted `sorry`);
* **floor (Buthe)** `[e^3.5, e^10]` (`floor_row11`, dyadic slab cover);
* **mid (envelope)** `[e^10, e^3756]` (`mid_row11`, `allCells.take 3746`);
* **sliver** `[e^3756, e^3757.6]` (`sliver_row11`, trusted `sorry`).

The generic helpers `expSplitNegXpow`, `Epi_le_evalLhsE_low`, `floor_xpow_of_check`
and `mid_xpow_of` are `n`-parameterized for reuse by row 10 (`n = 50`).
-/

namespace FKS2
namespace Table4Ext

open Real LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-- Transport: a checked cell dominated by the table value `eps`, with the
per-cell numeric certificate `eps ≤ exp(-b'/n)`, gives the row-`n` curve
`x^{-1/n}` bound for `Eπ` on the whole cell `[exp b, exp b']`. -/
theorem cell_Epi_le_xpow (n : ℕ) (hn : 0 < n) (c : Cell)
    (htrust : Eπ.bound (c.eps : ℝ) (Real.exp (c.b : ℝ)))
    (hnum : (c.eps : ℝ) ≤ Real.exp (-(c.b' : ℝ) / n)) :
    ∀ x ∈ Set.Icc (Real.exp (c.b : ℝ)) (Real.exp (c.b' : ℝ)),
      Eπ x ≤ x ^ (-(1 : ℝ) / n) := by
  intro x hx
  obtain ⟨hx_lo, hx_hi⟩ := hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx_lo
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- Eπ x ≤ eps
  have h1 : Eπ x ≤ (c.eps : ℝ) := htrust x hx_lo
  -- log x ≤ b'
  have hlogle : Real.log x ≤ (c.b' : ℝ) := (Real.log_le_iff_le_exp hxpos).mpr hx_hi
  -- x^(-1/n) = exp(-(log x)/n)
  have hxrpow : x ^ (-(1 : ℝ) / n) = Real.exp (-(Real.log x) / n) := by
    rw [Real.rpow_def_of_pos hxpos]
    congr 1
    ring
  -- monotonicity: exp(-b'/n) ≤ exp(-(log x)/n)
  have hmono : Real.exp (-(c.b' : ℝ) / n) ≤ Real.exp (-(Real.log x) / n) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    gcongr
  rw [hxrpow]
  calc Eπ x ≤ (c.eps : ℝ) := h1
    _ ≤ Real.exp (-(c.b' : ℝ) / n) := hnum
    _ ≤ Real.exp (-(Real.log x) / n) := hmono

/-! ## Per-cell numeric certificate `eps ≤ exp(-b'/n)` via the dyadic kernel -/

/-- `1/(64·n)`, the split-exp kernel coefficient for the row-`n` curve. -/
def xpowCoef (n : ℕ) : ℚ := 1 / (64 * n)

/-- `(exp ((1/(64n))·s²))^64` as an expression in `s = Expr.var 0`.  The `^64`
split keeps the `exp` argument order-one for the dyadic kernel. -/
def expSplitXpow (n : ℕ) : Expr :=
  sqE (sqE (sqE (sqE (sqE (sqE
    (Expr.exp (Expr.mul (Expr.const (xpowCoef n))
      (Expr.mul (Expr.var 0) (Expr.var 0)))))))))

lemma sqE_supported {e : Expr} (h : ExprSupportedWithInv e) :
    ExprSupportedWithInv (sqE e) := ExprSupportedWithInv.mul h h

lemma expSplitXpow_supported (n : ℕ) (q : ℚ) :
    ExprSupportedWithInv (Expr.sub (expSplitXpow n) (Expr.const q)) := by
  refine ExprSupportedWithInv.add ?_ (ExprSupportedWithInv.neg (ExprSupportedWithInv.const _))
  unfold expSplitXpow
  iterate 6 apply sqE_supported
  exact ExprSupportedWithInv.exp (ExprSupportedWithInv.mul (ExprSupportedWithInv.const _)
    (ExprSupportedWithInv.mul (ExprSupportedWithInv.var _) (ExprSupportedWithInv.var _)))

lemma eval_expSplitXpow (n : ℕ) (s : ℝ) :
    Expr.eval (fun _ => s) (expSplitXpow n)
      = exp ((xpowCoef n : ℝ) * (s * s)) ^ (64 : ℕ) := by
  simp only [expSplitXpow, eval_sqE, Expr.eval_exp, Expr.eval_mul,
    Expr.eval_const, Expr.eval_var, ← pow_mul]

/-- Boolean verification that the row-`n` curve `x^{-1/n}` dominates the table
value `eps` on one cell: side conditions plus the dyadic slab check of
`exp(s²/n) ≤ 1/eps` on `[slo, shi]`. -/
def checkXpowCell (n : ℕ) (c : Cell) : Bool :=
  if h : c.slo ≤ c.shi then
    decide (0 < c.eps) && decide (0 ≤ c.slo) &&
    decide (c.slo * c.slo ≤ (c.b : ℚ)) &&
    decide ((c.b' : ℚ) ≤ c.shi * c.shi) &&
    checkExprLeOnIntervalDyadic (expSplitXpow n) (Expr.const (1 / c.eps))
      ⟨c.slo, c.shi, h⟩ (-50) 8
  else false

set_option maxHeartbeats 1000000 in
-- One long transport declaration; each step is cheap but the default budget is
-- exceeded cumulatively (mirrors `cell_eps_le_admissible`).
/-- Soundness: a checked cell obeys `eps ≤ exp(-b'/n)`. -/
theorem checkXpowCell_sound (n : ℕ) (hn : 0 < n) (c : Cell)
    (hc : checkXpowCell n c = true) :
    (c.eps : ℝ) ≤ Real.exp (-(c.b' : ℝ) / n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold checkXpowCell at hc
  split at hc
  case isFalse => simp at hc
  case isTrue hle =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨heps, _hslo0⟩, _hslo⟩, hshi⟩, hcheck⟩ := hc
    -- semantic slab inequality: exp(s²/n) ≤ 1/eps on [slo, shi]
    have hslab := verify_expr_le_on_interval_dyadic (expSplitXpow n)
      (Expr.const (1 / c.eps)) ⟨c.slo, c.shi, hle⟩ (-50) 8
      (expSplitXpow_supported _ _) (by norm_num) hcheck
    -- instantiate at s = shi (the right endpoint, where exp(s²/n) is largest)
    have hshi_mem : (c.shi : ℝ) ∈ Set.Icc ((c.slo : ℝ)) ((c.shi : ℝ)) :=
      ⟨by exact_mod_cast hle, le_refl _⟩
    have hineq := hslab (c.shi : ℝ) hshi_mem
    rw [eval_expSplitXpow, Expr.eval_const] at hineq
    -- (exp ((1/64n)·shi²))^64 = exp(shi²/n)
    have hn' : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have harg : ((64 : ℕ) : ℝ) * ((xpowCoef n : ℝ) * ((c.shi : ℝ) * (c.shi : ℝ)))
        = ((c.shi : ℝ) * (c.shi : ℝ)) / n := by
      simp only [xpowCoef]; push_cast; field_simp
    have hexp64 :
        exp ((xpowCoef n : ℝ) * ((c.shi : ℝ) * (c.shi : ℝ))) ^ (64 : ℕ)
          = exp (((c.shi : ℝ) * (c.shi : ℝ)) / n) := by
      rw [← Real.exp_nat_mul, harg]
    rw [hexp64] at hineq
    -- 1/eps on the RHS as a real reciprocal
    have hrhs : ((1 / c.eps : ℚ) : ℝ) = 1 / (c.eps : ℝ) := by push_cast; ring
    rw [hrhs] at hineq
    -- positivity facts and the b' ≤ shi² side condition
    have hepsR : (0 : ℝ) < (c.eps : ℝ) := by exact_mod_cast heps
    have hbshi : (c.b' : ℝ) ≤ (c.shi : ℝ) * (c.shi : ℝ) := by exact_mod_cast hshi
    have hexppos : (0 : ℝ) < exp ((c.b' : ℝ) / n) := Real.exp_pos _
    -- exp(b'/n) ≤ exp(shi²/n) ≤ 1/eps
    have hmono2 : exp ((c.b' : ℝ) / n) ≤ exp (((c.shi : ℝ) * (c.shi : ℝ)) / n) := by
      apply Real.exp_le_exp.mpr
      gcongr
    have hchain : exp ((c.b' : ℝ) / n) ≤ 1 / (c.eps : ℝ) := le_trans hmono2 hineq
    -- eps ≤ exp(-b'/n)
    rw [neg_div, Real.exp_neg, ← one_div, le_div_iff₀ hexppos]
    have hmul : exp ((c.b' : ℝ) / n) * (c.eps : ℝ) ≤ 1 :=
      (le_div_iff₀ hepsR).mp hchain
    linarith [hmul]

/-- A checked cell together with its trusted row bound gives the row-`n` curve
`x^{-1/n}` bound for `Eπ` on the cell. -/
theorem cell_Epi_le_xpow_of_check (n : ℕ) (hn : 0 < n) (c : Cell)
    (hc : checkXpowCell n c = true)
    (hrow : Eπ.bound (c.eps : ℝ) (exp (c.b : ℝ))) :
    ∀ x ∈ Set.Icc (exp (c.b : ℝ)) (exp (c.b' : ℝ)),
      Eπ x ≤ x ^ (-(1 : ℝ) / n) :=
  cell_Epi_le_xpow n hn c hrow (checkXpowCell_sound n hn c hc)

/-! ## POC validation on a sample sublist (`n = 100`) -/

/-- POC sample for row 11 (`n = 100`): 20 easy low-`L` cells (`b = 10..29`) plus
20 tight cells (`b = 3736..3755`) running up to the last passing cell
`[3755, 3756]`. -/
def sampleCells : List Cell := allCells.take 20 ++ (allCells.drop 3726).take 20

/-- Every sampled cell passes the row-11 numeric check. -/
theorem sampleCells_checkXpow :
    sampleCells.all (fun c => checkXpowCell 100 c) = true := by native_decide

/-- Boundary witness: the first cell past the mid-range, `[3756, 3757]`, fails
the check (its table value exceeds `exp(-3757/100)` by ≈0.24%). -/
theorem boundaryCell_fails :
    ((allCells.drop 3746).take 1).all (fun c => checkXpowCell 100 c) = false := by
  native_decide

/-! ## Generic `x^{-1/n}` floor and mid assemblers (reusable for row 10, `n = 50`)

These promote the row-independent plumbing: a negative-exponent split target
expression, the Buthe `Eπ`-bound reread on the low range `[2, e^10]`, and the
floor / mid assemblers, all parameterized by `n`.  Row 11 instantiates `n = 100`;
row 10 will instantiate `n = 50` with its own `native_decide`s. -/

/-- Negative-exponent split expression `(exp (-(1/(64n))·s²))^64 = exp(-s²/n)`,
i.e. the `x^{-1/n}` floor-curve target (the sign-flipped companion of the
large-value `expSplitXpow`). -/
def expSplitNegXpow (n : ℕ) : Expr :=
  sqE (sqE (sqE (sqE (sqE (sqE
    (Expr.exp (Expr.mul (Expr.const (-(xpowCoef n)))
      (Expr.mul (Expr.var 0) (Expr.var 0)))))))))

/-- `expSplitNegXpow n` evaluated at `s = √(log x)` is exactly `x^{-1/n}`
(for `x > 0`, `log x ≥ 0`). -/
lemma eval_expSplitNegXpow_eq_xpow (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hxpos : 0 < x) (hL : 0 ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) (expSplitNegXpow n) = x ^ (-(1:ℝ)/n) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have hss : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hL
  simp only [expSplitNegXpow, eval_sqE, Expr.eval_exp, Expr.eval_mul, Expr.eval_const,
    Expr.eval_var, ← pow_mul]
  rw [← Real.exp_nat_mul, hss, Real.rpow_def_of_pos hxpos]
  congr 1
  simp only [xpowCoef]
  push_cast
  field_simp

/-- Support of `lhsE - expSplitNegXpow n` for the dyadic slab kernel. -/
lemma lhsE_sub_negxpow_supported (n : ℕ) :
    ExprSupportedWithInv (Expr.sub FloorButhe.lhsE (expSplitNegXpow n)) := by
  refine ExprSupportedWithInv.add ?_ (ExprSupportedWithInv.neg ?_)
  · show ExprSupportedWithInv FloorButhe.lhsE
    simp only [FloorButhe.lhsE, FloorButhe.pow8, FloorButhe.sqx, FloorButhe.s2,
      FloorButhe.s4, FloorButhe.e2]
    repeat constructor
  · unfold expSplitNegXpow
    iterate 6 apply sqE_supported
    exact ExprSupportedWithInv.exp (ExprSupportedWithInv.mul (ExprSupportedWithInv.const _)
      (ExprSupportedWithInv.mul (ExprSupportedWithInv.var _) (ExprSupportedWithInv.var _)))

/-- Buthe `Eπ`-upper-bound as `eval_lhsE` on the LOW range `[2, e^10]` (vs the
committed `FloorButhe.Epi_le_evalLhsE`'s `[e^5, e^10]`): identical reconciliation,
only the hypothesis is `2 ≤ x`.  Curve-independent (`FloorButhe.lhsE` is the Buthe
`x^{-1/2}` bound), so reusable by every `x^{-1/n}` row floor.  Bottoms out at Buthe
`theorem_2e/2f` + `li.two_approx`. -/
theorem Epi_le_evalLhsE_low (x : ℝ) (h2 : (2 : ℝ) ≤ x) (h10 : x ≤ Real.exp 10) :
    Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE := by
  have hxpos : (0:ℝ) < x := by linarith
  have hLpos : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
  have hLnn : (0:ℝ) ≤ Real.log x := le_of_lt hLpos
  have hx19 : x ≤ 10 ^ 19 := by
    have h2' : Real.exp 10 < (3:ℝ) ^ 10 := by
      calc Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 3 ^ 10 := by
            have h1 := Real.exp_one_lt_d9
            have hlt : Real.exp 1 < 3 := by linarith
            gcongr
    have h3 : (3:ℝ) ^ 10 ≤ 10 ^ 19 := by norm_num
    linarith [h10]
  have h2e := Buthe.theorem_2e h2 hx19
  have h2f := Buthe.theorem_2f h2 hx19
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

/-- Generic `x^{-1/n}` floor assembler on `[e^Lf, e^10]` (`1 ≤ Lf`): the Buthe
`Eπ`-bound (`Epi_le_evalLhsE_low`, valid from `x ≥ 2`) below a dyadic slab curve
`rE` that dominates `x^{-1/n}` (`hcurve`).  Slabs `slabsFrom slabLo nslabs` must
cover `[√Lf, √10]`.  The `Eπ`-bound and slab-cover are curve-independent; only the
per-row `rE`, its slab check, and `hcurve` vary. -/
theorem floor_xpow_of_check (rE : Expr) (n : ℕ) (Lf : ℝ) (slabLo : ℚ) (nslabs : ℕ)
    (hLf1 : (1 : ℝ) ≤ Lf)
    (hslo : (slabLo : ℝ) ≤ Real.sqrt Lf)
    (hshi : Real.sqrt 10 < (slabLo : ℝ) + (nslabs : ℝ) * 0.05)
    (hsupp : ExprSupportedWithInv (Expr.sub FloorButhe.lhsE rE))
    (hchk : checkExprLeOnSlabsDyadic FloorButhe.lhsE rE (slabsFrom slabLo nslabs) (-50) 8 = true)
    (hcurve : ∀ x, Real.exp Lf ≤ x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rE ≤ x ^ (-(1 : ℝ) / n)) :
    ∀ x ∈ Set.Icc (Real.exp Lf) (Real.exp 10), Eπ x ≤ x ^ (-(1:ℝ)/n) := by
  intro x hx
  obtain ⟨hlo, h10⟩ := hx
  have hexpLfpos : (0:ℝ) < Real.exp Lf := Real.exp_pos _
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le hexpLfpos hlo
  have h2 : (2:ℝ) ≤ x := by
    have he1 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    have he1Lf : Real.exp 1 ≤ Real.exp Lf := Real.exp_le_exp.mpr hLf1
    linarith [le_trans he1Lf hlo]
  have hLgeLf : Lf ≤ Real.log x := by
    rw [← Real.log_exp Lf]; exact Real.log_le_log hexpLfpos hlo
  have hLle10 : Real.log x ≤ 10 := by
    rw [← Real.log_exp 10]; exact Real.log_le_log hxpos h10
  have hcov_lo : (slabLo:ℝ) ≤ Real.sqrt (Real.log x) := le_trans hslo (Real.sqrt_le_sqrt hLgeLf)
  have hcov_hi : Real.sqrt (Real.log x) < (slabLo:ℝ) + (nslabs:ℝ) * 0.05 :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt hLle10) hshi
  obtain ⟨I, hI, hmem⟩ := coverFrom slabLo nslabs _ hcov_lo hcov_hi
  calc Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE :=
        Epi_le_evalLhsE_low x h2 h10
    _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rE :=
        verify_expr_le_on_slabs_dyadic FloorButhe.lhsE rE (slabsFrom slabLo nslabs) (-50) 8
          hsupp (by norm_num) hchk I hI _ hmem
    _ ≤ x ^ (-(1:ℝ)/n) := hcurve x hlo

/-- Generic `x^{-1/n}` mid assembler: over the `allCells` prefix `take k` (chained
from `10` to `m`, every cell passing the row-`n` `checkXpowCell`), `Eπ ≤ x^{-1/n}`
on `[e^10, e^m]`.  Uses `cover_of_chainOk` + `cell_Epi_le_xpow_of_check` +
`allCells_trusted`.  Row 11: `k = 3746, m = 3756`. -/
theorem mid_xpow_of (n : ℕ) (hn : 0 < n) (k m : ℕ)
    (hchain : chainOk 10 (allCells.take k) = true)
    (hne : allCells.take k ≠ [])
    (hlast : lastB 10 (allCells.take k) = m)
    (hall : (allCells.take k).all (fun c => checkXpowCell n c) = true) :
    ∀ x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp (m:ℝ)), Eπ x ≤ x ^ (-(1:ℝ)/n) := by
  intro x hx
  have hx_lo : Real.exp ((10:ℕ):ℝ) ≤ x := by simpa using hx.1
  have hx_hi : x ≤ Real.exp ((lastB 10 (allCells.take k) : ℕ):ℝ) := by
    rw [hlast]; exact hx.2
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk (allCells.take k) 10 hne hchain hx_lo hx_hi
  have hck : checkXpowCell n c = true := List.all_eq_true.mp hall c hcmem
  exact cell_Epi_le_xpow_of_check n hn c hck
    (allCells_trusted c (List.mem_of_mem_take hcmem)) x hcx

end Table4Ext

open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

set_option linter.style.nativeDecide false

/-! ## FKS2 Corollary 24, row 11 (`x^{-1/100}`, `log x ∈ [1, 3757.6]`)

The Table-7 row-11 curve, assembled from four segments split at `e^3.5`, `e^10`,
`e^3756`:

* **floor-trusted** `[e^1, e^3.5]` — direct `π`/`Li` for small `x` (trusted, `sorry`);
* **floor (Buthe)** `[e^3.5, e^10]` — `floor_xpow_of_check` + dyadic slab cover;
* **mid (envelope)** `[e^10, e^3756]` — `mid_xpow_of` over the certified `allCells`
  prefix `take 3746`;
* **sliver** `[e^3756, e^3757.6]` — Theorem-6 refined interpolation near the
  threshold (trusted, `sorry`).
-/

/-- The row-11 (`n = 100`) certified prefix of `allCells`: the first `3746` cells
(`b' ≤ 3756`) form a contiguous chain from `b = 10` to `b' = 3756`; the next cell
`[3756, 3757]` fails (`boundaryCell_fails`). -/
theorem midCells_chain : chainOk 10 (allCells.take 3746) = true := by native_decide

theorem midCells_ne_nil : allCells.take 3746 ≠ [] := by native_decide

theorem midCells_last : lastB 10 (allCells.take 3746) = 3756 := by native_decide

/-- Every cell of the row-11 passing prefix satisfies the `n = 100` numeric
certificate `exp(s²/100) ≤ 1/ε`, verified by the dyadic interval kernel over all
`3746` cells. -/
theorem allCells_take_checkXpow :
    (allCells.take 3746).all (fun c => checkXpowCell 100 c) = true := by native_decide

/-- **Row-11 mid** `[e^10, e^3756]` via the certified envelope prefix. -/
theorem mid_row11 : ∀ x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp (3756:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/100) := by
  intro x hx
  have hmem : x ∈ Set.Icc (Real.exp (10:ℝ)) (Real.exp ((3756:ℕ):ℝ)) := by
    refine ⟨hx.1, ?_⟩
    rw [show ((3756:ℕ):ℝ) = (3756:ℝ) from by norm_num]; exact hx.2
  have h := mid_xpow_of 100 (by norm_num) 3746 3756
    midCells_chain midCells_ne_nil midCells_last allCells_take_checkXpow x hmem
  simpa using h

/-- Row-11 floor slab certificate: `lhsE ≤ expSplitNegXpow 100` (the Buthe
`x^{-1/2}` bound `≤ x^{-1/100}`) over the 26 width-`0.05` slabs covering
`[√3.5, √10]`, verified by the dyadic interval kernel. -/
theorem floor_slab_check :
    checkExprLeOnSlabsDyadic FloorButhe.lhsE (expSplitNegXpow 100)
      (slabsFrom (187/100) 26) (-50) 8 = true := by native_decide

/-- **Row-11 floor (Buthe)** `[e^3.5, e^10]` via `floor_xpow_of_check`. -/
theorem floor_row11 : ∀ x ∈ Set.Icc (Real.exp (3.5:ℝ)) (Real.exp (10:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/100) := by
  intro x hx
  have hcurve : ∀ y, Real.exp (3.5:ℝ) ≤ y →
      Expr.eval (fun _ => Real.sqrt (Real.log y)) (expSplitNegXpow 100)
        ≤ y ^ (-(1:ℝ)/(100:ℕ)) := by
    intro y hy
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hyL : (0:ℝ) ≤ Real.log y := by
      have h35 : (3.5:ℝ) ≤ Real.log y := by
        rw [← Real.log_exp (3.5:ℝ)]; exact Real.log_le_log (Real.exp_pos _) hy
      linarith
    exact le_of_eq (eval_expSplitNegXpow_eq_xpow 100 (by norm_num) y hypos hyL)
  have h := floor_xpow_of_check (expSplitNegXpow 100) 100 (3.5:ℝ) (187/100) 26 (by norm_num)
    (by rw [show ((187/100:ℚ):ℝ) = 1.87 by norm_num,
          show (1.87:ℝ) = Real.sqrt (1.87^2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h316 : Real.sqrt 10 ≤ 3.163 := by
          rw [show (3.163:ℝ) = Real.sqrt (3.163^2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h316])
    (lhsE_sub_negxpow_supported 100) floor_slab_check hcurve x hx
  simpa using h

/-- **Row-11 floor-trusted** `[e^1, e^3.5]` (`x ∈ [2.72, 33.1]`): the direct
`π`/`Li` interpolation for small `x` that the blueprint proof invokes
(\cite[Lemmas 5.2, 5.3]{FKS}; "checks directly for particularly small `x`",
FKS2.lean:4640).  No tight sub-`e^{3.5}` `Eπ` envelope exists in the library for
the sharp `x^{-1/100}` target (the Buthe bound only clears it from `L ≈ 3.44`).
Same accepted numerical-data trust class as `Table4Ext.allCells_trusted`. -/
theorem floor_trusted_row11 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (3.5:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/100) := by
  exact FKS2.Cor24Trusted.floor_trusted_row11

/-- **Row-11 sliver** `[e^3756, e^3757.6]` (width `≈ 1.6` in `log x`, at the
threshold): the `x^{-1/100}` curve is `≤ 0.6%` above the `allCells` envelope on
this band, resolved in FKS2 by the refined Theorem-6 interpolation (arXiv
2206.12557, §5.2/5.3 / the "more refined collection of values than Table 4",
FKS2.lean:4640).  Same accepted trust class as `Table4Ext.allCells_trusted`. -/
theorem sliver_row11 : ∀ x ∈ Set.Icc (Real.exp (3756:ℝ)) (Real.exp (3757.6:ℝ)),
    Eπ x ≤ x ^ (-(1:ℝ)/100) := by
  exact FKS2.Cor24Trusted.sliver_row11

/-- **FKS2 Corollary 24, row 11** (`table7` entry `(x ↦ x^{-1/100}, Icc 1 3757.6)`):
`Eπ x ≤ x^{-1/100}` whenever `log x ∈ [1, 3757.6]`.  For `x > 0` this splits into
the four segments above; for `x ≤ 0` (possible since `log` is even) `Eπ x ≤ 0 <
x^{-1/100}`. -/
theorem corollary_24_row11 :
    ∀ x, Real.log x ∈ Set.Icc (1:ℝ) 3757.6 → Eπ x ≤ x ^ (-(1:ℝ)/100) := by
  intro x hlog
  obtain ⟨hlo, hhi⟩ := hlog
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · -- x < 0: `Eπ x ≤ 0 < x^{-1/100}`
    have hLpos : (0:ℝ) < Real.log x := by linarith
    have hEle0 : Eπ x ≤ 0 := by
      unfold Eπ
      apply div_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
      exact le_of_lt (div_neg_of_neg_of_pos hxneg hLpos)
    have hRpos : (0:ℝ) < x ^ (-(1:ℝ)/100) := by
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
    rcases le_total (Real.log x) 3.5 with h1 | h1
    · exact floor_trusted_row11 x (cvt 1 3.5 hlo h1)
    · rcases le_total (Real.log x) 10 with h2 | h2
      · exact floor_row11 x (cvt 3.5 10 h1 h2)
      · rcases le_total (Real.log x) 3756 with h3 | h3
        · exact mid_row11 x (cvt 10 3756 h2 h3)
        · exact sliver_row11 x (cvt 3756 3757.6 h3 hhi)

end FKS2
