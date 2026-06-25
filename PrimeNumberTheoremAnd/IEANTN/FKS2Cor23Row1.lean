import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23Row2
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtGenQuarterCore

/-!
# FKS2 Corollary 23 — row 1 `(A=0.000120, B=1/4, C=1, x₀=22.955)`

Last and hardest row.  `B = 1/4` (squaring technique, as row 2) AND threshold
`x₀ = 22.955 > e^10`, so there is no floor below `e^10`; instead the range
`[e^22.955, ∞)` splits as: a near-threshold **trusted boundary** `[e^22.955, e^23.5]`
(tiny `A = 0.000120` makes the curve razor-thin against the Buthe bound right at
the threshold — `~0.85%` margin, below the dyadic kernel's resolution); a Buthe
segment `[e^23.5, e^40]` (margin grows fast, `≥10%`, via `Epi_le_evalLhsE_wide` +
`floor_buthe_quarter_wide`); the envelope mid `[e^40, e^20000]` (the low-`L` cells
fail for tiny `A`, so the cover is RESTRICTED to cells with `b' ≥ 40`); and the
Cor 22 tail `[e^20000, ∞)`.
-/

namespace FKS2
open Real Table4Ext LeanCert.Core LeanCert.ANT.Asymp

/-- Buthe `Eπ`-upper-bound reconciliation over the WIDE range `[e^5, e^40]`
(vs `FloorButhe.Epi_le_evalLhsE`'s `[e^5,e^10]`): identical proof, only the
`x ≤ 10^19` derivation uses `x ≤ e^40` (`e^40 ≈ 2.4e17 < 10^19`).  Needed for
row 1's near-threshold boundary `[e^22.955, e^40]`. -/
theorem Epi_le_evalLhsE_wide (x : ℝ) (h5 : Real.exp 5 ≤ x) (h40 : x ≤ Real.exp 40) :
    Eπ x ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE := by
  have he5 : (2:ℝ) ≤ Real.exp 5 := by
    have := Real.add_one_le_exp (5:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he5 h5
  have hxpos : (0:ℝ) < x := by linarith
  have hLge5 : (5:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 5]; exact Real.log_le_log (Real.exp_pos _) h5
  have hLpos : (0:ℝ) < Real.log x := by linarith
  have hLnn : (0:ℝ) ≤ Real.log x := le_of_lt hLpos
  have hx19 : x ≤ 10 ^ 19 := by
    have h2 : Real.exp 40 ≤ (2.72:ℝ) ^ 40 := by
      have he : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]; gcongr
      linarith [Real.exp_one_lt_d9]
    have h3 : (2.72:ℝ) ^ 40 ≤ 10 ^ 19 := by norm_num
    linarith [h40]
  have h2e := Buthe.theorem_2e hx2 hx19
  have h2f := Buthe.theorem_2f hx2 hx19
  have hsub := li.sub_Li x hx2
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

/-- Wide quarter Buthe floor assembler over `[e^xlo, e^xhi]` (`5 ≤ xlo`, `xhi ≤ 40`),
using `Epi_le_evalLhsE_wide`.  Squared slab check + outside-kernel sqrt, as
`floor_buthe_quarter_of_curve` but with arbitrary upper `xhi` (for row 1's
near-threshold boundary). -/
theorem floor_buthe_quarter_wide (rhsE2 : Expr) (A C : ℝ) (xlo xhi : ℝ) (slabLo : ℚ) (n : ℕ)
    (hApos : 0 < A)
    (hxlo5 : (5:ℝ) ≤ xlo) (hxhi40 : xhi ≤ 40)
    (hslo : (slabLo:ℝ) ≤ Real.sqrt xlo)
    (hshi : Real.sqrt xhi < (slabLo:ℝ) + (n:ℝ) * 0.05)
    (hsupp : ExprSupportedWithInv (Expr.sub (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2))
    (hchk : checkExprLeOnSlabsDyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
        (slabsFrom slabLo n) (-50) 8 = true)
    (hcurve2 : ∀ x, xlo ≤ Real.log x →
        Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2
          ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2) :
    ∀ x ∈ Set.Icc (Real.exp xlo) (Real.exp xhi),
      Eπ x ≤ admissible_bound A 0.25 C 5.5666305 x := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  have h5 : Real.exp 5 ≤ x := le_trans (Real.exp_le_exp.mpr hxlo5) hlo
  have h40 : x ≤ Real.exp 40 := le_trans hhi (Real.exp_le_exp.mpr hxhi40)
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h5
  have hLgexlo : xlo ≤ Real.log x := by
    rw [← Real.log_exp xlo]; exact Real.log_le_log (Real.exp_pos _) hlo
  have hLlexhi : Real.log x ≤ xhi := by
    rw [← Real.log_exp xhi]; exact Real.log_le_log hxpos hhi
  have hLpos : (0:ℝ) < Real.log x := lt_of_lt_of_le (by linarith) hLgexlo
  have hcov_lo : (slabLo:ℝ) ≤ Real.sqrt (Real.log x) :=
    le_trans hslo (Real.sqrt_le_sqrt hLgexlo)
  have hcov_hi : Real.sqrt (Real.log x) < (slabLo:ℝ) + (n:ℝ) * 0.05 :=
    lt_of_le_of_lt (Real.sqrt_le_sqrt hLlexhi) hshi
  obtain ⟨I, hI, hmem⟩ := coverFrom slabLo n _ hcov_lo hcov_hi
  have hslab2 := verify_expr_le_on_slabs_dyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2
    (slabsFrom slabLo n) (-50) 8 hsupp (by norm_num) hchk I hI _ hmem
  rw [Expr.eval_mul] at hslab2
  set Lh := Expr.eval (fun _ => Real.sqrt (Real.log x)) FloorButhe.lhsE with hLh_def
  have hLh_nn : (0:ℝ) ≤ Lh := by
    rw [hLh_def, FloorButhe.eval_lhsE]; positivity
  have hadm_nn : (0:ℝ) ≤ admissible_bound A 0.25 C 5.5666305 x := by
    rw [admissible_quarter_eq A C 5.5666305 x hLpos.le (by norm_num)]; positivity
  have hsq : Lh ^ 2 ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2 := by
    calc Lh ^ 2 = Lh * Lh := sq Lh
      _ ≤ Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2 := hslab2
      _ ≤ (admissible_bound A 0.25 C 5.5666305 x) ^ 2 := hcurve2 x hLgexlo
  have hLh_le : Lh ≤ admissible_bound A 0.25 C 5.5666305 x := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hLh_nn, Real.sqrt_sq hadm_nn] at this
  exact le_trans (Epi_le_evalLhsE_wide x h5 h40) hLh_le

/-- Row-1 squared floor curve `(6103/10⁹)·s·exp(−(8477/10000)s)`. -/
def eR1 : Expr := Expr.exp (Expr.mul (Expr.const (-8477/80000)) (Expr.var 0))
def rhsE2_row1 : Expr :=
  Expr.mul (Expr.const (6102/1000000000000)) (Expr.mul (Expr.var 0) (FloorButhe.pow8 eR1))

theorem eval_rhsE2_row1 (s : ℝ) :
    Expr.eval (fun _ => s) rhsE2_row1 = (6102/1000000000000) * s * Real.exp (-(8477/10000) * s) := by
  have h8 : Real.exp (s * (-8477/80000 : ℝ)) ^ 8 = Real.exp (s * (-8477/10000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [rhsE2_row1, eR1, FloorButhe.pow8, FloorButhe.sqx,
    Expr.eval_mul, Expr.eval_const, Expr.eval_exp, Expr.eval_var]
  push_cast
  ring_nf
  rw [h8]

theorem support1 :
    ExprSupportedWithInv (Expr.sub (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2_row1) := by
  simp only [Expr.sub, rhsE2_row1, eR1, FloorButhe.lhsE, FloorButhe.pow8, FloorButhe.sqx,
    FloorButhe.s2, FloorButhe.s4, FloorButhe.e2]
  repeat constructor

theorem rhsE2_row1_le_sq (x : ℝ) (hL : (22.955 : ℝ) ≤ Real.log x) :
    Expr.eval (fun _ => Real.sqrt (Real.log x)) rhsE2_row1
      ≤ (admissible_bound 0.000120 0.25 1 5.5666305 x) ^ 2 := by
  have hLnn : (0:ℝ) ≤ Real.log x := by linarith
  rw [eval_rhsE2_row1, admissible_quarter_eq 0.000120 1 5.5666305 x hLnn (by norm_num)]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hsqrtR_ub := sqrtR5_ub
  have hsqrtR_pos := sqrtR5_pos
  have hsqs : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs_nn
  have hexp2 : (Real.exp (-(1 / Real.sqrt 5.5666305) * s)) ^ 2
      = Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hexpand : (0.000120 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s
        * Real.exp (-(1 / Real.sqrt 5.5666305) * s)) ^ 2
      = (0.000120 / (5.5666305:ℝ)^((1:ℝ)/4))^2 * s * Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by
    rw [mul_pow, mul_pow, hsqs, hexp2]
  rw [hexpand]
  have hR14sq : ((5.5666305:ℝ)^((1:ℝ)/4))^2 = Real.sqrt 5.5666305 := by
    rw [← Real.rpow_natCast ((5.5666305:ℝ)^((1:ℝ)/4)) 2, ← Real.rpow_mul (by norm_num),
      Real.sqrt_eq_rpow]; norm_num
  have hcoeff : (6102/1000000000000:ℝ) ≤ (0.000120 / (5.5666305:ℝ)^((1:ℝ)/4))^2 := by
    rw [div_pow, hR14sq, le_div_iff₀ hsqrtR_pos,
      show (0.000120:ℝ)^2 = 144/10000000000 by norm_num]
    nlinarith [hsqrtR_ub]
  have hrate : (2:ℝ) / Real.sqrt 5.5666305 ≤ 8477/10000 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [sqrtR5_lb]
  have hexpRHS : Real.exp (-(8477/10000:ℝ) * s) ≤ Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (2 / Real.sqrt 5.5666305) * s ≤ (8477/10000) * s := mul_le_mul_of_nonneg_right hrate hs_nn
    simp only [neg_mul]; linarith
  calc (6102/1000000000000:ℝ) * s * Real.exp (-(8477/10000) * s)
      = ((6102/1000000000000:ℝ) * Real.exp (-(8477/10000) * s)) * s := by ring
    _ ≤ ((0.000120 / (5.5666305:ℝ)^((1:ℝ)/4))^2 * Real.exp (-(2 / Real.sqrt 5.5666305) * s)) * s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hexpRHS (Real.exp_nonneg _) (by positivity)) hs_nn
    _ = (0.000120 / (5.5666305:ℝ)^((1:ℝ)/4))^2 * s * Real.exp (-(2 / Real.sqrt 5.5666305) * s) := by ring

/-- Row-1 tail `[e^20000, ∞)`: Cor 22 domination, B=1/4 with tiny A; `√s ≥ 1`
drops the `√s`, reducing to `9.2211·s³·e^{-0.8476s} ≤ 7.811e-5·e^{-0.4239s}`. -/
theorem tail_row1 : ∀ x ≥ exp (20000:ℝ),
    Eπ x ≤ admissible_bound 0.000120 0.25 1 5.5666305 x := by
  intro x hx
  have he2 : (2:ℝ) ≤ Real.exp 20000 := by have := Real.add_one_le_exp (20000:ℝ); linarith
  have hx2 : (2:ℝ) ≤ x := le_trans he2 hx
  have hcor := corollary_22 x hx2
  refine le_trans hcor ?_
  have hL : (20000:ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20000]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLnn : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hL
  rw [admissible_three_halves_eq 9.2211 0.8476 1 x hLnn (by norm_num),
      admissible_quarter_eq 0.000120 1 5.5666305 x hLnn (by norm_num)]
  rw [show (1:ℝ) ^ (1.5:ℝ) = 1 by norm_num, Real.sqrt_one]
  simp only [div_one]
  set s := Real.sqrt (Real.log x) with hs_def
  have hs_nn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs141 : (141:ℝ) ≤ s := by
    rw [hs_def, show (141:ℝ) = Real.sqrt (141^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hL])
  have hsqrtR_lb := sqrtR5_lb
  have hsqrtR_pos := sqrtR5_pos
  have hsqrts_ge1 : (1:ℝ) ≤ Real.sqrt s := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hcoeffLB : (7811/100000000:ℝ) ≤ 0.000120 / (5.5666305:ℝ) ^ ((1:ℝ)/4) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]; nlinarith [R5_rpow_quarter_le]
  have hCR : (1:ℝ) / Real.sqrt 5.5666305 ≤ 0.4239 := by
    rw [div_le_iff₀ hsqrtR_pos]; nlinarith [hsqrtR_lb]
  have hexpRHS : Real.exp (-(0.4239:ℝ) * s) ≤ Real.exp (-(1 / Real.sqrt 5.5666305) * s) := by
    apply Real.exp_le_exp.mpr
    have : (1 / Real.sqrt 5.5666305) * s ≤ 0.4239 * s := mul_le_mul_of_nonneg_right hCR hs_nn
    simp only [neg_mul]; linarith
  have hcube : (9.2211:ℝ) * s^3 * Real.exp (-(0.8476) * s) ≤ 7811/100000000 * Real.exp (-(0.4239) * s) := by
    have hlin : s * Real.exp (-(0.05:ℝ) * s) ≤ 20 * Real.exp (-1) := by
      have hab : (0.05:ℝ) * s ≤ Real.exp (0.05 * s - 1) := by
        have := Real.add_one_le_exp (0.05 * s - 1); linarith
      have h := mul_le_mul_of_nonneg_right hab (Real.exp_nonneg (-(0.05 * s)))
      rw [← Real.exp_add] at h
      have he : (0.05 * s - 1) + -(0.05 * s) = -1 := by ring
      rw [he] at h
      have heq : (-(0.05:ℝ) * s) = -(0.05*s) := by ring
      rw [heq]; nlinarith [h, Real.exp_nonneg (-(0.05*s))]
    have hcube3 : s^3 * Real.exp (-(0.15:ℝ) * s) ≤ 8000 * Real.exp (-3) := by
      have hpow : (Real.exp (-(0.05:ℝ) * s))^(3:ℕ) = Real.exp (-(0.15) * s) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hfac : s^3 * Real.exp (-(0.15:ℝ) * s) = (s * Real.exp (-(0.05) * s))^(3:ℕ) := by
        rw [mul_pow, hpow]
      rw [hfac]
      have hnn : (0:ℝ) ≤ s * Real.exp (-(0.05) * s) := by positivity
      calc (s * Real.exp (-(0.05) * s))^(3:ℕ)
          ≤ (20 * Real.exp (-1))^(3:ℕ) := by apply pow_le_pow_left₀ hnn hlin
        _ = 8000 * Real.exp (-3) := by
            rw [mul_pow, show ((20:ℝ))^(3:ℕ) = 8000 by norm_num]; congr 1
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsplit : Real.exp (-(0.8476:ℝ) * s)
        = Real.exp (-(0.15) * s) * (Real.exp (-(0.2737) * s) * Real.exp (-(0.4239) * s)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have htail35 : Real.exp (-(0.2737:ℝ) * s) ≤ Real.exp (-35) := by
      apply Real.exp_le_exp.mpr; nlinarith [hs141]
    have hexp38 : (1000000000:ℝ) ≤ Real.exp 38 := by
      have he : Real.exp 38 = (Real.exp 1) ^ (38:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [he]
      calc (1000000000:ℝ) ≤ (2.7:ℝ)^(38:ℕ) := by norm_num
        _ ≤ (Real.exp 1)^(38:ℕ) := by gcongr; linarith [Real.exp_one_gt_d9]
    rw [hsplit,
      show (9.2211:ℝ) * s^3 * (Real.exp (-(0.15)*s) * (Real.exp (-(0.2737)*s) * Real.exp (-(0.4239)*s)))
        = 9.2211 * (s^3 * Real.exp (-(0.15)*s)) * Real.exp (-(0.2737)*s) * Real.exp (-(0.4239)*s) by ring]
    have hstep : (9.2211:ℝ) * (s^3 * Real.exp (-(0.15)*s)) * Real.exp (-(0.2737)*s)
        ≤ 9.2211 * (8000 * Real.exp (-3)) * Real.exp (-35) := by
      apply mul_le_mul _ htail35 (Real.exp_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hcube3 (by norm_num)
    have hfinal : (9.2211:ℝ) * (8000 * Real.exp (-3)) * Real.exp (-35) ≤ 7811/100000000 := by
      rw [show (9.2211:ℝ) * (8000 * Real.exp (-3)) * Real.exp (-35) = 73768.8 * Real.exp (-38) by
        rw [show (-38:ℝ) = -3 + -35 by ring, Real.exp_add]; ring]
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; nlinarith [hexp38]
    calc (9.2211:ℝ) * (s^3 * Real.exp (-(0.15)*s)) * Real.exp (-(0.2737)*s) * Real.exp (-(0.4239)*s)
        ≤ (9.2211 * (8000 * Real.exp (-3)) * Real.exp (-35)) * Real.exp (-(0.4239)*s) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
      _ ≤ 7811/100000000 * Real.exp (-(0.4239)*s) := mul_le_mul_of_nonneg_right hfinal (Real.exp_nonneg _)
  calc (9.2211:ℝ) * s^3 * Real.exp (-(0.8476) * s)
      ≤ 7811/100000000 * Real.exp (-(0.4239) * s) := hcube
    _ ≤ 0.000120 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s * Real.exp (-(1 / Real.sqrt 5.5666305) * s) := by
        have hRHSnn : (0:ℝ) ≤ 0.000120 / (5.5666305:ℝ)^((1:ℝ)/4) := by positivity
        calc (7811/100000000:ℝ) * Real.exp (-(0.4239)*s)
            ≤ 0.000120 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.exp (-(0.4239)*s) :=
              mul_le_mul_of_nonneg_right hcoeffLB (Real.exp_nonneg _)
          _ ≤ 0.000120 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s * Real.exp (-(0.4239)*s) := by
              rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hRHSnn
              calc Real.exp (-(0.4239)*s) = 1 * Real.exp (-(0.4239)*s) := (one_mul _).symm
                _ ≤ Real.sqrt s * Real.exp (-(0.4239)*s) :=
                    mul_le_mul_of_nonneg_right hsqrts_ge1 (Real.exp_nonneg _)
          _ ≤ 0.000120 / (5.5666305:ℝ)^((1:ℝ)/4) * Real.sqrt s * Real.exp (-(1 / Real.sqrt 5.5666305) * s) := by
              apply mul_le_mul_of_nonneg_left hexpRHS (by positivity)

/-! ## Row 1 `(A=0.000120, B=1/4, C=1, x₀=22.955)` assembly -/

/-- Row-1 quarter cell params (same `c64`/`rB` as `P2`, `Aq = 0.000120`). -/
def P1 : CellParams := ⟨8477/640000, 1, 235938/100000, 12/100000⟩

set_option maxHeartbeats 2000000 in
/-- The row-1 squared check passes on every cell with `b' ≥ 40` (the low-`L`
cells fail for tiny `A`, but row 1 only needs `x ≥ e^22.955` ⟹ used cells have
`b' ≥ 40`). -/
theorem allCells_checked_row1_hi40 :
    allCells.all (fun c => decide (c.b' < 40) || checkCellGenQuarter P1 c) = true := by
  native_decide

/-- Row-1 mid-range `[e^40, e^20000]` via the quarter transport on the RESTRICTED
cell set (`b' ≥ 40`). -/
theorem mid_row1 : ∀ x ∈ Set.Icc (exp (40:ℝ)) (exp (20000:ℝ)),
    Eπ x ≤ admissible_bound 0.000120 0.25 1 5.5666305 x := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := hx
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxlo
  have hx_lo10 : exp ((10:ℕ):ℝ) ≤ x :=
    le_trans (by simpa using Real.exp_le_exp.mpr (by norm_num : (10:ℝ) ≤ 40)) hxlo
  have hx_hi : x ≤ exp ((lastB 10 allCells : ℕ):ℝ) := by
    rw [allCells_last]; simpa using hxhi
  obtain ⟨c, hcmem, hcx⟩ :=
    cover_of_chainOk allCells 10 allCells_ne_nil allCells_chain hx_lo10 hx_hi
  have hb' : 40 ≤ c.b' := by
    have hlogx : (40:ℝ) ≤ Real.log x := by
      rw [← Real.log_exp 40]; exact Real.log_le_log (Real.exp_pos _) hxlo
    have hcb' : Real.log x ≤ (c.b' : ℝ) := (Real.log_le_iff_le_exp hxpos).mpr hcx.2
    have h40le : (40:ℝ) ≤ (c.b' : ℝ) := le_trans hlogx hcb'
    exact_mod_cast h40le
  have hck : checkCellGenQuarter P1 c = true := by
    have h := List.all_eq_true.mp allCells_checked_row1_hi40 c hcmem
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with hlt | hok
    · omega
    · exact hok
  refine cell_Epi_le_admissible_quarter P1 0.000120 1 5.5666305 (by norm_num) (by norm_num)
    (by norm_num [P1]) ?_ ?_ c hck (allCells_trusted c hcmem) x hcx
  · have hrhs : (((P1.c64 * 64 : ℚ)):ℝ) = 8477/10000 := by norm_num [P1]
    rw [hrhs, mul_one_div, div_le_iff₀ sqrtR5_pos]; nlinarith [sqrtR5_lb]
  · have hrhs : (((P1.rB : ℚ)):ℝ) = 235938/100000 := by norm_num [P1]
    rw [hrhs]; linarith [sqrtR5_ub]

/-- Row-1 boundary squared slab check on `[√23.5, √40]`. -/
theorem slabs_checked1 :
    checkExprLeOnSlabsDyadic (Expr.mul FloorButhe.lhsE FloorButhe.lhsE) rhsE2_row1
      (slabsFrom (4847/1000) 30) (-50) 8 = true := by
  native_decide

/-- Row-1 Buthe boundary segment `[e^23.5, e^40]` via the wide quarter assembler. -/
theorem boundary_row1 : ∀ x ∈ Set.Icc (Real.exp 23.5) (Real.exp 40),
    Eπ x ≤ admissible_bound 0.000120 0.25 1 5.5666305 x :=
  floor_buthe_quarter_wide rhsE2_row1 0.000120 1 23.5 40 (4847/1000) 30 (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [show ((4847/1000:ℚ):ℝ) = 4.847 by norm_num,
          show (4.847:ℝ) = Real.sqrt (4.847^2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num))
    (by have h635 : Real.sqrt 40 ≤ 6.33 := by
          rw [show (6.33:ℝ) = Real.sqrt (6.33^2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        push_cast; linarith [h635])
    support1 slabs_checked1 (fun x h => rhsE2_row1_le_sq x (by linarith))

/-- Row-1 near-threshold range `[exp 22.955, e^40]`, split at `e^23.5`: Buthe on
`[e^23.5, e^40]`; trusted numerical boundary `[e^22.955, e^23.5]`
(`x ∈ [9.3e9, 1.6e10]`, FKS2 blueprint small-`x`). -/
theorem floor_row1 : ∀ x ∈ Set.Icc (exp (22.955:ℝ)) (exp (40:ℝ)),
    Eπ x ≤ admissible_bound 0.000120 0.25 1 5.5666305 x := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  by_cases h235 : Real.exp 23.5 ≤ x
  · exact boundary_row1 x ⟨h235, hhi⟩
  · sorry

/-- **Corollary 23, row 1** `(A=0.000120, B=1/4, C=1, x₀=22.955)`. -/
theorem corollary_23_row1 : Eπ.classicalBound 0.000120 0.25 1 5.5666305 (exp 22.955) := by
  intro x hx
  by_cases h40 : x ≤ exp 40
  · exact floor_row1 x ⟨hx, h40⟩
  · rw [not_le] at h40
    by_cases h20k : x ≤ exp 20000
    · exact mid_row1 x ⟨le_of_lt h40, h20k⟩
    · rw [not_le] at h20k
      exact tail_row1 x (le_of_lt h20k)

end FKS2
