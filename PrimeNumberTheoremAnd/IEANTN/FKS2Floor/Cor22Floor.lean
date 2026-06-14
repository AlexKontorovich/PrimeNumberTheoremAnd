import PrimeNumberTheoremAnd.IEANTN.FKS2
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4Ext
import LeanCert.Engine.ChebyshevTheta
import LeanCert.Validity.AffineCover
import LeanCert.Tactic.IntervalAuto

open LeanCert.Engine.ChebyshevTheta
open Real MeasureTheory Chebyshev LeanCert.Core LeanCert.Validity
namespace FKS2.Floor

theorem exp10_lt : Real.exp 10 < 22027 := by interval_decide

/-- Eθ ≤ 4/5 on [2, e^10], via the θ engine + ⌊x⌋ stitching.
`checkAllThetaRelErrorReal start limit` checks real unit intervals for
`N < limit`; since `exp 10 < 22027`, the relevant floors satisfy
`N < 22027` and use the `[N, N+1)` real certificate branch. -/
theorem etheta_le_floor :
    ∀ x ∈ Set.Icc (2:ℝ) (Real.exp 10), Eθ x ≤ (4/5 : ℝ) := by
  have hcheck : checkAllThetaRelErrorReal 2 22027 (4/5) 20 = true := by native_decide
  intro x hx
  obtain ⟨hx2, hxe⟩ := hx
  have hxpos : (0:ℝ) ≤ x := by linarith
  set N := ⌊x⌋₊ with hN
  have hNlo : (N:ℝ) ≤ x := Nat.floor_le hxpos
  have hNhi : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx2)
  have hxlt : x < 22027 := lt_of_le_of_lt hxe exp10_lt
  have hNlim : N < 22027 := (Nat.floor_lt hxpos).mpr (by exact_mod_cast hxlt)
  have hNpos : 0 < N := by omega
  have himpl := checkAllThetaRelErrorReal_implies 2 22027 (4/5) 20 hcheck N hNpos hN2
    (by omega : N ≤ 22027)
  rw [if_pos hNlim] at himpl
  have h := verify_theta_rel_error_real N 20 (4/5) (by norm_num) (by norm_num) himpl x hNlo hNhi
  have hcast : ((4/5 : ℚ) : ℝ) = (4/5 : ℝ) := by norm_num
  rw [hcast] at h
  unfold Eθ
  rw [div_le_iff₀ (by linarith : (0:ℝ) < x)]
  exact h

/-- δ(2) = 1 exactly. -/
theorem delta_two : δ 2 = 1 := by
  have hpi : pi 2 = 1 := by
    have hfl : ⌊(2:ℝ)⌋₊ = 2 := by norm_num
    unfold pi; rw [hfl]; norm_num [Nat.primeCounting, Nat.primeCounting']; decide
  have hLi : Li 2 = 0 := by unfold Li; exact intervalIntegral.integral_same
  have hth : θ (2:ℝ) = Real.log 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Chebyshev.theta_eq_sum_primesLE_log]
    have hpr : Nat.primesLE 2 = {2} := by decide
    rw [hpr, Finset.sum_singleton]
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold δ; rw [hpi, hLi, hth]
  rw [show (1 - 0) / ((2:ℝ) / Real.log 2) - (Real.log 2 - 2) / 2 = 1 by field_simp; ring]
  norm_num

/-- Integrability of the eq_30 integrand on [2,x] (mirrors lemma_12). -/
theorem etheta_integrand_intble {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => Eθ t / log t ^ 2) volume 2 x := by
  have log_t_ne_zero : ∀ t ∈ Set.uIcc (2:ℝ) x, log t ≠ 0 := fun t ht ↦ by
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    exact ne_of_gt (log_pos (by linarith [ht.1]))
  have t_ne_zero : ∀ t ∈ Set.uIcc (2:ℝ) x, t ≠ 0 := fun t ht ↦ by
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht; exact ne_of_gt (by linarith [ht.1])
  refine IntervalIntegrable.mul_continuousOn ?_ (by fun_prop (disch := grind))
  unfold Eθ
  refine IntervalIntegrable.mul_continuousOn ?_ (by fun_prop (disch := grind))
  refine IntervalIntegrable.abs <| IntervalIntegrable.sub ?_ intervalIntegral.intervalIntegrable_id
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
  conv => arg 1; ext y; rw [← one_mul (θ y), theta_eq_sum_Icc, Finset.sum_filter]
  apply integrableOn_mul_sum_Icc _ (by linarith)
  apply ContinuousOn.integrableOn_Icc; fun_prop

/-- ∫₂ˣ Eθ/log²t ≤ (4/5)/(log 2)²·(x−2) on the floor (crude: Eθ ≤ 4/5, log t ≥ log 2). -/
theorem integral_etheta_bound {x : ℝ} (hx2 : 2 ≤ x) (hxe : x ≤ exp 10) :
    ∫ t in (2:ℝ)..x, Eθ t / log t ^ 2 ≤ (4/5) / (log 2) ^ 2 * (x - 2) := by
  have hlog2 : (0:ℝ) < log 2 := log_pos (by norm_num)
  calc ∫ t in (2:ℝ)..x, Eθ t / log t ^ 2
      ≤ ∫ _t in (2:ℝ)..x, (4/5) / (log 2) ^ 2 := by
        apply intervalIntegral.integral_mono_on hx2 (etheta_integrand_intble hx2)
          intervalIntegrable_const
        intro t ⟨ht2, htx⟩
        have hEθt : Eθ t ≤ 4/5 := etheta_le_floor t ⟨ht2, le_trans htx hxe⟩
        have hEθnn : 0 ≤ Eθ t := by unfold Eθ; positivity
        have hlogt : log 2 ≤ log t := log_le_log (by norm_num) ht2
        have hlogt_pos : (0:ℝ) < log t := lt_of_lt_of_le hlog2 hlogt
        have hsq : (log 2)^2 ≤ (log t)^2 := by nlinarith [hlogt, hlog2.le]
        calc Eθ t / log t ^ 2 ≤ (4/5) / log t ^ 2 := by gcongr
          _ ≤ (4/5) / (log 2) ^ 2 := by gcongr
    _ = (4/5) / (log 2) ^ 2 * (x - 2) := by
        rw [intervalIntegral.integral_const]; ring

open LeanCert.Core LeanCert.Validity in
/-- s-form comparison Exprs: f(s)=0.8+(5/3)s², g(s)=9.2211 s³ exp(-0.8476 s). -/
def fExpr : Expr :=
  Expr.add (Expr.const (4/5)) (Expr.mul (Expr.const (5/3)) (Expr.mul (Expr.var 0) (Expr.var 0)))

open LeanCert.Core in
def gExpr : Expr :=
  Expr.mul (Expr.mul (Expr.const (92211/10000))
      (Expr.mul (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.var 0)))
    (Expr.exp (Expr.mul (Expr.const (-2119/2500)) (Expr.var 0)))

def cbps : List ℚ := (List.range 24).map (fun k => ((83 + 10*(k+1) : ℚ))/100)

open LeanCert.Core LeanCert.Validity in
theorem cover_cmp :
    ∀ s ∈ Set.Icc ((83/100 : ℚ) : ℝ) ((cbps.getLast (by decide) : ℚ) : ℝ),
      Expr.eval (fun _ => s) fExpr ≤ Expr.eval (fun _ => s) gExpr :=
  verify_le_affine_cover fExpr gExpr (by unfold fExpr gExpr Expr.sub; repeat constructor)
    {} (83/100) cbps (by decide) (by native_decide)

/-- The curve comparison on the floor.  After setting `s = sqrt (log x)`,
the affine cover verifies `0.8 + (5/3) * s^2 ≤ 9.2211 * s^3 * exp (-0.8476 * s)`,
which rewrites to `4/5 + (5/3) * log x ≤ admissible_bound ... x`. -/
theorem linear_le_curve {x : ℝ} (hx2 : 2 ≤ x) (hxe : x ≤ exp 10) :
    4/5 + (5/3) * log x ≤ admissible_bound 9.2211 (3/2) 0.8476 1 x := by
  have hlogx_nn : 0 ≤ log x := log_nonneg (by linarith)
  have hlogx_lo : log 2 ≤ log x := log_le_log (by norm_num) hx2
  have hlogx_hi : log x ≤ 10 := by
    rw [show (10:ℝ) = log (exp 10) by rw [log_exp]]; exact log_le_log (by positivity) hxe
  set s := Real.sqrt (log x) with hs_def
  have hs2 : s ^ 2 = log x := Real.sq_sqrt hlogx_nn
  have hgl : cbps.getLast (by decide) = (323/100 : ℚ) := by native_decide
  have hs_mem : s ∈ Set.Icc ((83/100 : ℚ) : ℝ) ((cbps.getLast (by decide) : ℚ) : ℝ) := by
    rw [hgl]
    refine ⟨?_, ?_⟩
    · have h1 : ((83/100 : ℚ):ℝ) ^ 2 ≤ log x := by
        have he : ((83/100 : ℚ):ℝ) ^ 2 = 6889/10000 := by norm_num
        rw [he]; nlinarith [hlogx_lo, Real.log_two_gt_d9]
      calc ((83/100 : ℚ):ℝ) = Real.sqrt (((83/100 : ℚ):ℝ) ^ 2) :=
            (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (log x) := Real.sqrt_le_sqrt h1
        _ = s := hs_def.symm
    · have h2 : log x ≤ ((323/100 : ℚ):ℝ) ^ 2 := by
        have he : ((323/100 : ℚ):ℝ) ^ 2 = 104329/10000 := by norm_num
        rw [he]; linarith [hlogx_hi]
      calc s = Real.sqrt (log x) := hs_def
        _ ≤ Real.sqrt (((323/100 : ℚ):ℝ) ^ 2) := Real.sqrt_le_sqrt h2
        _ = ((323/100 : ℚ):ℝ) := Real.sqrt_sq (by norm_num)
  have hcov := cover_cmp s hs_mem
  simp only [fExpr, gExpr, Expr.eval_add, Expr.eval_mul, Expr.eval_const, Expr.eval_var,
    Expr.eval_exp] at hcov
  -- LHS: 4/5 + 5/3 * (s*s) = 4/5 + 5/3 * log x
  rw [show s * s = log x by rw [← sq]; exact hs2] at hcov
  have hlogx_pos : (0:ℝ) < log x := lt_of_lt_of_le (log_pos (by norm_num)) hlogx_lo
  unfold admissible_bound
  simp only [div_one]
  have e1 : (log x) ^ ((3:ℝ)/2) = log x * s := by
    rw [show log x * s = s ^ 3 by rw [← hs2]; ring, hs_def, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast ((log x) ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hlogx_nn]
    norm_num
  have e2 : (log x) ^ ((1:ℝ)/2) = s := by rw [hs_def, Real.sqrt_eq_rpow]
  rw [e1, e2]
  convert hcov using 2 <;> norm_num

/-- The Corollary 22 small-x floor: Eπ ≤ the admissible curve on [2, e^10],
ungated — via the Chebyshev θ engine (Eθ bound), eq_30, and the affine-cover
curve comparison. -/
theorem corollary_22_floor :
    ∀ x ∈ Set.Icc (2:ℝ) (exp 10), Eπ x ≤ admissible_bound 9.2211 (3/2) 0.8476 1 x := by
  intro x hx
  obtain ⟨hx2, hxe⟩ := hx
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx_pos : (0:ℝ) < log x := log_pos (by linarith)
  have hℓ : (0:ℝ) < log 2 := log_pos (by norm_num)
  have hℓ2 : (0:ℝ) < (log 2) ^ 2 := by positivity
  have hℓ_gt : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hlogxx_nn : (0:ℝ) ≤ log x / x := div_nonneg hlogx_pos.le hxpos.le
  have h30 := eq_30 (x₀ := 2) hx2 (by norm_num)
  rw [delta_two] at h30
  have hEθ : Eθ x ≤ 4/5 := etheta_le_floor x ⟨hx2, hxe⟩
  have hint : ∫ t in (2:ℝ)..x, Eθ t / log t ^ 2 ≤ (4/5) / (log 2) ^ 2 * (x - 2) :=
    integral_etheta_bound hx2 hxe
  -- bracket algebra: the two correction terms ≤ (5/3) log x
  have hb1 : 2 / log 2 ≤ 2887/1000 := by rw [div_le_iff₀ hℓ]; nlinarith [hℓ_gt]
  have hb2 : (4/5) / (log 2) ^ 2 ≤ 1666/1000 := by rw [div_le_iff₀ hℓ2]; nlinarith [hℓ_gt, hℓ]
  have hbracket :
      (log x / x) * (2 / log 2) * 1 + (log x / x) * ((4/5) / (log 2) ^ 2 * (x - 2))
        ≤ (5/3) * log x := by
    have hred : 2 / log 2 + (4/5) / (log 2) ^ 2 * (x - 2) ≤ (5/3) * x := by
      have hxm2 : (0:ℝ) ≤ x - 2 := by linarith
      have hstep : 2 / log 2 + (4/5) / (log 2) ^ 2 * (x - 2)
          ≤ 2887/1000 + 1666/1000 * (x - 2) := by gcongr
      nlinarith [hstep, hx2]
    have h := mul_le_mul_of_nonneg_left hred hlogxx_nn
    rw [show (log x / x) * ((5/3) * x) = (5/3) * log x by field_simp] at h
    rw [show (log x / x) * (2 / log 2 + (4/5) / (log 2) ^ 2 * (x - 2))
        = (log x / x) * (2 / log 2) * 1 + (log x / x) * ((4/5) / (log 2) ^ 2 * (x - 2)) by
      ring] at h
    exact h
  calc Eπ x
      ≤ Eθ x + log x / x * (2 / log 2) * 1
          + log x / x * ∫ t in (2:ℝ)..x, Eθ t / log t ^ 2 := h30
    _ ≤ 4/5 + log x / x * (2 / log 2) * 1
          + log x / x * ((4/5) / (log 2) ^ 2 * (x - 2)) := by gcongr
    _ ≤ 4/5 + (5/3) * log x := by linarith [hbracket]
    _ ≤ admissible_bound 9.2211 (3/2) 0.8476 1 x := linear_le_curve hx2 hxe

/-- Full Corollary 22, reduced to the remaining mid-range table-data theorem.
The small range is `corollary_22_floor`; the asymptotic tail is
`FKS2.corollary_22_tail`. -/
theorem corollary_22_of_midrange
    (hmid : ∀ x ∈ Set.Icc (exp 10) (exp 20000),
      Eπ x ≤ admissible_bound 9.2211 (3/2) 0.8476 1 x) :
    Eπ.classicalBound 9.2211 (3/2) 0.8476 1 2 := by
  intro x hx
  by_cases hsmall : x ≤ exp 10
  · exact corollary_22_floor x ⟨hx, hsmall⟩
  · by_cases htail : exp 20000 ≤ x
    · exact _root_.FKS2.corollary_22_tail x htail
    · have hx_lo : exp 10 ≤ x := le_of_lt (lt_of_not_ge hsmall)
      have hx_hi : x ≤ exp 20000 := le_of_not_ge htail
      exact hmid x ⟨hx_lo, hx_hi⟩

/-- Corollary 22, assembled from the small range, the extended Table 4
mid-range, and the asymptotic tail. The remaining trust boundary is
`Table4Ext.allCells_trusted`, used by `Table4Ext.Epi_le_admissible_on_midrange`. -/
theorem corollary_22_from_table4Ext :
    Eπ.classicalBound 9.2211 (3/2) 0.8476 1 2 :=
  corollary_22_of_midrange (by
    intro x hx
    have h := Table4Ext.Epi_le_admissible_on_midrange hx
    norm_num [Table4Ext.Aq, Table4Ext.Cq] at h ⊢
    exact h)


end FKS2.Floor
