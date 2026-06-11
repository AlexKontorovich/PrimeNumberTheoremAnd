import PrimeNumberTheoremAnd.IEANTN.KadiriU8TestFn
import PrimeNumberTheoremAnd.IEANTN.KadiriU8Wiring

/-!
# The U8 chain closed at the Kadiri test function (sprint U8, unit 26)

This file fires `u8_kadiri_thm_3_1_q1_of_line_identifications` at
`φ = kadiriTestFn f s`, discharging every hypothesis from in-tree bricks:

* the analytic surface from `kadiriTestFn_contDiff` / `kadiriTestFn_decay` /
  `summable_kadiriTestFn_weighted_at_zeros`;
* the digamma contour integrability `hΓ_int` from `digamma_strip_bound` times
  the quadratic band decay of the transform (so the carried hypothesis of the
  weighted identity is now discharged at the test function);
* the full-product line integrabilities from
  `integrable_left_line_neg_logDeriv_mul` and
  `integrable_right_line_neg_logDeriv_mul`;
* the two line identifications from `KadiriU8TestFn.lean`.

The lines are fixed at `σL = -(1 + 1/2)` and `σR = (1 + Re s)/2`.  The
resulting `u8_kadiri_thm_3_1_q1_kadiriTestFn` carries `sorryAx` through the
good-heights bound (sub-unit U6a) only.
-/

namespace Kadiri

open Complex MeasureTheory
open ArithmeticFunction hiding log
open Filter Set Asymptotics
open scoped Topology

noncomputable section

/-! ## Line continuity of the Mellin data -/

private lemma kadiriTestFn_mellin_line_continuous {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {σ : ℝ} (hσ2 : -2 < σ) (hσs : σ < s.re) :
    Continuous fun t : ℝ =>
      mellin (fun u : ℝ => kadiriTestFn f s (Real.log u)) ((σ : ℂ) + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hre : ((σ : ℂ) + (t₀ : ℂ) * I).re = σ := by simp
  have han := kadiriTestFn_mellin_analyticAt hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
    (w := (σ : ℂ) + (t₀ : ℂ) * I) (by rw [hre]; exact hσ2) (by rw [hre]; exact hσs)
  exact ContinuousAt.comp (g := mellin fun u : ℝ => kadiriTestFn f s (Real.log u))
    (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) han.continuousAt (by fun_prop)

/-! ## The digamma contour integrability -/

/-- The `hΓ_int` input of the explicit formula, discharged at the Kadiri test
function: the digamma factor grows logarithmically on the critical line
(`digamma_strip_bound`) while the transform decays quadratically. -/
theorem kadiriTestFn_gamma_integrable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun t : ℝ =>
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y in (.Ioi (0 : ℝ)),
          kadiriTestFn f s y * exp (((1 / 2 : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume) := by
  have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  -- the inner integral is the Mellin data on the critical line
  have hinner : ∀ t : ℝ,
      (∫ y in (.Ioi (0 : ℝ)),
        kadiriTestFn f s y * exp (((1 / 2 : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume) =
      mellin (fun u : ℝ => kadiriTestFn f s (Real.log u)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    intro t
    rw [← u8Phi_neg_eq_mellin_log (fun y hy => kadiriTestFn_neg f s hy)]
    unfold u8Phi
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [hcast, neg_neg]
  obtain ⟨Cψ, hCψ0, hCψ⟩ := digamma_strip_bound (α := 1 / 2) (β := 1 / 2) (by norm_num)
  obtain ⟨CΦ, hCΦ⟩ := kadiriTestFn_mellin_band_decay hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s (a := 1 / 2) (b := 1 / 2) (by norm_num) le_rfl (by linarith)
  have hψcont : Continuous fun t : ℝ =>
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hψ : ContinuousAt digamma (((1 / 2 : ℂ) + (t₀ : ℂ) * I) / 2) := by
      refine (analyticAt_digamma_of_re_pos ?_).continuousAt
      have hpt : ((1 / 2 : ℂ) + (t₀ : ℂ) * I) / 2 = (1 / 4 : ℂ) + ((t₀ / 2 : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [hpt]
      norm_num [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
    have hinnercont : ContinuousAt
        (fun t : ℝ => digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)) t₀ :=
      ContinuousAt.comp (g := digamma)
        (f := fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * I) / 2) hψ (by fun_prop)
    exact Complex.continuous_ofReal.continuousAt.comp
      (Complex.continuous_re.continuousAt.comp hinnercont)
  have hMcont := kadiriTestFn_mellin_line_continuous hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s (σ := 1 / 2) (by norm_num) (by linarith)
  have hfun : (fun t : ℝ =>
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y in (.Ioi (0 : ℝ)),
          kadiriTestFn f s y * exp (((1 / 2 : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume) =
      fun t : ℝ =>
        ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
          mellin (fun u : ℝ => kadiriTestFn f s (Real.log u))
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    funext t
    rw [hinner t]
  rw [hfun]
  refine integrable_of_norm_le_log_div_sq (C := Cψ * CΦ) (hψcont.mul hMcont) fun t ht => ?_
  have hψb : ‖digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)‖ ≤ Cψ * Real.log (|t| + 2) := by
    have := hCψ ((1 / 2 : ℂ) + (t : ℂ) * I) (by simp) (by simp)
    simpa using this
  have hreb : ‖(((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℝ) : ℂ)‖ ≤
      Cψ * Real.log (|t| + 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (Complex.abs_re_le_norm _) hψb
  have hMb := hCΦ (1 / 2) Set.left_mem_uIcc t ht
  rw [norm_mul]
  calc ‖(((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℝ) : ℂ)‖ *
        ‖mellin (fun u : ℝ => kadiriTestFn f s (Real.log u)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (Cψ * Real.log (|t| + 2)) * (CΦ / t ^ 2) :=
        mul_le_mul hreb hMb (norm_nonneg _)
          (mul_nonneg hCψ0.le (Real.log_nonneg (by linarith [abs_nonneg t])))
    _ = Cψ * CΦ * Real.log (|t| + 2) / t ^ 2 := by ring

/-! ## The full-product line integrabilities -/

private lemma kadiriTestFn_u8Phi_line_decay {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {σ : ℝ} (hσ2 : -2 < σ) (hσs : σ < s.re) :
    ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖u8Phi (kadiriTestFn f s) (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ CΦ / t ^ 2 := by
  obtain ⟨C, hC⟩ := kadiriTestFn_mellin_band_decay hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s (a := σ) (b := σ) hσ2 le_rfl hσs
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (lt_of_lt_of_le one_pos ht) 2
  rw [u8Phi_neg_eq_mellin_log (fun y hy => kadiriTestFn_neg f s hy)]
  refine le_trans (hC σ Set.left_mem_uIcc t ht) ?_
  gcongr
  exact le_max_left _ _

/-- The right-line full-product integrability (`hright` of the contour pull)
at the Kadiri test function. -/
theorem kadiriTestFn_hright_integrable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {σR : ℝ} (hσR : 1 < σR) (hσRs : σR < s.re) :
    Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((σR : ℂ) + t * I) *
        (-(u8Phi (kadiriTestFn f s) (-((σR : ℂ) + t * I)))) := by
  obtain ⟨CΦ, _, hCΦ⟩ := kadiriTestFn_u8Phi_line_decay hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s (by linarith : (-2 : ℝ) < σR) hσRs
  have hcont : Continuous fun t : ℝ =>
      u8Phi (kadiriTestFn f s) (-((σR : ℂ) + (t : ℂ) * I)) := by
    have hM := kadiriTestFn_mellin_line_continuous hd hf_C2 hf_supp hf_d hf_deriv_0
      hf_deriv_d s (σ := σR) (by linarith) hσRs
    refine hM.congr fun t => ?_
    rw [u8Phi_neg_eq_mellin_log (fun y hy => kadiriTestFn_neg f s hy)]
  exact integrable_right_line_neg_logDeriv_mul hσR hcont hCΦ

/-- The left-line full-product integrability (`hleft` of the contour pull)
at the Kadiri test function, on the line `σL = -(1 + a)` with `a ∈ (0, 1)`. -/
theorem kadiriTestFn_hleft_integrable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) {s : ℂ} (hs : 1 < s.re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Integrable fun t : ℝ =>
      -logDeriv riemannZeta ((-(1 + a) : ℝ) + t * I) *
        (-(u8Phi (kadiriTestFn f s) (-(((-(1 + a) : ℝ) : ℂ) + t * I)))) := by
  have hσ2 : (-2 : ℝ) < -(1 + a) := by linarith
  have hσs : -(1 + a) < s.re := by linarith
  have hcont : Continuous fun t : ℝ =>
      u8Phi (kadiriTestFn f s) (-(verticalLine (-(1 + a)) t)) := by
    have hM := kadiriTestFn_mellin_line_continuous hd hf_C2 hf_supp hf_d hf_deriv_0
      hf_deriv_d s (σ := -(1 + a)) hσ2 hσs
    refine hM.congr fun t => ?_
    rw [u8Phi_neg_eq_mellin_log (fun y hy => kadiriTestFn_neg f s hy)]
    rfl
  have hdec : ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖u8Phi (kadiriTestFn f s) (-(verticalLine (-(1 + a)) t))‖ ≤ CΦ / t ^ 2 := by
    obtain ⟨CΦ, hCΦ0, hCΦ⟩ := kadiriTestFn_u8Phi_line_decay hd hf_C2 hf_supp hf_d
      hf_deriv_0 hf_deriv_d s hσ2 hσs
    exact ⟨CΦ, hCΦ0, fun t ht => hCΦ t ht⟩
  have h := integrable_left_line_neg_logDeriv_mul (b := 1) ha ha1 ha1 hcont hdec
  refine h.neg.congr ?_
  filter_upwards with t
  simp only [Pi.neg_apply, logDeriv_apply, verticalLine]
  push_cast
  ring

/-! ## The chain closed at the test function -/

/-- The repaired `kadiri_thm_3_1_q1` conclusion at the Kadiri test function,
with every analytic hypothesis discharged from in-tree bricks.  The only
remaining axiom debt is the good-heights log-derivative bound (sub-unit U6a),
inherited through the contour pull. -/
theorem u8_kadiri_thm_3_1_q1_kadiriTestFn {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) {s : ℂ} (hs : 1 < s.re) :
    let Φ : ℂ → ℂ :=
      fun z ↦ ∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      Φ (-1) + Φ 0
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
            (fun ρ ↦ Φ (-ρ))
        - kadiriTestFn f s 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * kadiriTestFn f s (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-((1 / 2 : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨b, hb, hdec, hdec'⟩ := kadiriTestFn_decay hf_supp hs
  obtain ⟨CΦ, _, hCΦband⟩ : ∃ CΦ : ℝ, 0 ≤ CΦ ∧
      ∀ x ∈ Set.uIcc (-(1 + (1 / 2 : ℝ))) ((1 + s.re) / 2), ∀ t : ℝ, 1 ≤ |t| →
        ‖u8Phi (kadiriTestFn f s) (-((x : ℂ) + (t : ℂ) * I))‖ ≤ CΦ / t ^ 2 := by
    obtain ⟨C, hC⟩ := kadiriTestFn_mellin_band_decay hd hf_C2 hf_supp hf_d hf_deriv_0
      hf_deriv_d s (a := -(1 + (1 / 2 : ℝ))) (b := (1 + s.re) / 2)
      (by norm_num) (by linarith) (by linarith)
    refine ⟨max C 0, le_max_right _ _, fun x hx t ht => ?_⟩
    have ht0 : (0 : ℝ) < t ^ 2 := by
      rw [← sq_abs]
      exact pow_pos (lt_of_lt_of_le one_pos ht) 2
    rw [u8Phi_neg_eq_mellin_log (fun y hy => kadiriTestFn_neg f s hy)]
    refine le_trans (hC x hx t ht) ?_
    gcongr
    exact le_max_left _ _
  exact u8_kadiri_thm_3_1_q1_of_line_identifications
    (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s)
    hb hdec hdec'
    (summable_kadiriTestFn_weighted_at_zeros hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs)
    (kadiriTestFn_gamma_integrable hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs)
    (σL := -(1 + (1 / 2 : ℝ))) (σR := (1 + s.re) / 2)
    (by norm_num) (by norm_num) (by linarith)
    (fun w hw1 hw2 => by
      have han := kadiriTestFn_mellin_analyticAt hd hf_C2 hf_supp hf_d hf_deriv_0
        hf_deriv_d s (w := w) (by linarith) (by linarith)
      refine han.congr ?_
      filter_upwards with u
      rw [u8Phi_neg_eq_mellin_log (fun y hy => kadiriTestFn_neg f s hy)])
    (kadiriTestFn_hleft_integrable hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d hs
      (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    (kadiriTestFn_hright_integrable hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      (by linarith) (by linarith))
    (CΦ := CΦ) (Y₀ := 1) hCΦband
    (u8RightLineInversionHypothesis_kadiriTestFn hd hf_C2 hf_supp hf_d hf_deriv_0
      hf_deriv_d (by linarith) (by linarith))
    (u8LeftLineFunctionalEquationSplitHypothesis_kadiriTestFn hd hf_C2 hf_supp hf_d
      hf_deriv_0 hf_deriv_d hs (by norm_num) (by norm_num))

end

end Kadiri
