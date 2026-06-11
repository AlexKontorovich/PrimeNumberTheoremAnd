import PrimeNumberTheoremAnd.IEANTN.KadiriU8LeftLine

/-!
# The U8 line identifications at the Kadiri test function (sprint U8, unit 25)

This file instantiates the two line-identification endpoints at
`φ = kadiriTestFn f s`, discharging their Mellin-side hypotheses:

* the multiplicative test function `t ↦ φ (log t)` vanishes on `(0, 1]` and is
  exactly `O(t ^ (-s.re))` at infinity, so Mellin convergence and
  differentiability on the strip `-2 < re < s.re` come from the mathlib big-O
  criteria;
* the transform identity `kadiriTestFn_laplaceTransform` gives the explicit
  form `f 0 / (s - w) - laplaceTransform f (s - w)` on the strip, whose
  quadratic line decay is `laplace_sub_pole_strip_decay`; a compactness
  argument moves the decay threshold from `2|s.im| + 2` down to `1`;
* global continuity is `kadiriTestFn_contDiff`.

The endpoints are
`u8RightLineInversionHypothesis_kadiriTestFn` (any `σR ∈ (1, s.re)`) and
`u8LeftLineFunctionalEquationSplitHypothesis_kadiriTestFn`
(any `σL ∈ (-2, 0)`).
-/

namespace Kadiri

open Complex MeasureTheory
open ArithmeticFunction hiding log
open Filter Set Asymptotics
open scoped Topology

noncomputable section

/-! ## One-sidedness and a global bound -/

lemma kadiriTestFn_neg (f : ℝ → ℝ) (s : ℂ) {y : ℝ} (hy : y < 0) :
    kadiriTestFn f s y = 0 := by
  simp [kadiriTestFn, not_le.mpr hy]

private lemma exists_bound_abs_f {d : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, |f y| ≤ B := by
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_C2.continuousOn
  refine ⟨max B₁ 0, le_max_right _ _, fun y => ?_⟩
  rcases lt_or_ge y 0 with hy | hy
  · rw [image_eq_zero_of_notMem_tsupport fun hmem => absurd (hf_supp hmem).1 (not_le.mpr hy)]
    simp
  · by_cases hyd : y ≤ d
    · exact le_trans (by simpa [Real.norm_eq_abs] using hB₁ y ⟨hy, hyd⟩) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport fun hmem =>
        absurd (hf_supp hmem).2 (not_lt.mpr (le_of_not_ge hyd))]
      simp

private lemma kadiriTestFn_norm_le {d : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 0 ≤ y →
      ‖kadiriTestFn f s y‖ ≤ B * Real.exp (-s.re * y) := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_bound_abs_f hf_C2 hf_supp
  refine ⟨|f 0| + B₁, add_nonneg (abs_nonneg _) hB₁0, fun y hy => ?_⟩
  have hre : (-s * (y : ℂ)).re = -s.re * y := by
    simp [Complex.mul_re]
  simp only [kadiriTestFn, if_pos hy]
  rw [norm_mul, Complex.norm_exp, hre]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  rw [show ((f 0 : ℂ) - (f y : ℂ)) = ((f 0 - f y : ℝ) : ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  calc |f 0 - f y| ≤ |f 0| + |f y| := abs_sub _ _
    _ ≤ |f 0| + B₁ := by linarith [hB₁ y]

/-! ## Big-O data for the multiplicative test function -/

private lemma kadiriTestFn_log_isBigO_atTop {d : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) :
    (fun t : ℝ => kadiriTestFn f s (Real.log t)) =O[Filter.atTop]
      fun t : ℝ => t ^ (-s.re) := by
  obtain ⟨B, hB0, hB⟩ := kadiriTestFn_norm_le hf_C2 hf_supp s
  rw [Asymptotics.isBigO_iff]
  refine ⟨B, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  calc ‖kadiriTestFn f s (Real.log t)‖
      ≤ B * Real.exp (-s.re * Real.log t) := hB _ hlog
    _ = B * t ^ (-s.re) := by
        rw [Real.rpow_def_of_pos ht0, mul_comm (Real.log t)]
    _ ≤ B * ‖t ^ (-s.re)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]

private lemma kadiriTestFn_log_isBigO_zero (f : ℝ → ℝ) (s : ℂ) :
    (fun t : ℝ => kadiriTestFn f s (Real.log t)) =O[nhdsWithin 0 (Set.Ioi 0)]
      fun t : ℝ => t ^ (-(-2 : ℝ)) := by
  have hev : (fun t : ℝ => kadiriTestFn f s (Real.log t)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun _ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    obtain ⟨ht1, ht2⟩ := Set.mem_Ioo.mp ht
    exact kadiriTestFn_neg f s (Real.log_neg ht1 ht2)
  exact hev.trans_isBigO (Asymptotics.isBigO_zero _ _)

private lemma kadiriTestFn_log_locallyIntegrableOn {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ) :
    LocallyIntegrableOn (fun t : ℝ => kadiriTestFn f s (Real.log t)) (Set.Ioi 0) := by
  have hglob := (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s).continuous
  have hcont : ContinuousOn (fun t : ℝ => kadiriTestFn f s (Real.log t)) (Set.Ioi 0) :=
    hglob.comp_continuousOn (Real.continuousOn_log.mono fun t ht =>
      Set.mem_compl_singleton_iff.mpr (ne_of_gt ht))
  exact hcont.locallyIntegrableOn measurableSet_Ioi

/-! ## Mellin convergence and analyticity on the strip -/

lemma kadiriTestFn_mellinConvergent {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {σ : ℝ} (hσ2 : -2 < σ) (hσs : σ < s.re) :
    MellinConvergent (fun t : ℝ => kadiriTestFn f s (Real.log t)) (σ : ℂ) :=
  mellinConvergent_of_isBigO_rpow
    (kadiriTestFn_log_locallyIntegrableOn hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s)
    (kadiriTestFn_log_isBigO_atTop hf_C2 hf_supp s)
    (by simpa using hσs)
    (kadiriTestFn_log_isBigO_zero f s)
    (by simpa using hσ2)

lemma kadiriTestFn_mellin_analyticAt {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {w : ℂ} (hw2 : -2 < w.re) (hws : w.re < s.re) :
    AnalyticAt ℂ (mellin fun t : ℝ => kadiriTestFn f s (Real.log t)) w := by
  have hopen : IsOpen {z : ℂ | -2 < z.re ∧ z.re < s.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hdiff : DifferentiableOn ℂ (mellin fun t : ℝ => kadiriTestFn f s (Real.log t))
      {z : ℂ | -2 < z.re ∧ z.re < s.re} := fun z hz =>
    (mellin_differentiableAt_of_isBigO_rpow
      (kadiriTestFn_log_locallyIntegrableOn hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s)
      (kadiriTestFn_log_isBigO_atTop hf_C2 hf_supp s) hz.2
      (kadiriTestFn_log_isBigO_zero f s) hz.1).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds ⟨hw2, hws⟩)

/-! ## The explicit transform and the quadratic band decay -/

/-- On `Re w < Re s` the Mellin data of the test function is the
pole-subtracted Laplace transform. -/
lemma kadiriTestFn_mellin_eq {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ)
    {w : ℂ} (hws : w.re < s.re) :
    mellin (fun t : ℝ => kadiriTestFn f s (Real.log t)) w =
      (f 0 : ℂ) / (s - w) - laplaceTransform f (s - w) := by
  have h1 := u8Phi_neg_eq_mellin_log (φ := kadiriTestFn f s)
    (fun y hy => kadiriTestFn_neg f s hy) w
  have h2 := kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-w)
    (by rw [Complex.add_re, Complex.neg_re]; linarith)
  rw [← h1]
  unfold u8Phi
  rw [show s + -w = s - w from by ring] at h2
  exact h2

/-- Quadratic decay of the Mellin data on every vertical band left of `Re s`,
with threshold `1`: `laplace_sub_pole_strip_decay` supplies the bound above
`2|Im s| + 2`, and a compactness bound covers the middle. -/
lemma kadiriTestFn_mellin_band_decay {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {a b : ℝ} (ha : -2 < a) (hab : a ≤ b) (hbs : b < s.re) :
    ∃ C : ℝ, ∀ x ∈ Set.uIcc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖mellin (fun u : ℝ => kadiriTestFn f s (Real.log u)) ((x : ℂ) + (t : ℂ) * I)‖
        ≤ C / t ^ 2 := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := laplace_sub_pole_strip_decay hd hf_C2 hf_supp hf_d
    hf_deriv_0 hf_deriv_d s b
  set Y₀ : ℝ := 2 * |s.im| + 2 with hY₀def
  have hY₀1 : (1 : ℝ) ≤ Y₀ := by
    have := abs_nonneg s.im
    rw [hY₀def]
    linarith
  have hY₀0 : (0 : ℝ) < Y₀ := lt_of_lt_of_le one_pos hY₀1
  -- the compact middle bound
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => mellin (fun u : ℝ => kadiriTestFn f s (Real.log u))
        ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (Set.Icc a b ×ˢ Set.Icc (-Y₀) Y₀) := by
    intro p hp
    have hre : ((p.1 : ℂ) + (p.2 : ℂ) * I).re = p.1 := by simp
    have han := kadiriTestFn_mellin_analyticAt hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      (w := (p.1 : ℂ) + (p.2 : ℂ) * I) (by rw [hre]; linarith [hp.1.1])
      (by rw [hre]; linarith [hp.1.2])
    exact (ContinuousAt.comp (g := mellin fun u : ℝ => kadiriTestFn f s (Real.log u))
      (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
      han.continuousAt (by fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  have hB0 : 0 ≤ B :=
    le_trans (norm_nonneg _) (hB (a, 0) ⟨⟨le_refl a, hab⟩, ⟨by linarith, hY₀0.le⟩⟩)
  refine ⟨max C₀ (B * Y₀ ^ 2), fun x hx t ht => ?_⟩
  have hxmem := hx
  rw [Set.uIcc_of_le hab] at hxmem
  have ht0 : (0 : ℝ) < t ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (lt_of_lt_of_le one_pos ht) 2
  by_cases hY : Y₀ ≤ |t|
  · -- the strip-decay regime
    have hform := kadiriTestFn_mellin_eq hd hf_C2 hf_supp s
      (w := (x : ℂ) + (t : ℂ) * I) (by simpa using lt_of_le_of_lt hxmem.2 hbs)
    rw [hform]
    refine le_trans (hC₀ x t hxmem.2 (by rw [hY₀def] at hY; exact hY)) ?_
    gcongr
    exact le_max_left _ _
  · -- the compact middle
    have hmem : ((x, t) : ℝ × ℝ) ∈ Set.Icc a b ×ˢ Set.Icc (-Y₀) Y₀ := by
      refine ⟨hxmem, ?_, ?_⟩
      · linarith [neg_abs_le t, not_le.mp hY]
      · linarith [le_abs_self t, not_le.mp hY]
    refine le_trans (hB (x, t) hmem) ?_
    have htY : t ^ 2 ≤ Y₀ ^ 2 := by
      rw [← sq_abs t, ← sq_abs Y₀, abs_of_pos hY₀0]
      have := not_le.mp hY
      nlinarith [abs_nonneg t]
    rw [le_div_iff₀ ht0]
    calc B * t ^ 2 ≤ B * Y₀ ^ 2 := by nlinarith
      _ ≤ max C₀ (B * Y₀ ^ 2) := le_max_right _ _

/-! ## Line integrability -/

lemma kadiriTestFn_mellin_verticalIntegrable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ)
    {σ : ℝ} (hσ2 : -2 < σ) (hσs : σ < s.re) :
    VerticalIntegrable (mellin fun t : ℝ => kadiriTestFn f s (Real.log t)) σ := by
  obtain ⟨C, hC⟩ := kadiriTestFn_mellin_band_decay hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s (a := σ) (b := σ) hσ2 le_rfl hσs
  have hσmem : σ ∈ Set.uIcc σ σ := Set.left_mem_uIcc
  have hC0 : 0 ≤ C := by
    have h1 := hC σ hσmem 1 (by norm_num)
    have := norm_nonneg (mellin (fun t : ℝ => kadiriTestFn f s (Real.log t))
      ((σ : ℂ) + (1 : ℝ) * I))
    nlinarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hcont : Continuous fun t : ℝ =>
      mellin (fun u : ℝ => kadiriTestFn f s (Real.log u)) ((σ : ℂ) + (t : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have hre : ((σ : ℂ) + (t₀ : ℂ) * I).re = σ := by simp
    have han := kadiriTestFn_mellin_analyticAt hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      (w := (σ : ℂ) + (t₀ : ℂ) * I) (by rw [hre]; exact hσ2) (by rw [hre]; exact hσs)
    exact ContinuousAt.comp (g := mellin fun u : ℝ => kadiriTestFn f s (Real.log u))
      (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) han.continuousAt (by fun_prop)
  refine integrable_of_norm_le_log_div_sq (C := C / Real.log 2) hcont fun t ht => ?_
  have hL2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  have ht0 : (0 : ℝ) < t ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (lt_of_lt_of_le one_pos ht) 2
  refine le_trans (hC σ hσmem t ht) ?_
  rw [div_le_div_iff_of_pos_right ht0, div_mul_eq_mul_div, le_div_iff₀ hlog2]
  exact mul_le_mul_of_nonneg_left hL2 hC0

/-! ## The two endpoints at the test function -/

/-- The right-line inversion identity holds at the Kadiri test function, for
any line `1 < σR < Re s`. -/
theorem u8RightLineInversionHypothesis_kadiriTestFn {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) {s : ℂ}
    {σR : ℝ} (hσR : 1 < σR) (hσRs : σR < s.re) :
    U8RightLineInversionHypothesis (kadiriTestFn f s) (u8Phi (kadiriTestFn f s)) σR := by
  have hglob := (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s).continuous
  exact u8RightLineInversionHypothesis_of_mellin_data hσR
    (fun y hy => kadiriTestFn_neg f s hy)
    (kadiriTestFn_mellinConvergent hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      (by linarith) hσRs)
    (kadiriTestFn_mellin_verticalIntegrable hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      (by linarith) hσRs)
    (fun n _ => hglob.continuousAt)

/-- The left-line functional-equation split holds at the Kadiri test function,
for any line `-2 < σL < 0`, provided `1 < Re s`. -/
theorem u8LeftLineFunctionalEquationSplitHypothesis_kadiriTestFn {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) {s : ℂ} (hs : 1 < s.re)
    {σL : ℝ} (hσL2 : -2 < σL) (hσL0 : σL < 0) :
    U8LeftLineFunctionalEquationSplitHypothesis (kadiriTestFn f s)
      (u8Phi (kadiriTestFn f s)) σL := by
  have hglob := (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s).continuous
  obtain ⟨CΦ, hCΦ⟩ := kadiriTestFn_mellin_band_decay hd hf_C2 hf_supp hf_d hf_deriv_0
    hf_deriv_d s (a := σL) (b := (1 / 2 : ℝ)) hσL2 (by linarith) (by linarith)
  exact u8LeftLineFunctionalEquationSplitHypothesis_of_mellin_data hσL2 hσL0
    (fun y hy => kadiriTestFn_neg f s hy)
    hglob.continuousAt
    (kadiriTestFn_mellinConvergent hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      hσL2 (by linarith))
    (kadiriTestFn_mellin_verticalIntegrable hd hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d s
      hσL2 (by linarith))
    (fun w hw1 hw2 => kadiriTestFn_mellin_analyticAt hd hf_C2 hf_supp hf_d hf_deriv_0
      hf_deriv_d s (by linarith) (by linarith))
    hCΦ

end

end Kadiri
