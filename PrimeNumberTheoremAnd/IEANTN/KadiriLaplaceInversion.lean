import PrimeNumberTheoremAnd.IEANTN.Kadiri
import Mathlib.Analysis.MellinInversion

/-!
# Mellin-side inversion bridge for the Kadiri explicit-formula lane

This file packages the fixed-line inversion step used before any contour
shift.  The multiplicative test function is `x ↦ φ (log x)`, whose Mellin
transform is the Laplace transform `Φ (-s)` after the change of variables
`x = exp y`.
-/

namespace Kadiri

open Complex MeasureTheory
open ArithmeticFunction hiding log
open Filter Set Asymptotics
open scoped Topology

noncomputable section

private theorem rexpNegDeriv :
    ∀ x ∈ Set.univ, HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexpNeg_image_univ : Real.exp ∘ Neg.neg '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexpNeg_injOn_univ : Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)

private theorem rexp_smul_cpow (x : ℝ) (s z : ℂ) :
    Real.exp (-x) • Complex.exp (-(x : ℂ)) ^ (s - 1) • z =
      Complex.exp (-s * (x : ℂ)) • z := by
  change (Real.exp (-x) : ℂ) * (Complex.exp (-(x : ℂ)) ^ (s - 1) * z) =
    Complex.exp (-s * (x : ℂ)) * z
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc]
  nth_rewrite 1 [← cpow_one (Complex.exp (-(x : ℂ)))]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

private theorem integral_comp_neg_univ (F : ℝ → ℂ) :
    (∫ x : ℝ, F (-x)) = ∫ x : ℝ, F x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h := A.integral_map (μ := volume) F
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  simpa using h.symm

private lemma eq_zero_of_tsupport_subset_Ico_left {d : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (hx : x < 0) : f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact not_le_of_gt hx (hf_supp hmem).1

private lemma eq_zero_zero_of_continuous_tsupport_subset_Ico {d : ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_supp : tsupport f ⊆ Set.Ico 0 d) : f 0 = 0 := by
  have hseq : Tendsto (fun n : ℕ => -((1 : ℝ) / (n + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hf_tend : Tendsto (fun n : ℕ => f (-((1 : ℝ) / (n + 1)))) atTop (𝓝 (f 0)) :=
    hf_cont.continuousAt.tendsto.comp hseq
  have hzero : (fun n : ℕ => f (-((1 : ℝ) / (n + 1)))) = fun _ => (0 : ℝ) := by
    funext n
    apply eq_zero_of_tsupport_subset_Ico_left hf_supp
    have hpos : 0 < (1 : ℝ) / (n + 1) := by positivity
    linarith
  have hzero_tend : Tendsto (fun n : ℕ => f (-((1 : ℝ) / (n + 1)))) atTop (𝓝 (0 : ℝ)) := by
    rw [hzero]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hzero_tend hf_tend).symm

private lemma eq_zero_of_tsupport_subset_Ico_right {d : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (hdx : d ≤ x) : f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact not_lt_of_ge hdx (hf_supp hmem).2

private lemma laplaceTransform_eq_interval_of_tsupport_subset_Ico {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ Set.Ico 0 d) (w : ℂ) :
    laplaceTransform f w = ∫ t in (0 : ℝ)..d, exp (-w * (t : ℂ)) * (f t : ℂ) := by
  unfold laplaceTransform
  rw [intervalIntegral.integral_of_le hd.le]
  exact setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self (fun x hx => by
      have hxpos : 0 < x := hx.1
      have hdx : d ≤ x := by
        by_contra hnot
        exact hx.2 ⟨hxpos, le_of_not_ge hnot⟩
      simp [eq_zero_of_tsupport_subset_Ico_right hf_supp hdx])

private lemma real_to_complex_tsupport_subset_Icc {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) :
    tsupport (fun x : ℝ => ((f x : ℝ) : ℂ)) ⊆ Set.Icc 0 d := by
  refine (tsupport_comp_subset (g := fun x : ℝ => ((x : ℝ) : ℂ)) (by simp) f).trans ?_
  intro x hx
  exact ⟨(hf_supp hx).1, (hf_supp hx).2.le⟩

private theorem kadiriMellin_log_eq_integral (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun t : ℝ => ((f (Real.log t) : ℝ) : ℂ)) s =
      ∫ y : ℝ, Complex.exp (s * (y : ℂ)) * (f y : ℂ) := by
  calc
    mellin (fun t : ℝ => ((f (Real.log t) : ℝ) : ℂ)) s
        = ∫ u : ℝ, Complex.exp (-s * (u : ℂ)) * (f (-u) : ℂ) := by
          rw [mellin, ← rexpNeg_image_univ, integral_image_eq_integral_abs_deriv_smul
            MeasurableSet.univ rexpNegDeriv rexpNeg_injOn_univ]
          rw [setIntegral_univ]
          congr with x
          simpa [Function.comp_def, Real.log_exp, abs_of_pos (Real.exp_pos (-x)), smul_eq_mul,
            mul_assoc] using rexp_smul_cpow x s ((f (-x) : ℝ) : ℂ)
    _ = ∫ y : ℝ, Complex.exp (s * (y : ℂ)) * (f y : ℂ) := by
          rw [← integral_comp_neg_univ (fun y : ℝ => Complex.exp (s * (y : ℂ)) * (f y : ℂ))]
          congr
          ext u
          simp

private lemma integral_exp_mul_eq_laplaceTransform_neg {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) :
    (∫ y : ℝ, Complex.exp (s * (y : ℂ)) * (f y : ℂ)) = laplaceTransform f (-s) := by
  calc
    (∫ y : ℝ, Complex.exp (s * (y : ℂ)) * (f y : ℂ))
        = ∫ y in Set.Ici (0 : ℝ), Complex.exp (s * (y : ℂ)) * (f y : ℂ) := by
          rw [← setIntegral_univ]
          exact setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
            (Set.subset_univ _) (fun x hx => by
              have hxneg : x < 0 := lt_of_not_ge hx.2
              simp [eq_zero_of_tsupport_subset_Ico_left hf_supp hxneg])
    _ = ∫ y in Set.Ioi (0 : ℝ), Complex.exp (s * (y : ℂ)) * (f y : ℂ) := by
          rw [integral_Ici_eq_integral_Ioi]
    _ = laplaceTransform f (-s) := by
          unfold laplaceTransform
          refine (setIntegral_congr_fun (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
            fun y _ => ?_).symm
          simp

/-- Logarithmic change of variables for the Kadiri real test-function class:
the Mellin transform of `t ↦ f (log t)` is the in-tree Laplace transform at
`-s`. -/
theorem kadiriMellin_log_eq_laplaceTransform {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) :
    mellin (fun t : ℝ => ((f (Real.log t) : ℝ) : ℂ)) s = laplaceTransform f (-s) := by
  rw [kadiriMellin_log_eq_integral]
  exact integral_exp_mul_eq_laplaceTransform_neg hf_supp s

/-- The Mellin-line transform after subtracting the high-frequency
`f 0 / w` Laplace pole, written in the `s` variable where `w = -s`. -/
noncomputable def kadiriPoleSubtractedMellin (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  laplaceTransform f (-s) + (f 0 : ℂ) / s

/-- The Perron kernel carried by the `f 0 / w` pole term on the right Mellin
line.  The weighted Kadiri consumer only evaluates it at integers `n > 1`,
where it vanishes. -/
noncomputable def kadiriPoleKernel (x : ℝ) : ℂ :=
  if 1 < x then 0 else -1

theorem kadiriPoleKernel_of_one_lt {x : ℝ} (hx : 1 < x) :
    kadiriPoleKernel x = 0 := by
  simp [kadiriPoleKernel, hx]

theorem kadiriPoleKernel_of_lt_one {x : ℝ} (hx : x < 1) :
    kadiriPoleKernel x = -1 := by
  simp [kadiriPoleKernel, not_lt.mpr hx.le]

/-- The multiplicative test function whose Mellin transform is the
pole-subtracted line transform on a right half-plane: fill the interval
`0 < t < 1` with the endpoint value `f 0`, then use `f (log t)` to the
right of `1`. -/
noncomputable def kadiriPoleFilledLogFunction (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  if t < 1 then (f 0 : ℂ) else (f (Real.log t) : ℂ)

theorem kadiriPoleFilledLogFunction_of_one_lt {f : ℝ → ℝ} {x : ℝ} (hx : 1 < x) :
    kadiriPoleFilledLogFunction f x = (f (Real.log x) : ℂ) := by
  simp [kadiriPoleFilledLogFunction, not_lt.mpr hx.le]

/-- The explicit Mellin kernel contributed by the filled interval `0 < t < 1`.
This is the `f 0 / s` term in the pole-subtracted transform identity. -/
theorem kadiriPoleKernelIntegral {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (s - 1)) = 1 / s := by
  rw [integral_cpow (r := s - 1) (a := (0 : ℝ)) (b := 1)]
  · have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    simp [hs0]
  · left
    simpa using hs

/-- Pole-split fixed-line inversion expression: the line-integrable
pole-subtracted Mellin inverse plus the explicit Perron kernel carried by the
`f 0 / w` term. -/
noncomputable def kadiriPoleSplitMellinInv (σ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℂ :=
  mellinInv σ (kadiriPoleSubtractedMellin f) x + (f 0 : ℂ) * kadiriPoleKernel x

/-- Mellin inversion for the pole-subtracted transform once the pole-filled
function has been identified as its Mellin-side source. -/
theorem kadiriPoleSubtracted_mellinInv_eq_of_poleFilled
    {σ x : ℝ} {f : ℝ → ℝ} (hx : 0 < x)
    (hMellin : MellinConvergent (kadiriPoleFilledLogFunction f) (σ : ℂ))
    (hTransform : ∀ s : ℂ,
      mellin (kadiriPoleFilledLogFunction f) s = kadiriPoleSubtractedMellin f s)
    (hVertical : VerticalIntegrable (kadiriPoleSubtractedMellin f) σ)
    (hCont : ContinuousAt (kadiriPoleFilledLogFunction f) x) :
    mellinInv σ (kadiriPoleSubtractedMellin f) x =
      kadiriPoleFilledLogFunction f x := by
  have hVertical' : VerticalIntegrable (mellin (kadiriPoleFilledLogFunction f)) σ := by
    dsimp [VerticalIntegrable] at hVertical ⊢
    exact hVertical.congr (Eventually.of_forall fun y => (hTransform (σ + y * I)).symm)
  calc
    mellinInv σ (kadiriPoleSubtractedMellin f) x
        = mellinInv σ (mellin (kadiriPoleFilledLogFunction f)) x := by
          dsimp [mellinInv]
          simp_rw [← hTransform]
    _ = kadiriPoleFilledLogFunction f x :=
          mellinInv_mellin_eq σ (f := kadiriPoleFilledLogFunction f) hx
            hMellin hVertical' hCont

private lemma laplaceLine_continuous {d σ : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_supp : tsupport f ⊆ Set.Ico 0 d) :
    Continuous fun y : ℝ => laplaceTransform f (-(σ + y * I)) := by
  have hcont_int : Continuous fun y : ℝ =>
      ∫ t in (0 : ℝ)..d, exp (-(-(σ + y * I)) * (t : ℂ)) * (f t : ℂ) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ (0 : ℝ) d
    change Continuous fun p : ℝ × ℝ => exp (-(-(σ + p.1 * I)) * (p.2 : ℂ)) * (f p.2 : ℂ)
    fun_prop
  refine hcont_int.congr ?_
  intro y
  exact (laplaceTransform_eq_interval_of_tsupport_subset_Ico hd hf_supp (-(σ + y * I))).symm

private lemma laplaceLine_continuous_of_contDiffOn {d σ : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) :
    Continuous fun y : ℝ => laplaceTransform f (-(σ + y * I)) := by
  have hf_contOn : ContinuousOn f (Set.Icc 0 d) := hf_C2.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp_continuousOn hf_contOn)
  let K' : ℝ := max K 0
  have hK' : ∀ t ∈ Set.Icc (0 : ℝ) d, ‖((f t : ℝ) : ℂ)‖ ≤ K' := by
    intro t ht
    exact (hK t ht).trans (le_max_left K 0)
  let B : ℝ := Real.exp (max σ 0 * d) * K'
  have hB0 : 0 ≤ B := by
    exact mul_nonneg (Real.exp_pos _).le (le_max_right K 0)
  have hcont_int : Continuous fun y : ℝ =>
      ∫ t in (0 : ℝ)..d, exp (-(-(σ + y * I)) * (t : ℂ)) * (f t : ℂ) := by
    refine intervalIntegral.continuous_of_dominated_interval
      (bound := fun _ : ℝ => B) ?_ ?_ ?_ ?_
    · intro y
      have hcont : ContinuousOn
          (fun t : ℝ => exp (-(-(σ + y * I)) * (t : ℂ)) * (f t : ℂ))
          (Set.uIcc (0 : ℝ) d) := by
        refine (Continuous.continuousOn ?_).mul
          ((Complex.continuous_ofReal.comp_continuousOn hf_contOn).mono ?_)
        · fun_prop
        · intro t ht
          simpa [Set.uIcc, min_eq_left hd.le, max_eq_right hd.le] using ht
      exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · intro y
      filter_upwards with t ht
      rw [norm_mul, Complex.norm_exp]
      have htIcc : t ∈ Set.Icc (0 : ℝ) d := by
        simpa [Set.uIcc, min_eq_left hd.le, max_eq_right hd.le] using
          (Set.uIoc_subset_uIcc ht)
      have hre : (-(-(σ + y * I)) * (t : ℂ)).re = σ * t := by
        simp [Complex.mul_re]
      have hexp : Real.exp ((-(-(σ + y * I)) * (t : ℂ)).re) ≤
          Real.exp (max σ 0 * d) := by
        rw [hre]
        apply Real.exp_le_exp.2
        have hσ : σ ≤ max σ 0 := le_max_left σ 0
        have hσ0 : 0 ≤ max σ 0 := le_max_right σ 0
        calc σ * t ≤ max σ 0 * t := mul_le_mul_of_nonneg_right hσ htIcc.1
          _ ≤ max σ 0 * d := mul_le_mul_of_nonneg_left htIcc.2 hσ0
      exact mul_le_mul hexp (hK' t htIcc) (norm_nonneg _) (Real.exp_pos _).le
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      fun_prop
  refine hcont_int.congr ?_
  intro y
  exact (laplaceTransform_eq_interval_of_tsupport_subset_Ico hd hf_supp (-(σ + y * I))).symm

private lemma rpow_neg_two_integrableAtFilter_atTop :
    IntegrableAtFilter (fun y : ℝ => |y| ^ (-(2 : ℝ))) Filter.atTop volume := by
  refine ⟨Set.Ioi 1, Filter.Ioi_mem_atTop 1, ?_⟩
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) zero_lt_one).congr_fun
    (fun y hy => ?_) measurableSet_Ioi
  exact congrArg (· ^ (-(2 : ℝ)))
    (abs_of_pos (zero_lt_one.trans_le (Set.mem_Ioi.mp hy).le)).symm

private lemma laplaceLine_decay_bound {d σ : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) :
    ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 →
      ‖laplaceTransform f (-(σ + y * I))‖ ≤ C * ‖|y| ^ (-(2 : ℝ))‖ := by
  have hf0 : f 0 = 0 := eq_zero_zero_of_continuous_tsupport_subset_Ico hf_cont hf_supp
  obtain ⟨C, hC⟩ := laplaceTransform_sub_pole_norm_decay hd hf_C2 hf_supp hf_d
    hf_deriv_0 hf_deriv_d (-σ)
  refine ⟨max 0 C, fun y hy => ?_⟩
  set w : ℂ := -((y : ℂ) * I) + -(σ : ℂ)
  have hw_orig : w = -(σ + y * I) := by
    simp [w, add_comm]
  have hwre : -σ ≤ w.re := by simp [w]
  have hwim : w.im ≠ 0 := by simp [w, hy]
  have hdecay := hC w hwre hwim
  have hzero : ((f 0 : ℝ) : ℂ) / w = 0 := by simp [hf0]
  calc
    ‖laplaceTransform f (-(σ + y * I))‖
        = ‖laplaceTransform f w‖ := by rw [hw_orig]
    _ = ‖((f 0 : ℝ) : ℂ) / w - laplaceTransform f w‖ := by
          simp [hzero]
    _ ≤ C / w.im ^ 2 := hdecay
    _ ≤ max 0 C / w.im ^ 2 := by
          gcongr
          exact le_max_right 0 C
    _ = max 0 C * ‖|y| ^ (-(2 : ℝ))‖ := by
          rw [div_eq_mul_inv, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _),
            Real.rpow_neg (abs_nonneg y)]
          simp [w, pow_two]

/-- Vertical integrability of the pole-subtracted Kadiri Mellin line under the
real Kadiri test-function surface.  This is the line-integrable half of the
pole split; no global continuity of `f` is used. -/
theorem kadiriPoleSubtractedVerticalIntegrable_of_laplaceDecay {d σ : ℝ}
    (hd : 0 < d) (hσ : σ ≠ 0) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) :
    VerticalIntegrable (kadiriPoleSubtractedMellin f) σ := by
  dsimp [VerticalIntegrable]
  let line : ℝ → ℂ := fun y => kadiriPoleSubtractedMellin f (σ + y * I)
  have hden : ∀ y : ℝ, σ + y * I ≠ 0 := by
    intro y h
    have hre : σ = 0 := by
      simpa using congrArg Complex.re h
    exact hσ hre
  have hline_cont : Continuous line := by
    dsimp [line, kadiriPoleSubtractedMellin]
    exact (laplaceLine_continuous_of_contDiffOn (d := d) (σ := σ) hd hf_C2 hf_supp).add
      (continuous_const.div (by fun_prop) hden)
  have h_loc : LocallyIntegrable line := hline_cont.locallyIntegrable
  obtain ⟨C, hC⟩ := laplaceTransform_sub_pole_norm_decay hd hf_C2 hf_supp hf_d
    hf_deriv_0 hf_deriv_d (-σ)
  have h_int_top := rpow_neg_two_integrableAtFilter_atTop
  have h_int_bot : IntegrableAtFilter (fun y : ℝ => |y| ^ (-(2 : ℝ))) Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
      simp
    rw [this, Function.comp_def]
    simp only [abs_neg]
    exact h_int_top
  have hbound : ∃ C' : ℝ, ∀ y : ℝ, y ≠ 0 →
      ‖line y‖ ≤ C' * ‖|y| ^ (-(2 : ℝ))‖ := by
    refine ⟨max 0 C, fun y hy => ?_⟩
    set w : ℂ := -(σ + y * I)
    have hwre : -σ ≤ w.re := by simp [w]
    have hwim : w.im ≠ 0 := by simp [w, hy]
    have hdecay := hC w hwre hwim
    have hline :
        line y = -(((f 0 : ℝ) : ℂ) / w - laplaceTransform f w) := by
      have hs_eq : (σ + y * I : ℂ) = -w := by
        simp [w]
      dsimp [line, kadiriPoleSubtractedMellin]
      rw [hs_eq]
      simp
      ring_nf
    calc
      ‖line y‖ = ‖((f 0 : ℝ) : ℂ) / w - laplaceTransform f w‖ := by
          rw [hline, norm_neg]
      _ ≤ C / w.im ^ 2 := hdecay
      _ ≤ max 0 C / w.im ^ 2 := by
          gcongr
          exact le_max_right 0 C
      _ = max 0 C * ‖|y| ^ (-(2 : ℝ))‖ := by
          rw [div_eq_mul_inv, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _),
            Real.rpow_neg (abs_nonneg y)]
          simp [w, pow_two]
  obtain ⟨C', hC'⟩ := hbound
  have h_line_int : Integrable line := by
    apply h_loc.integrable_of_isBigO_atBot_atTop
      (g := fun y : ℝ => |y| ^ (-(2 : ℝ)))
      (g' := fun y : ℝ => |y| ^ (-(2 : ℝ)))
    · apply IsBigO.of_bound C'
      filter_upwards [Filter.eventually_ne_atBot 0] with y hy using hC' y hy
    · exact h_int_bot
    · apply IsBigO.of_bound C'
      filter_upwards [Filter.eventually_ne_atTop 0] with y hy using hC' y hy
    · exact h_int_top
  exact h_line_int

/-- Vertical integrability of the Mellin transform after the logarithmic
change of variables, obtained from the Kadiri two-IBP decay theorem.  The raw
Laplace transform needs `f 0 = 0`, derived here from continuity and
`tsupport f ⊆ Ico 0 d`; otherwise the in-tree theorem only gives `O(1/|Im|²)`
for the pole-subtracted transform. -/
theorem kadiriVerticalIntegrable_mellin_log_of_laplaceDecay {d σ : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) :
    VerticalIntegrable (mellin (fun t : ℝ => ((f (Real.log t) : ℝ) : ℂ))) σ := by
  dsimp [VerticalIntegrable]
  let line : ℝ → ℂ := fun y => laplaceTransform f (-(σ + y * I))
  have hline_cont : Continuous line := laplaceLine_continuous hd hf_cont hf_supp
  have h_loc : LocallyIntegrable line := hline_cont.locallyIntegrable
  obtain ⟨C, hC⟩ := laplaceLine_decay_bound (σ := σ) hd hf_cont hf_C2 hf_supp hf_d
    hf_deriv_0 hf_deriv_d
  have h_int_top := rpow_neg_two_integrableAtFilter_atTop
  have h_int_bot : IntegrableAtFilter (fun y : ℝ => |y| ^ (-(2 : ℝ))) Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
      simp
    rw [this, Function.comp_def]
    simp only [abs_neg]
    exact h_int_top
  have h_line_int : Integrable line := by
    apply h_loc.integrable_of_isBigO_atBot_atTop
      (g := fun y : ℝ => |y| ^ (-(2 : ℝ)))
      (g' := fun y : ℝ => |y| ^ (-(2 : ℝ)))
    · apply IsBigO.of_bound C
      filter_upwards [Filter.eventually_ne_atBot 0] with y hy using hC y hy
    · exact h_int_bot
    · apply IsBigO.of_bound C
      filter_upwards [Filter.eventually_ne_atTop 0] with y hy using hC y hy
    · exact h_int_top
  refine h_line_int.congr ?_
  filter_upwards with y
  dsimp [line]
  rw [kadiriMellin_log_eq_laplaceTransform hf_supp]

/-- Compact support in the additive Kadiri variable gives Mellin convergence
after the logarithmic change of variables. -/
theorem kadiriMellinConvergent_log_of_tsupport_subset_Icc {d σ : ℝ} {φ : ℝ → ℂ}
    (hφ_cont : Continuous φ) (hφ_supp : tsupport φ ⊆ Set.Icc 0 d) :
    MellinConvergent (fun t : ℝ => φ (Real.log t)) (σ : ℂ) := by
  have hfc : LocallyIntegrableOn (fun t : ℝ => φ (Real.log t)) (Set.Ioi 0) := by
    apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    exact continuousOn_of_forall_continuousAt fun t ht =>
      hφ_cont.continuousAt.comp (Real.continuousAt_log (ne_of_gt ht))
  have htop_zero : (fun t : ℝ => φ (Real.log t)) =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [eventually_gt_atTop (Real.exp d)] with t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have htpos : 0 < t := (Real.exp_pos d).trans ht
    have hlog_gt : d < Real.log t := by
      rw [← Real.exp_lt_exp, Real.exp_log htpos]
      exact ht
    exact not_lt_of_ge (hφ_supp hmem).2 hlog_gt
  have htop : (fun t : ℝ => φ (Real.log t)) =O[atTop] fun t : ℝ => t ^ (-(σ + 1)) :=
    htop_zero.trans_isBigO (isBigO_zero _ _)
  have hbot_zero : (fun t : ℝ => φ (Real.log t)) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)]
      with t htpos htlt
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hlog_neg : Real.log t < 0 := Real.log_neg htpos htlt
    exact not_le_of_gt hlog_neg (hφ_supp hmem).1
  have hbot : (fun t : ℝ => φ (Real.log t)) =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(σ - 1)) :=
    hbot_zero.trans_isBigO (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow (a := σ + 1) (b := σ - 1) hfc htop
    (by simp) hbot (by simp)

/-- Continuity at the multiplicative point follows from continuity of the
additive test function at its logarithm. -/
theorem kadiriContinuousAt_log_comp {φ : ℝ → ℂ} {x : ℝ} (hx : 0 < x)
    (hφx : ContinuousAt φ (Real.log x)) :
    ContinuousAt (fun t : ℝ => φ (Real.log t)) x := by
  exact hφx.comp (Real.continuousAt_log hx.ne')

/-- The pointwise Mellin-inversion bridge for the Kadiri Laplace variable.

Applied to `g x = φ (log x)`, mathlib's Mellin inversion theorem recovers
`φ (log x)` from the vertical-line integral of `mellin g`.  The analytic
content is exactly the three standard hypotheses of `mellinInv_mellin_eq`.
-/
theorem kadiriMellinInv_mellin_log_eq {φ : ℝ → ℂ} {σ x : ℝ} (hx : 0 < x)
    (hMellin : MellinConvergent (fun t : ℝ => φ (Real.log t)) (σ : ℂ))
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ)
    (hφx : ContinuousAt φ (Real.log x)) :
    mellinInv σ (mellin (fun t : ℝ => φ (Real.log t))) x = φ (Real.log x) := by
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx.ne'
  exact mellinInv_mellin_eq σ (f := fun t : ℝ => φ (Real.log t)) hx hMellin hVertical
    (hφx.comp hlog)

/-- The same inversion bridge unfolded to the vertical-line integral. -/
theorem kadiriVerticalIntegral_mellin_log_eq {φ : ℝ → ℂ} {σ x : ℝ} (hx : 0 < x)
    (hMellin : MellinConvergent (fun t : ℝ => φ (Real.log t)) (σ : ℂ))
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ)
    (hφx : ContinuousAt φ (Real.log x)) :
    (1 / (2 * Real.pi)) •
        (∫ y : ℝ,
          ((x : ℂ) ^ (-(σ + y * I)) •
            mellin (fun t : ℝ => φ (Real.log t)) (σ + y * I))) =
      φ (Real.log x) := by
  simpa [mellinInv] using
    kadiriMellinInv_mellin_log_eq (φ := φ) (σ := σ) (x := x) hx hMellin hVertical hφx

/-- Compact-support wrapper for the pointwise inversion bridge.  The support
hypothesis discharges `MellinConvergent`, and continuity of `φ` discharges the
pointwise continuity hypothesis of mathlib's inversion theorem. -/
theorem kadiriCompactSupport_mellinInv_mellin_log_eq {d σ x : ℝ} {φ : ℝ → ℂ}
    (hx : 0 < x) (hφ_cont : Continuous φ) (hφ_supp : tsupport φ ⊆ Set.Icc 0 d)
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ) :
    mellinInv σ (mellin (fun t : ℝ => φ (Real.log t))) x = φ (Real.log x) := by
  exact kadiriMellinInv_mellin_log_eq (φ := φ) (σ := σ) (x := x) hx
    (kadiriMellinConvergent_log_of_tsupport_subset_Icc
      (σ := σ) hφ_cont hφ_supp)
    hVertical hφ_cont.continuousAt

/-- Compact-support pointwise inversion for real Kadiri test functions, with
`VerticalIntegrable` discharged by the logarithmic Mellin-Laplace identity and
the in-tree two-IBP Laplace decay theorem. -/
theorem kadiriCompactSupport_mellinInv_mellin_log_eq_of_laplaceDecay {d σ x : ℝ}
    (hd : 0 < d) (hx : 0 < x) {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) :
    mellinInv σ (mellin (fun t : ℝ => ((f (Real.log t) : ℝ) : ℂ))) x =
      (f (Real.log x) : ℂ) := by
  let φ : ℝ → ℂ := fun y => (f y : ℂ)
  have hφ_cont : Continuous φ := by
    exact Complex.continuous_ofReal.comp hf_cont
  exact kadiriMellinInv_mellin_log_eq (φ := φ) (σ := σ) (x := x) hx
    (kadiriMellinConvergent_log_of_tsupport_subset_Icc
      (d := d) (σ := σ) hφ_cont (real_to_complex_tsupport_subset_Icc hf_supp))
    (kadiriVerticalIntegrable_mellin_log_of_laplaceDecay (d := d) (σ := σ) hd
      hf_cont hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d)
    hφ_cont.continuousAt

/-- Weighted fixed-line inversion.  The zero-index guard matches the
von-Mangoldt weights, where `Λ 0 = 0`, and avoids asking Mellin inversion at
the non-positive point `0`. -/
theorem kadiriMellinInv_weighted_log_sum_eq {φ : ℝ → ℂ} {σ : ℝ} (a : ℕ → ℂ)
    (ha0 : a 0 = 0)
    (hMellin : MellinConvergent (fun t : ℝ => φ (Real.log t)) (σ : ℂ))
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ)
    (hφ : ∀ n : ℕ, n ≠ 0 → ContinuousAt φ (Real.log n)) :
    (∑' n : ℕ, a n * mellinInv σ (mellin (fun t : ℝ => φ (Real.log t))) n) =
      ∑' n : ℕ, a n * φ (Real.log n) := by
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  · rw [kadiriMellinInv_mellin_log_eq (φ := φ) (σ := σ) (x := (n : ℝ))
      (by exact_mod_cast hn) hMellin hVertical (hφ n hn.ne')]

/-- Von-Mangoldt-weighted fixed-line inversion, the form used in the
Dirichlet-series step of the Kadiri explicit formula. -/
theorem kadiriMellinInv_vonMangoldt_log_sum_eq {φ : ℝ → ℂ} {σ : ℝ}
    (hMellin : MellinConvergent (fun t : ℝ => φ (Real.log t)) (σ : ℂ))
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ)
    (hφ : ∀ n : ℕ, n ≠ 0 → ContinuousAt φ (Real.log n)) :
    (∑' n : ℕ, (Λ n : ℂ) * mellinInv σ (mellin (fun t : ℝ => φ (Real.log t))) n) =
      ∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n) := by
  refine kadiriMellinInv_weighted_log_sum_eq (φ := φ) (σ := σ)
    (fun n : ℕ => (Λ n : ℂ)) ?_ hMellin hVertical hφ
  simp

/-- Compact-support wrapper for weighted fixed-line inversion. -/
theorem kadiriCompactSupport_mellinInv_weighted_log_sum_eq {d σ : ℝ} {φ : ℝ → ℂ}
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (hφ_cont : Continuous φ) (hφ_supp : tsupport φ ⊆ Set.Icc 0 d)
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ) :
    (∑' n : ℕ, a n * mellinInv σ (mellin (fun t : ℝ => φ (Real.log t))) n) =
      ∑' n : ℕ, a n * φ (Real.log n) := by
  exact kadiriMellinInv_weighted_log_sum_eq (φ := φ) (σ := σ) a ha0
    (kadiriMellinConvergent_log_of_tsupport_subset_Icc
      (σ := σ) hφ_cont hφ_supp)
    hVertical (fun _ _ => hφ_cont.continuousAt)

/-- Weighted compact-support inversion for real Kadiri test functions, with
`VerticalIntegrable` discharged from the Laplace-side decay theorem. -/
theorem kadiriCompactSupport_mellinInv_weighted_log_sum_eq_of_laplaceDecay {d σ : ℝ}
    (hd : 0 < d) {f : ℝ → ℝ} (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (hf_cont : Continuous f)
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) :
    (∑' n : ℕ,
        a n * mellinInv σ (mellin (fun t : ℝ => ((f (Real.log t) : ℝ) : ℂ))) n) =
      ∑' n : ℕ, a n * (f (Real.log n) : ℂ) := by
  let φ : ℝ → ℂ := fun y => (f y : ℂ)
  have hφ_cont : Continuous φ := by
    exact Complex.continuous_ofReal.comp hf_cont
  exact kadiriMellinInv_weighted_log_sum_eq (φ := φ) (σ := σ) a ha0
    (kadiriMellinConvergent_log_of_tsupport_subset_Icc
      (d := d) (σ := σ) hφ_cont (real_to_complex_tsupport_subset_Icc hf_supp))
    (kadiriVerticalIntegrable_mellin_log_of_laplaceDecay (d := d) (σ := σ) hd
      hf_cont hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d)
    (fun _ _ => hφ_cont.continuousAt)

/-- Weighted pole-split wrapper for the real Kadiri class.  The discharged
content here is the line-integrability of the pole-subtracted transform and
the explicit Perron-kernel contribution at the weighted integer points.  The
remaining analytic inputs identify the pole-filled function as the Mellin-side
source of the pole-subtracted transform. -/
theorem kadiriPoleSplit_mellinInv_weighted_log_sum_eq_of_laplaceDecay {d σ : ℝ}
    (hd : 0 < d) (hσ : σ ≠ 0) {f : ℝ → ℝ} (a : ℕ → ℂ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0)
    (hMellin : MellinConvergent (kadiriPoleFilledLogFunction f) (σ : ℂ))
    (hTransform : ∀ s : ℂ,
      mellin (kadiriPoleFilledLogFunction f) s = kadiriPoleSubtractedMellin f s)
    (hCont : ∀ n : ℕ, 1 < n → ContinuousAt (kadiriPoleFilledLogFunction f) n) :
    (∑' n : ℕ, a n * kadiriPoleSplitMellinInv σ f n) =
      ∑' n : ℕ, a n * (f (Real.log n) : ℂ) := by
  have hVertical : VerticalIntegrable (kadiriPoleSubtractedMellin f) σ :=
    kadiriPoleSubtractedVerticalIntegrable_of_laplaceDecay
      (d := d) (σ := σ) hd hσ hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp [ha0]
  by_cases hn1 : n = 1
  · simp [hn1, ha1]
  have hn_gt_one : 1 < n := by omega
  have hn_gt_one_real : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt_one
  have hxpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)
  have hInvFilled :
      mellinInv σ (kadiriPoleSubtractedMellin f) n =
        kadiriPoleFilledLogFunction f n :=
    kadiriPoleSubtracted_mellinInv_eq_of_poleFilled
      (σ := σ) (x := (n : ℝ)) (f := f) hxpos hMellin hTransform hVertical
      (hCont n hn_gt_one)
  have hInv :
      mellinInv σ (kadiriPoleSubtractedMellin f) n =
        (f (Real.log n) : ℂ) := by
    exact hInvFilled.trans (kadiriPoleFilledLogFunction_of_one_lt hn_gt_one_real)
  rw [kadiriPoleSplitMellinInv, hInv, kadiriPoleKernel_of_one_lt hn_gt_one_real]
  simp

/-- Compact-support wrapper for the von-Mangoldt weighted fixed-line
inversion. -/
theorem kadiriCompactSupport_mellinInv_vonMangoldt_log_sum_eq {d σ : ℝ} {φ : ℝ → ℂ}
    (hφ_cont : Continuous φ) (hφ_supp : tsupport φ ⊆ Set.Icc 0 d)
    (hVertical : VerticalIntegrable (mellin (fun t : ℝ => φ (Real.log t))) σ) :
    (∑' n : ℕ, (Λ n : ℂ) * mellinInv σ (mellin (fun t : ℝ => φ (Real.log t))) n) =
      ∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n) := by
  exact kadiriMellinInv_vonMangoldt_log_sum_eq (φ := φ) (σ := σ)
    (kadiriMellinConvergent_log_of_tsupport_subset_Icc
      (σ := σ) hφ_cont hφ_supp)
    hVertical (fun _ _ => hφ_cont.continuousAt)

end

end Kadiri
