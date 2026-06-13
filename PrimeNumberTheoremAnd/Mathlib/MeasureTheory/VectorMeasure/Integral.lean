import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Integral

open Set MeasureTheory VectorMeasure ContinuousLinearMap
open scoped ENNReal BoundedContinuousFunction

namespace MeasureTheory

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dominatedFinMeasAdditive_cbmApplyMeasure_lsmul_variation (μ : VectorMeasure X F) :
    DominatedFinMeasAdditive μ.variation (cbmApplyMeasure μ (lsmul ℝ ℝ)) 1 := by
  refine ⟨fun _s _t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ (lsmul ℝ ℝ) hs ht hdisj,
    fun s _hs hsf ↦ ?_⟩
  calc
    ‖cbmApplyMeasure μ (lsmul ℝ ℝ) s‖
        ≤ ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ * ‖μ s‖ :=
      norm_cbmApplyMeasure_le μ (lsmul ℝ ℝ) s
    _ ≤ 1 * ‖μ s‖ := by
      exact mul_le_mul_of_nonneg_right opNorm_lsmul_le (norm_nonneg _)
    _ ≤ 1 * μ.variation.real s := by
      gcongr
      exact norm_measure_le_variation hsf.ne

theorem setToFun_lsmul_variation_eq_integral [CompleteSpace F] (μ : VectorMeasure X F)
    {g : X → ℝ} (hg : Integrable g μ.variation) :
    setToFun μ.variation (cbmApplyMeasure μ (lsmul ℝ ℝ))
        (dominatedFinMeasAdditive_cbmApplyMeasure_lsmul_variation μ) g =
      ∫ᵛ x, g x ∂•μ := by
  rw [VectorMeasure.integral]
  rw [dif_pos (inferInstance : CompleteSpace F)]
  refine setToFun_congr_measure_of_integrable 1 ENNReal.one_ne_top ?_
    (dominatedFinMeasAdditive_cbmApplyMeasure_lsmul_variation μ)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ (lsmul ℝ ℝ)) g hg
  simp only [one_smul]
  refine variation_le_of_forall_enorm_le ?_
  intro s _hs
  have hnorm : ‖(μ.transpose (lsmul ℝ ℝ)) s‖ ≤ ‖μ s‖ := by
    calc
      ‖(μ.transpose (lsmul ℝ ℝ)) s‖ = ‖cbmApplyMeasure μ (lsmul ℝ ℝ) s‖ := rfl
      _ ≤ ‖(lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)‖ * ‖μ s‖ :=
        norm_cbmApplyMeasure_le μ (lsmul ℝ ℝ) s
      _ ≤ 1 * ‖μ s‖ := by
        exact mul_le_mul_of_nonneg_right opNorm_lsmul_le (norm_nonneg _)
      _ = ‖μ s‖ := one_mul _
  have henorm : ‖(μ.transpose (lsmul ℝ ℝ)) s‖ₑ ≤ ‖μ s‖ₑ := by
    simpa [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  exact henorm.trans (enorm_measure_le_variation μ s)

theorem norm_setToFun_lsmul_variation_le_of_norm_le [CompleteSpace F] (μ : VectorMeasure X F)
    {g : X → ℝ} {C : ℝ} (hg : Integrable g μ.variation) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) (hμ : μ.variation univ ≠ ∞) :
    ‖setToFun μ.variation (cbmApplyMeasure μ (lsmul ℝ ℝ))
        (dominatedFinMeasAdditive_cbmApplyMeasure_lsmul_variation μ) g‖ ≤
      C * (μ.variation univ).toReal := by
  calc
    ‖setToFun μ.variation (cbmApplyMeasure μ (lsmul ℝ ℝ))
        (dominatedFinMeasAdditive_cbmApplyMeasure_lsmul_variation μ) g‖
        ≤ 1 * ‖hg.toL1 g‖ :=
      norm_setToFun_le (dominatedFinMeasAdditive_cbmApplyMeasure_lsmul_variation μ) hg
        zero_le_one
    _ = ‖hg.toL1 g‖ := one_mul _
    _ ≤ C * (μ.variation univ).toReal := by
      rw [Integrable.norm_toL1_eq_lintegral_enorm]
      have hlin :
          (∫⁻ x, ‖g x‖ₑ ∂μ.variation) ≤ ENNReal.ofReal C * μ.variation univ := by
        calc
          (∫⁻ x, ‖g x‖ₑ ∂μ.variation) ≤ ∫⁻ _x, ENNReal.ofReal C ∂μ.variation := by
            refine lintegral_mono fun x ↦ ?_
            rw [← ofReal_norm (g x)]
            exact ENNReal.ofReal_le_ofReal (hbound x)
          _ = ENNReal.ofReal C * μ.variation univ := lintegral_const _
      have htop : ENNReal.ofReal C * μ.variation univ ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ
      have hreal := ENNReal.toReal_mono htop hlin
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, measureReal_def] using hreal

namespace VectorMeasure

theorem norm_integral_smul_le_of_norm_le (μ : VectorMeasure X F) {g : X → ℝ} {C : ℝ}
    (hg : Integrable g μ.variation) (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C)
    (hμ : μ.variation univ ≠ ∞) :
    ‖∫ᵛ x, g x ∂•μ‖ ≤ C * (μ.variation univ).toReal := by
  by_cases hF : CompleteSpace F
  · letI := hF
    rw [← setToFun_lsmul_variation_eq_integral μ hg]
    exact norm_setToFun_lsmul_variation_le_of_norm_le μ hg hC hbound hμ
  · rw [integral]
    simp [hF, mul_nonneg hC ENNReal.toReal_nonneg]

theorem norm_integral_smul_boundedContinuousFunction_le {X F : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : VectorMeasure X F) [IsFiniteMeasure μ.variation] (g : X →ᵇ ℝ) :
    ‖∫ᵛ x, g x ∂•μ‖ ≤ ‖g‖ * (μ.variation univ).toReal :=
  norm_integral_smul_le_of_norm_le μ (BoundedContinuousFunction.integrable μ.variation g)
    (norm_nonneg g) (BoundedContinuousFunction.norm_coe_le_norm g)
    (measure_ne_top μ.variation univ)

end VectorMeasure

variable {X : Type*} [MeasurableSpace X]

theorem dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation
    (μ : VectorMeasure X ℂ) :
    DominatedFinMeasAdditive μ.variation
      (cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ)) 1 := by
  refine ⟨fun _s _t hs ht _ _ hdisj ↦
    cbmApplyMeasure_union μ (ContinuousLinearMap.mul ℝ ℂ) hs ht hdisj, fun s _hs hsf ↦ ?_⟩
  calc
    ‖cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ) s‖
        ≤ ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ * ‖μ s‖ :=
      norm_cbmApplyMeasure_le μ (ContinuousLinearMap.mul ℝ ℂ) s
    _ ≤ 1 * ‖μ s‖ := by
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) (norm_nonneg _)
    _ ≤ 1 * μ.variation.real s := by
      gcongr
      exact norm_measure_le_variation hsf.ne

theorem setToFun_mul_complex_variation_eq_integral (μ : VectorMeasure X ℂ)
    {g : X → ℂ} (hg : Integrable g μ.variation) :
    setToFun μ.variation (cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ))
        (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ) g =
      VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ) := by
  rw [VectorMeasure.integral]
  rw [dif_pos (inferInstance : CompleteSpace ℂ)]
  refine setToFun_congr_measure_of_integrable 1 ENNReal.one_ne_top ?_
    (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ)) g hg
  simp only [one_smul]
  refine variation_le_of_forall_enorm_le ?_
  intro s _hs
  have hnorm : ‖(μ.transpose (ContinuousLinearMap.mul ℝ ℂ)) s‖ ≤ ‖μ s‖ := by
    calc
      ‖(μ.transpose (ContinuousLinearMap.mul ℝ ℂ)) s‖ =
          ‖cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ) s‖ := rfl
      _ ≤ ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ * ‖μ s‖ :=
        norm_cbmApplyMeasure_le μ (ContinuousLinearMap.mul ℝ ℂ) s
      _ ≤ 1 * ‖μ s‖ := by
        exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) (norm_nonneg _)
      _ = ‖μ s‖ := one_mul _
  have henorm : ‖(μ.transpose (ContinuousLinearMap.mul ℝ ℂ)) s‖ₑ ≤ ‖μ s‖ₑ := by
    simpa [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  exact henorm.trans (enorm_measure_le_variation μ s)

theorem vectorMeasure_integral_mul_complex_indicator_const (μ : VectorMeasure X ℂ)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ.variation s ≠ ∞) (x : ℂ) :
    VectorMeasure.integral μ (s.indicator fun _ => x) (ContinuousLinearMap.mul ℝ ℂ) =
      x * μ s := by
  have hg : Integrable (s.indicator fun _ => x) μ.variation :=
    (integrableOn_const hμs).integrable_indicator hs
  rw [← setToFun_mul_complex_variation_eq_integral μ hg]
  rw [setToFun_indicator_const (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ)
    hs hμs]
  exact cbmApplyMeasure_apply μ (ContinuousLinearMap.mul ℝ ℂ) s x

theorem vectorMeasure_integral_mul_complex_const (μ : VectorMeasure X ℂ)
    [IsFiniteMeasure μ.variation] (x : ℂ) :
    VectorMeasure.integral μ (fun _ => x) (ContinuousLinearMap.mul ℝ ℂ) =
      x * μ Set.univ := by
  rw [← Set.indicator_univ (fun _ : X => x)]
  exact vectorMeasure_integral_mul_complex_indicator_const μ MeasurableSet.univ
    (measure_ne_top _ _) x

theorem complexMeasure_re_toComplexMeasure_add_im_toComplexMeasure_eq (μ : VectorMeasure X ℂ) :
    ((ComplexMeasure.re μ).toComplexMeasure 0) +
      ((0 : SignedMeasure X).toComplexMeasure (ComplexMeasure.im μ)) = μ := by
  ext s hs
  rw [VectorMeasure.add_apply, SignedMeasure.toComplexMeasure_apply,
    SignedMeasure.toComplexMeasure_apply, ComplexMeasure.re_apply, ComplexMeasure.im_apply,
    VectorMeasure.mapRange_apply, VectorMeasure.mapRange_apply]
  exact Complex.ext (by simp) (by simp)

theorem complexMeasure_re_toComplexMeasure_variation_le (μ : VectorMeasure X ℂ) :
    (((ComplexMeasure.re μ).toComplexMeasure 0).variation) ≤ μ.variation := by
  refine variation_le_of_forall_enorm_le ?_
  intro s hs
  rw [SignedMeasure.toComplexMeasure_apply, ComplexMeasure.re_apply, VectorMeasure.mapRange_apply]
  have hnorm : ‖({ re := (μ s).re, im := (0 : ℝ) } : ℂ)‖ ≤ ‖μ s‖ := by
    rw [show ({ re := (μ s).re, im := (0 : ℝ) } : ℂ) = ((μ s).re : ℂ) by rfl,
      Complex.norm_real]
    exact Complex.abs_re_le_norm (μ s)
  calc
    ‖({ re := (μ s).re, im := (0 : ℝ) } : ℂ)‖ₑ =
        ENNReal.ofReal ‖({ re := (μ s).re, im := (0 : ℝ) } : ℂ)‖ := by
      exact (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ‖μ s‖ := ENNReal.ofReal_le_ofReal hnorm
    _ = ‖μ s‖ₑ := by exact ofReal_norm _
    _ ≤ μ.variation s := enorm_measure_le_variation μ s

theorem complexMeasure_im_toComplexMeasure_variation_le (μ : VectorMeasure X ℂ) :
    (((0 : SignedMeasure X).toComplexMeasure (ComplexMeasure.im μ)).variation) ≤
      μ.variation := by
  refine variation_le_of_forall_enorm_le ?_
  intro s hs
  rw [SignedMeasure.toComplexMeasure_apply, ComplexMeasure.im_apply, VectorMeasure.mapRange_apply]
  have hnorm : ‖({ re := (0 : ℝ), im := (μ s).im } : ℂ)‖ ≤ ‖μ s‖ := by
    rw [show ({ re := (0 : ℝ), im := (μ s).im } : ℂ) =
        ((μ s).im : ℂ) * Complex.I by
      apply Complex.ext <;> simp]
    rw [Complex.norm_mul, Complex.norm_real]
    simpa using Complex.abs_im_le_norm (μ s)
  calc
    ‖({ re := (0 : ℝ), im := (μ s).im } : ℂ)‖ₑ =
        ENNReal.ofReal ‖({ re := (0 : ℝ), im := (μ s).im } : ℂ)‖ := by
      exact (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ‖μ s‖ := ENNReal.ofReal_le_ofReal hnorm
    _ = ‖μ s‖ₑ := by exact ofReal_norm _
    _ ≤ μ.variation s := enorm_measure_le_variation μ s

theorem vectorMeasure_integral_eq_re_add_I_im_of_integrable (μ : VectorMeasure X ℂ)
    {g : X → ℂ} (hg : Integrable g μ.variation) :
    VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ) =
      VectorMeasure.integral ((ComplexMeasure.re μ).toComplexMeasure 0) g
        (ContinuousLinearMap.mul ℝ ℂ) +
        VectorMeasure.integral
          ((0 : SignedMeasure X).toComplexMeasure (ComplexMeasure.im μ)) g
          (ContinuousLinearMap.mul ℝ ℂ) := by
  let μre : VectorMeasure X ℂ := (ComplexMeasure.re μ).toComplexMeasure 0
  let μim : VectorMeasure X ℂ := (0 : SignedMeasure X).toComplexMeasure (ComplexMeasure.im μ)
  have hsum : μre + μim = μ := by
    simpa [μre, μim] using complexMeasure_re_toComplexMeasure_add_im_toComplexMeasure_eq μ
  have hre_le : μre.variation ≤ μ.variation := by
    simpa [μre] using complexMeasure_re_toComplexMeasure_variation_le μ
  have him_le : μim.variation ≤ μ.variation := by
    simpa [μim] using complexMeasure_im_toComplexMeasure_variation_le μ
  have hgre : Integrable g μre.variation := hg.mono_measure hre_le
  have hgim : Integrable g μim.variation := hg.mono_measure him_le
  have hvar_sum : μ.variation ≤ μre.variation + μim.variation := by
    rw [← hsum]
    exact VectorMeasure.variation_add_le
  have hT_eq : ∀ s : Set X, MeasurableSet s →
      (μre.variation + μim.variation) s < (∞ : ℝ≥0∞) →
        cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ) s =
          (cbmApplyMeasure μre (ContinuousLinearMap.mul ℝ ℂ) +
            cbmApplyMeasure μim (ContinuousLinearMap.mul ℝ ℂ)) s := by
    intro s hs _hfin
    ext z
    have hmeasure : μ s = μre s + μim s := by
      rw [← hsum]
      rfl
    simp [cbmApplyMeasure_apply, hmeasure, mul_add]
  change VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ) =
    VectorMeasure.integral μre g (ContinuousLinearMap.mul ℝ ℂ) +
      VectorMeasure.integral μim g (ContinuousLinearMap.mul ℝ ℂ)
  rw [← setToFun_mul_complex_variation_eq_integral μ hg]
  rw [← setToFun_mul_complex_variation_eq_integral μre hgre]
  rw [← setToFun_mul_complex_variation_eq_integral μim hgim]
  exact setToFun_add_left''
    (hT := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μre)
    (hT' := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μim)
    (hT'' := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ)
    hT_eq hgre hgim hvar_sum zero_le_one zero_le_one zero_le_one

namespace Measure

noncomputable abbrev toComplexMeasureZero (μ : Measure X) [IsFiniteMeasure μ] :
    VectorMeasure X ℂ :=
  μ.toSignedMeasure.toComplexMeasure 0

theorem toComplexMeasureZero_apply (μ : Measure X) [IsFiniteMeasure μ] {s : Set X}
    (hs : MeasurableSet s) :
    μ.toComplexMeasureZero s = (μ.real s : ℂ) := by
  classical
  change { re := if MeasurableSet s then μ.real s else 0, im := (0 : ℝ) } =
    (μ.real s : ℂ)
  rw [if_pos hs]
  rfl

theorem toComplexMeasureZero_variation_le (μ : Measure X) [IsFiniteMeasure μ] :
    μ.toComplexMeasureZero.variation ≤ μ := by
  refine variation_le_of_forall_enorm_le ?_
  intro s hs
  have hnorm : ‖μ.toComplexMeasureZero s‖ ≤ μ.real s := by
    rw [toComplexMeasureZero_apply μ hs]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ μ.real s from measureReal_nonneg)]
  calc
    ‖μ.toComplexMeasureZero s‖ₑ = ENNReal.ofReal ‖μ.toComplexMeasureZero s‖ := by
      exact (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (μ.real s) := ENNReal.ofReal_le_ofReal hnorm
    _ = μ s := ENNReal.ofReal_toReal (measure_ne_top μ s)

end Measure

theorem dominatedFinMeasAdditive_cbmApplyMeasure_toComplexMeasureZero_mul_complex
    (μ : Measure X) [IsFiniteMeasure μ] :
    DominatedFinMeasAdditive μ
      (cbmApplyMeasure μ.toComplexMeasureZero (ContinuousLinearMap.mul ℝ ℂ) :
        Set X → ℂ →L[ℝ] ℂ) 1 := by
  refine ⟨fun _s _t hs ht _ _ hdisj =>
    cbmApplyMeasure_union _ _ hs ht hdisj, fun s hs _hsf => ?_⟩
  have hnormμ : ‖μ.toComplexMeasureZero s‖ ≤ μ.real s := by
    rw [Measure.toComplexMeasureZero_apply μ hs]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ μ.real s from measureReal_nonneg)]
  calc
    ‖cbmApplyMeasure μ.toComplexMeasureZero (ContinuousLinearMap.mul ℝ ℂ) s‖
        ≤ ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ *
            ‖μ.toComplexMeasureZero s‖ :=
      norm_cbmApplyMeasure_le μ.toComplexMeasureZero (ContinuousLinearMap.mul ℝ ℂ) s
    _ ≤ 1 * ‖μ.toComplexMeasureZero s‖ := by
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) (norm_nonneg _)
    _ ≤ 1 * μ.real s :=
      mul_le_mul_of_nonneg_left hnormμ zero_le_one

theorem vectorMeasure_integral_toComplexMeasureZero_mul_eq_integral
    (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℂ} (hg : Integrable g μ) :
    VectorMeasure.integral μ.toComplexMeasureZero g (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ x, g x ∂μ := by
  rw [← setToFun_mul_complex_variation_eq_integral μ.toComplexMeasureZero]
  · rw [integral_eq_setToFun]
    have hvar_le := Measure.toComplexMeasureZero_variation_le μ
    have hdomμ := dominatedFinMeasAdditive_cbmApplyMeasure_toComplexMeasureZero_mul_complex μ
    calc
      setToFun μ.toComplexMeasureZero.variation
          (cbmApplyMeasure μ.toComplexMeasureZero (ContinuousLinearMap.mul ℝ ℂ))
          (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation
            μ.toComplexMeasureZero) g
          = setToFun μ
              (cbmApplyMeasure μ.toComplexMeasureZero (ContinuousLinearMap.mul ℝ ℂ))
              hdomμ g := by
            exact (setToFun_congr_measure_of_integrable 1 ENNReal.one_ne_top
              (by simpa using hvar_le) hdomμ
              (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation
                μ.toComplexMeasureZero) g hg).symm
      _ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul μ) g := by
            exact setToFun_congr_left' hdomμ (dominatedFinMeasAdditive_weightedSMul μ)
              (fun s hs _hfin => by
                ext z
                rw [cbmApplyMeasure_apply, Measure.toComplexMeasureZero_apply μ hs,
                  weightedSMul_apply]
                simp [mul_comm]) g
  · exact hg.mono_measure (Measure.toComplexMeasureZero_variation_le μ)

theorem vectorMeasure_integral_restrict_toComplexMeasureZero_mul_eq_setIntegral
    (μ : Measure X) {s : Set X} [IsFiniteMeasure (μ.restrict s)]
    {g : X → ℂ} (hg : IntegrableOn g s μ) :
    VectorMeasure.integral (μ.restrict s).toComplexMeasureZero g
        (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ x in s, g x ∂μ := by
  simpa using
    vectorMeasure_integral_toComplexMeasureZero_mul_eq_integral (μ.restrict s) hg.integrable

theorem vectorMeasure_integral_restrict_toComplexMeasureZero_sub_mul_eq_setIntegral_sub
    (μ ν : Measure X) {s : Set X}
    [IsFiniteMeasure (μ.restrict s)] [IsFiniteMeasure (ν.restrict s)]
    {g : X → ℂ} (hμg : IntegrableOn g s μ) (hνg : IntegrableOn g s ν) :
    VectorMeasure.integral
        ((μ.restrict s).toComplexMeasureZero - (ν.restrict s).toComplexMeasureZero)
        g (ContinuousLinearMap.mul ℝ ℂ) =
      (∫ x in s, g x ∂μ) - ∫ x in s, g x ∂ν := by
  let μc : VectorMeasure X ℂ := (μ.restrict s).toComplexMeasureZero
  let νc : VectorMeasure X ℂ := (ν.restrict s).toComplexMeasureZero
  let ξ : VectorMeasure X ℂ := μc - νc
  have hμc_var_le : μc.variation ≤ μ.restrict s := by
    simpa [μc] using Measure.toComplexMeasureZero_variation_le (μ.restrict s)
  have hνc_var_le : νc.variation ≤ ν.restrict s := by
    simpa [νc] using Measure.toComplexMeasureZero_variation_le (ν.restrict s)
  have hμc_g : Integrable g μc.variation := hμg.integrable.mono_measure hμc_var_le
  have hνc_g : Integrable g νc.variation := hνg.integrable.mono_measure hνc_var_le
  have hsum_g : Integrable g (μc.variation + νc.variation) := hμc_g.add_measure hνc_g
  have hξ_var_le : ξ.variation ≤ μc.variation + νc.variation := by
    simpa [ξ] using VectorMeasure.variation_sub_le (μ := μc) (ν := νc)
  have hξ_g : Integrable g ξ.variation := hsum_g.mono_measure hξ_var_le
  have hdomξ := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation ξ
  have hdomξ_sum : DominatedFinMeasAdditive (μc.variation + νc.variation)
      (cbmApplyMeasure ξ (ContinuousLinearMap.mul ℝ ℂ)) 1 :=
    DominatedFinMeasAdditive.of_measure_le hξ_var_le hdomξ zero_le_one
  have hdomμ := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μc
  have hdomν := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation νc
  have hdom_sub :=
    DominatedFinMeasAdditive.sub_measure μc.variation νc.variation hdomμ hdomν
  have hT_eq : ∀ t : Set X, MeasurableSet t →
      (μc.variation + νc.variation) t < (∞ : ℝ≥0∞) →
        cbmApplyMeasure ξ (ContinuousLinearMap.mul ℝ ℂ) t =
          (cbmApplyMeasure μc (ContinuousLinearMap.mul ℝ ℂ) -
            cbmApplyMeasure νc (ContinuousLinearMap.mul ℝ ℂ)) t := by
    intro t ht _hfin
    ext z
    simp [ξ, cbmApplyMeasure_apply, sub_eq_add_neg, mul_add]
  change VectorMeasure.integral ξ g (ContinuousLinearMap.mul ℝ ℂ) =
    (∫ x in s, g x ∂μ) - ∫ x in s, g x ∂ν
  rw [← setToFun_mul_complex_variation_eq_integral ξ hξ_g]
  rw [← vectorMeasure_integral_restrict_toComplexMeasureZero_mul_eq_setIntegral μ hμg]
  rw [← vectorMeasure_integral_restrict_toComplexMeasureZero_mul_eq_setIntegral ν hνg]
  change setToFun ξ.variation (cbmApplyMeasure ξ (ContinuousLinearMap.mul ℝ ℂ)) hdomξ g =
    VectorMeasure.integral μc g (ContinuousLinearMap.mul ℝ ℂ) -
      VectorMeasure.integral νc g (ContinuousLinearMap.mul ℝ ℂ)
  rw [← setToFun_mul_complex_variation_eq_integral μc hμc_g]
  rw [← setToFun_mul_complex_variation_eq_integral νc hνc_g]
  calc
    setToFun ξ.variation (cbmApplyMeasure ξ (ContinuousLinearMap.mul ℝ ℂ)) hdomξ g =
        setToFun (μc.variation + νc.variation)
          (cbmApplyMeasure ξ (ContinuousLinearMap.mul ℝ ℂ)) hdomξ_sum g := by
          exact (setToFun_congr_measure_of_integrable 1 ENNReal.one_ne_top
            (by simpa [one_smul] using hξ_var_le) hdomξ_sum hdomξ g hsum_g).symm
    _ = setToFun (μc.variation + νc.variation)
          (cbmApplyMeasure μc (ContinuousLinearMap.mul ℝ ℂ) -
            cbmApplyMeasure νc (ContinuousLinearMap.mul ℝ ℂ)) hdom_sub g := by
          exact setToFun_congr_left' hdomξ_sum hdom_sub hT_eq g
    _ = setToFun μc.variation (cbmApplyMeasure μc (ContinuousLinearMap.mul ℝ ℂ)) hdomμ g -
          setToFun νc.variation (cbmApplyMeasure νc (ContinuousLinearMap.mul ℝ ℂ)) hdomν g := by
          exact setToFun_sub_measure hdomμ hdomν hμc_g hνc_g

theorem vectorMeasure_restrict_variation_le (μ : VectorMeasure X ℂ) {s : Set X}
    (hs : MeasurableSet s) : (μ.restrict s).variation ≤ μ.variation := by
  refine variation_le_of_forall_enorm_le fun E hE => ?_
  rw [VectorMeasure.restrict_apply μ hs hE]
  exact (enorm_measure_le_variation μ (E ∩ s)).trans (measure_mono Set.inter_subset_left)

/-- The indicator restriction `f ↦ s.indicator f` as a `1`-Lipschitz self-map of `L¹(m)`. -/
noncomputable def indicatorL1 (m : Measure X) (s : Set X) (hs : MeasurableSet s) :
    (X →₁[m] ℂ) → (X →₁[m] ℂ) :=
  fun f => ((L1.integrable_coeFn f).indicator hs).toL1 (s.indicator ⇑f)

theorem coeFn_indicatorL1 {m : Measure X} {s : Set X} (hs : MeasurableSet s) (f : X →₁[m] ℂ) :
    ⇑(indicatorL1 m s hs f) =ᵐ[m] s.indicator ⇑f := by
  rw [indicatorL1]
  exact Integrable.coeFn_toL1 ((L1.integrable_coeFn f).indicator hs)

theorem lipschitzWith_indicatorL1 {m : Measure X} {s : Set X} (hs : MeasurableSet s) :
    LipschitzWith 1 (indicatorL1 m s hs) := by
  intro f g
  rw [ENNReal.coe_one, one_mul, Lp.edist_eq_eLpNorm_neg_add, Lp.edist_eq_eLpNorm_neg_add]
  refine eLpNorm_mono_ae ?_
  filter_upwards [coeFn_indicatorL1 hs f, coeFn_indicatorL1 hs g] with x hxf hxg
  simp only [Pi.add_apply, Pi.neg_apply, hxf, hxg]
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs]
  · simp [Set.indicator_of_notMem hxs]

/-- The map `f ↦ setToFun m T hT (s.indicator f)` is continuous on `L¹(m)`. The indicator
restriction `f ↦ s.indicator f` is a `1`-Lipschitz self-map of `L¹(m)`, after which
`continuous_setToFun` applies. -/
theorem continuous_setToFun_indicator {m : Measure X} {T : Set X → ℂ →L[ℝ] ℂ} {C : ℝ}
    (hT : DominatedFinMeasAdditive m T C) {s : Set X} (hs : MeasurableSet s) :
    Continuous fun f : X →₁[m] ℂ => setToFun m T hT (s.indicator ⇑f) := by
  have heq : (fun f : X →₁[m] ℂ => setToFun m T hT (s.indicator ⇑f)) =
      (fun f : X →₁[m] ℂ => setToFun m T hT ⇑f) ∘ (indicatorL1 m s hs) := by
    funext f
    exact (setToFun_congr_ae hT (coeFn_indicatorL1 hs f)).symm
  rw [heq]
  exact (continuous_setToFun hT).comp (lipschitzWith_indicatorL1 hs).continuous

theorem vectorMeasure_integral_mul_complex_add (μ : VectorMeasure X ℂ) {f g : X → ℂ}
    (hf : Integrable f μ.variation) (hg : Integrable g μ.variation) :
    VectorMeasure.integral μ (f + g) (ContinuousLinearMap.mul ℝ ℂ) =
      VectorMeasure.integral μ f (ContinuousLinearMap.mul ℝ ℂ) +
        VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ) := by
  rw [← setToFun_mul_complex_variation_eq_integral μ hf,
    ← setToFun_mul_complex_variation_eq_integral μ hg,
    ← setToFun_mul_complex_variation_eq_integral μ (hf.add hg)]
  exact setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ) hf hg

theorem vectorMeasure_integral_indicator_eq_restrict (μ : VectorMeasure X ℂ)
    [IsFiniteMeasure μ.variation] {s : Set X} (hs : MeasurableSet s) {g : X → ℂ}
    (hg : Integrable g μ.variation) :
    VectorMeasure.integral μ (s.indicator g) (ContinuousLinearMap.mul ℝ ℂ) =
      VectorMeasure.integral (μ.restrict s) g (ContinuousLinearMap.mul ℝ ℂ) := by
  have hvar_le : (μ.restrict s).variation ≤ μ.variation := vectorMeasure_restrict_variation_le μ hs
  have hfin : IsFiniteMeasure (μ.restrict s).variation :=
    ⟨lt_of_le_of_lt (hvar_le Set.univ) (measure_lt_top μ.variation Set.univ)⟩
  -- Reduce to a statement provable by induction over `g` against `μ.variation`.
  set B := ContinuousLinearMap.mul ℝ ℂ with hB
  -- The predicate to induct on.
  set P : (X → ℂ) → Prop := fun g =>
    VectorMeasure.integral μ (s.indicator g) B = VectorMeasure.integral (μ.restrict s) g B with hP
  suffices hsuff : ∀ ⦃g : X → ℂ⦄, Integrable g μ.variation → P g from hsuff hg
  intro g hg
  refine Integrable.induction P ?_ ?_ ?_ ?_ hg
  · -- base case: `g = t.indicator (fun _ => c)`
    intro c t ht htfin
    have htfin' : μ.variation t ≠ ∞ := htfin.ne
    have hsint : μ.variation (s ∩ t) ≠ ∞ :=
      ne_top_of_le_ne_top htfin' (measure_mono Set.inter_subset_right)
    have hrtfin : (μ.restrict s).variation t ≠ ∞ := (measure_lt_top _ _).ne
    change VectorMeasure.integral μ (s.indicator (t.indicator fun _ => c)) B =
      VectorMeasure.integral (μ.restrict s) (t.indicator fun _ => c) B
    rw [Set.indicator_indicator, hB,
      vectorMeasure_integral_mul_complex_indicator_const μ (hs.inter ht) hsint c,
      vectorMeasure_integral_mul_complex_indicator_const (μ.restrict s) ht hrtfin c,
      VectorMeasure.restrict_apply μ hs ht, Set.inter_comm s t]
  · -- additivity
    intro f₁ f₂ _ hf₁ hf₂ hPf₁ hPf₂
    have hf₁r : Integrable f₁ (μ.restrict s).variation := hf₁.mono_measure hvar_le
    have hf₂r : Integrable f₂ (μ.restrict s).variation := hf₂.mono_measure hvar_le
    change VectorMeasure.integral μ (s.indicator (f₁ + f₂)) B =
      VectorMeasure.integral (μ.restrict s) (f₁ + f₂) B
    rw [Set.indicator_add', hB,
      vectorMeasure_integral_mul_complex_add μ (hf₁.indicator hs) (hf₂.indicator hs),
      vectorMeasure_integral_mul_complex_add (μ.restrict s) hf₁r hf₂r]
    exact congr_arg₂ (· + ·) hPf₁ hPf₂
  · -- closedness
    have hdomμ := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ
    have hLHS : Continuous fun f : X →₁[μ.variation] ℂ =>
        VectorMeasure.integral μ (s.indicator ⇑f) B := by
      have := continuous_setToFun_indicator hdomμ hs
      refine this.congr fun f => ?_
      exact setToFun_mul_complex_variation_eq_integral μ ((L1.integrable_coeFn f).indicator hs)
    have hdomρ := dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation (μ.restrict s)
    have hdomρ_up : DominatedFinMeasAdditive μ.variation
        (cbmApplyMeasure (μ.restrict s) B) 1 :=
      DominatedFinMeasAdditive.of_measure_le hvar_le hdomρ zero_le_one
    have hRHS : Continuous fun f : X →₁[μ.variation] ℂ =>
        VectorMeasure.integral (μ.restrict s) (⇑f) B := by
      have hcont : Continuous fun f : X →₁[μ.variation] ℂ =>
          setToFun μ.variation (cbmApplyMeasure (μ.restrict s) B) hdomρ_up ⇑f :=
        continuous_setToFun hdomρ_up
      refine hcont.congr fun f => ?_
      have hfr : Integrable (⇑f) (μ.restrict s).variation :=
        (L1.integrable_coeFn f).mono_measure hvar_le
      rw [← setToFun_mul_complex_variation_eq_integral (μ.restrict s) hfr]
      exact setToFun_congr_measure_of_integrable 1 ENNReal.one_ne_top
        (by simpa [one_smul] using hvar_le) hdomρ_up hdomρ _ (L1.integrable_coeFn f)
    exact isClosed_eq hLHS hRHS
  · -- a.e. congruence
    intro f₁ f₂ hf₁₂ hf₁ hPf₁
    have hf₂ : Integrable f₂ μ.variation := hf₁.congr hf₁₂
    have hf₁r : Integrable f₁ (μ.restrict s).variation := hf₁.mono_measure hvar_le
    have hf₂r : Integrable f₂ (μ.restrict s).variation := hf₂.mono_measure hvar_le
    have hf₁₂r : f₁ =ᵐ[(μ.restrict s).variation] f₂ :=
      (Measure.absolutelyContinuous_of_le hvar_le) hf₁₂
    have hind₁₂ : s.indicator f₁ =ᵐ[μ.variation] s.indicator f₂ := by
      filter_upwards [hf₁₂] with x hx
      by_cases hxs : x ∈ s
      · simp [Set.indicator_of_mem hxs, hx]
      · simp [Set.indicator_of_notMem hxs]
    change VectorMeasure.integral μ (s.indicator f₂) B =
      VectorMeasure.integral (μ.restrict s) f₂ B
    rw [← setToFun_mul_complex_variation_eq_integral μ (hf₂.indicator hs),
      ← setToFun_mul_complex_variation_eq_integral (μ.restrict s) hf₂r,
      setToFun_congr_ae _ hind₁₂.symm,
      setToFun_congr_ae _ hf₁₂r.symm,
      setToFun_mul_complex_variation_eq_integral μ (hf₁.indicator hs),
      setToFun_mul_complex_variation_eq_integral (μ.restrict s) hf₁r]
    exact hPf₁

theorem norm_setToFun_mul_complex_variation_le_of_norm_le (μ : VectorMeasure X ℂ)
    {g : X → ℂ} {C : ℝ} (hg : Integrable g μ.variation) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) (hμ : μ.variation univ ≠ ∞) :
    ‖setToFun μ.variation (cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ))
        (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ) g‖ ≤
      C * (μ.variation univ).toReal := by
  calc
    ‖setToFun μ.variation (cbmApplyMeasure μ (ContinuousLinearMap.mul ℝ ℂ))
        (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ) g‖
        ≤ 1 * ‖hg.toL1 g‖ :=
      norm_setToFun_le (dominatedFinMeasAdditive_cbmApplyMeasure_mul_complex_variation μ) hg
        zero_le_one
    _ = ‖hg.toL1 g‖ := one_mul _
    _ ≤ C * (μ.variation univ).toReal := by
      rw [Integrable.norm_toL1_eq_lintegral_enorm]
      have hlin :
          (∫⁻ x, ‖g x‖ₑ ∂μ.variation) ≤ ENNReal.ofReal C * μ.variation univ := by
        calc
          (∫⁻ x, ‖g x‖ₑ ∂μ.variation) ≤ ∫⁻ _x, ENNReal.ofReal C ∂μ.variation := by
            refine lintegral_mono fun x ↦ ?_
            rw [← ofReal_norm (g x)]
            exact ENNReal.ofReal_le_ofReal (hbound x)
          _ = ENNReal.ofReal C * μ.variation univ := lintegral_const _
      have htop : ENNReal.ofReal C * μ.variation univ ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ
      have hreal := ENNReal.toReal_mono htop hlin
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, measureReal_def] using hreal

namespace VectorMeasure

theorem norm_integral_mul_complex_le_of_norm_le (μ : VectorMeasure X ℂ) {g : X → ℂ} {C : ℝ}
    (hg : Integrable g μ.variation) (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C)
    (hμ : μ.variation univ ≠ ∞) :
    ‖VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ)‖ ≤
      C * (μ.variation univ).toReal := by
  rw [← setToFun_mul_complex_variation_eq_integral μ hg]
  exact norm_setToFun_mul_complex_variation_le_of_norm_le μ hg hC hbound hμ

theorem norm_integral_mul_complex_boundedContinuousFunction_le {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] (μ : VectorMeasure X ℂ)
    [IsFiniteMeasure μ.variation] (g : X →ᵇ ℂ) :
    ‖VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ)‖ ≤
      ‖g‖ * (μ.variation univ).toReal :=
  norm_integral_mul_complex_le_of_norm_le μ
    (BoundedContinuousFunction.integrable μ.variation g) (norm_nonneg g)
    (BoundedContinuousFunction.norm_coe_le_norm g) (measure_ne_top μ.variation univ)

end VectorMeasure

end MeasureTheory
