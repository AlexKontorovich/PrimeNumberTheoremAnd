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
