import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
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

end MeasureTheory
