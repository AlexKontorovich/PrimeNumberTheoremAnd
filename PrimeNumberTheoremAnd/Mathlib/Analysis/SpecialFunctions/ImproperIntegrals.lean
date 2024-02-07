import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open Real Filter MeasureTheory

open scoped Topology

private theorem intervalIntegral_one_div_one_add_sq_tendsto :
    Tendsto (fun i => ∫ (x : ℝ) in -i..i, 1 / (1 + x ^ 2)) atTop (𝓝 π) := by
  have := tendsto_nhds_of_tendsto_nhdsWithin arctan_atTop
  convert Tendsto.add this this <;> simp

theorem integrable_one_div_one_add_sq : Integrable fun (x : ℝ) ↦ 1 / (1 + x ^ 2) := by
  have (x : ℝ) : ‖1 / (1 + x ^ 2)‖ = 1 / (1 + x ^ 2) := norm_of_nonneg (by positivity)
  refine integrable_of_intervalIntegral_norm_tendsto π (fun i ↦ ?_) tendsto_neg_atTop_atBot
    tendsto_id (by simpa only [this] using intervalIntegral_one_div_one_add_sq_tendsto)
  by_cases hi : i = 0
  · rewrite [hi, Set.Ioc_eq_empty (by norm_num)]; exact integrableOn_empty
  · refine (intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_).1
    simp [← two_mul, arctan_ne_zero hi]

theorem integral_Iic_one_div_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Iic i, 1 / (1 + x ^ 2) = arctan i + (π / 2) :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan x)
    integrable_one_div_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin arctan_atBot)
    |>.trans (sub_neg_eq_add _ _)

theorem integral_Ioi_one_div_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Ioi i, 1 / (1 + x ^ 2) = (π / 2) - arctan i :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan x)
    integrable_one_div_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin arctan_atTop)

theorem integral_volume_one_div_one_add_sq : ∫ (x : ℝ), 1 / (1 + x ^ 2) = π :=
  tendsto_nhds_unique (intervalIntegral_tendsto_integral integrable_one_div_one_add_sq
    tendsto_neg_atTop_atBot tendsto_id) intervalIntegral_one_div_one_add_sq_tendsto
