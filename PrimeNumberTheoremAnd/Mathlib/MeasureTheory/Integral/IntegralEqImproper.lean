import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Filter Set TopologicalSpace

open scoped ENNReal NNReal Topology

section IntegrationByParts

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {a b : ℝ} {a' b' : A} {u : ℝ → A} {v : ℝ → A} {u' : ℝ → A} {v' : ℝ → A}

theorem integral_mul_deriv_eq_deriv_mul
    (hu : ∀ x, HasDerivAt u (u' x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ), u x * v' x = b' - a' - ∫ (x : ℝ), u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  simpa only [add_comm] using integral_deriv_mul_eq_sub hu hv (hu'v.add huv') h_bot h_top

theorem integral_Iic_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ Iio a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Iio a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Iic a)) (hu'v : IntegrableOn (u' * v) (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : ℝ) in Iic a, u x * v' x = a' - b' - ∫ (x : ℝ) in Iic a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Iic_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

end IntegrationByParts
