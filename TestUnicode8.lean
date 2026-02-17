import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform
open Real MeasureTheory FourierTransform

example (ψ : ℝ → ℂ) (hψ : Integrable ψ) (h : ℝ) (u : ℝ) :
    𝓕 (fun t => ψ (t + h)) u = (𝐞 (h * u) : Circle) • 𝓕 ψ u := by
  -- try using Fourier.fourierIntegral_comp_add_right
  -- 𝓕 is Real.fourierIntegral with inner product; for ℝ it is multiplication.
  simp [Real.fourier_real_eq]
