import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform
open Real MeasureTheory FourierTransform

example (ψ : ℝ → ℂ) (h : ℝ) :
    𝓕 (ψ ∘ fun t : ℝ => t + h) = fun u : ℝ => (𝐞 (h * u) : Circle) • 𝓕 ψ u := by
  -- try using VectorFourier lemma
  -- unfold 𝓕? maybe Real.fourier_eq
  ext u
  -- 𝓕 is defined as VectorFourier.fourierIntegral fourierChar volume (innerₗ ℝ)
  -- use Real.fourier_eq and VectorFourier.fourierIntegral_comp_add_right
  -- but need measurable add etc
  simpa [Real.fourier_eq, inner_mul_right] using
    (VectorFourier.fourierIntegral_comp_add_right (V := ℝ) (W := ℝ) (E := ℂ)
      (e := (𝐞 : AddChar ℝ Circle)) (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) ψ h u)
