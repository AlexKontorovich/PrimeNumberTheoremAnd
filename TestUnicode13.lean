import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform RealInnerProductSpace
open Real MeasureTheory FourierTransform

example (ψ : ℝ → ℂ) (h : ℝ) :
    𝓕 (ψ ∘ fun t : ℝ => t + h) = fun u : ℝ => (𝐞 (h * u) : Circle) • 𝓕 ψ u := by
  -- Use VectorFourier translation lemma for inner-product Fourier transform
  ext u
  -- `𝓕` is definitionally `VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)`
  -- so the translation lemma applies directly.
  simpa [Real.fourier_eq, inner_mul_right, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun F => F u)
      (VectorFourier.fourierIntegral_comp_add_right (V := ℝ) (W := ℝ) (E := ℂ)
        (e := (𝐞 : AddChar ℝ Circle)) (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) ψ h)
