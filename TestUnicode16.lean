import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform RealInnerProductSpace
open Real MeasureTheory FourierTransform

example (ψ : ℝ → ℂ) (h : ℝ) :
    𝓕 (ψ ∘ fun t : ℝ => t + h) = fun u : ℝ => (𝐞 (h * u) : Circle) • 𝓕 ψ u := by
  ext u
  -- apply VectorFourier translation lemma for the inner-product Fourier transform
  have htrans := VectorFourier.fourierIntegral_comp_add_right (V := ℝ) (W := ℝ) (E := ℂ)
    (e := (𝐞 : AddChar ℝ Circle)) (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) ψ h
  -- evaluate at u
  have htrans_u := congrArg (fun F => F u) htrans
  -- rewrite `𝓕` as `VectorFourier.fourierIntegral`
  -- and simplify `((innerₗ ℝ) h) u`
  simpa [Real.fourier_eq, mul_comm] using htrans_u
