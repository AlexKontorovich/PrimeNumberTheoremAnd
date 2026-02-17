import PrimeNumberTheoremAnd.Wiener
import PrimeNumberTheoremAnd.BVFourier

open scoped FourierTransform RealInnerProductSpace
open Real MeasureTheory FourierTransform

example (ψ : ℝ → ℂ) (hψ : Integrable ψ) (h : ℝ) (u : ℝ) :
    𝓕 (fun t => ψ t - ψ (t + h)) u = (1 - (𝐞 (h * u) : ℂ)) * 𝓕 ψ u := by
  -- compute Fourier of translate
  have htrans : 𝓕 (ψ ∘ fun t : ℝ => t + h) u = (𝐞 (h * u) : Circle) • 𝓕 ψ u := by
    -- from VectorFourier lemma
    have htrans' := VectorFourier.fourierIntegral_comp_add_right (V := ℝ) (W := ℝ) (E := ℂ)
      (e := (𝐞 : AddChar ℝ Circle)) (μ := (volume : Measure ℝ)) (L := innerₗ ℝ) ψ h
    have := congrArg (fun F => F u) htrans'
    simpa [Real.fourier_eq, mul_comm] using this
  -- use linearity
  have hψ_int : Integrable (fun t : ℝ => ψ (t + h)) := by
    simpa [Function.comp] using hψ.comp_add_right h
  -- apply F_sub lemma from PrimeNumberTheoremAnd.Fourier? maybe
  -- but in this file we can just unfold real.fourier_real_eq and use integral_sub
  -- Let's use lemma `F_sub` from PrimeNumberTheoremAnd.Fourier.
  simpa [sub_eq_add_neg, mul_add, mul_assoc] using ?_
