import PrimeNumberTheoremAnd.LaplaceInversion

/-!
# Window error bounds for the sin-div sinc kernel

For a complex-valued function `g` with a uniform derivative bound `D`, the windowed
error term

`(if u = 0 then 0 else sin (T * u) / (π * u)) • (g (x - u) - g x)`

is controlled pointwise by `D / π`, uniformly in the height `T`, and consequently its
integral over `[-1, 1]` is bounded by `(D / π) · vol (Ioc (-1) 1)`.  These supply the
local-window hypothesis of `norm_fourierInvTrunc_le_of_windowed_sin_div_bounds`.
-/

open MeasureTheory Set

/-- Pointwise bound on the sin-div windowed error term: scaling by the normalized sinc
kernel and a mean-value estimate on `g (x - u) - g x` gives a bound `D / π` that is
independent of the height `T`. -/
theorem sin_div_error_pointwise_bound
    {g : ℝ → ℂ} {D x T u : ℝ}
    (hD : 0 ≤ D) (hgdiff : Differentiable ℝ g)
    (hderiv : ∀ y : ℝ, ‖deriv g y‖ ≤ D) :
    ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
        (g (x - u) - g x)‖ ≤ D / Real.pi := by
  by_cases hu : u = 0
  · simp [hu, div_nonneg hD Real.pi_pos.le]
  · rw [if_neg hu, norm_smul]
    have hscalar :
        ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 1 / (Real.pi * |u|) := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      have hsin : |Real.sin (T * u)| ≤ 1 := Real.abs_sin_le_one _
      exact div_le_div_of_nonneg_right hsin
        (mul_nonneg Real.pi_pos.le (abs_nonneg u))
    have hdiff : ‖g (x - u) - g x‖ ≤ D * |u| := by
      have hmv :=
        (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
          (f := g) (C := D)
          (fun y _hy => hgdiff y)
          (fun y _hy => hderiv y)
          (x := x) (y := x - u) (by simp) (by simp)
      have hnorm : ‖(x - u) - x‖ = |u| := by
        rw [Real.norm_eq_abs]
        have hsub : (x - u) - x = -u := by ring
        rw [hsub, abs_neg]
      simpa [hnorm] using hmv
    have hupper_nonneg : 0 ≤ 1 / (Real.pi * |u|) := by positivity
    calc
      ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ * ‖g (x - u) - g x‖
          ≤ (1 / (Real.pi * |u|)) * (D * |u|) := by
            exact mul_le_mul hscalar hdiff (norm_nonneg _) hupper_nonneg
      _ = D / Real.pi := by
            field_simp [Real.pi_ne_zero, abs_pos.mpr hu]

/-- Interval form of `sin_div_error_pointwise_bound`: integrating the pointwise bound over
`[-1, 1]` controls the windowed error integral by `(D / π) · vol (Ioc (-1) 1)`. -/
theorem sin_div_error_interval_bound
    {g : ℝ → ℂ} {D x T : ℝ}
    (hD : 0 ≤ D) (hgdiff : Differentiable ℝ g)
    (hderiv : ∀ y : ℝ, ‖deriv g y‖ ≤ D) :
    ‖∫ u in (-(1 : ℝ))..(1 : ℝ),
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (g (x - u) - g x)‖ ≤
      (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ)) ≤ 1)]
  refine norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Ioc (-(1 : ℝ)) (1 : ℝ)) ?_ ?_
  · simp [Real.volume_Ioc]
  · intro u _hu
    exact sin_div_error_pointwise_bound (g := g) (D := D) (x := x) (T := T) (u := u)
      hD hgdiff hderiv
