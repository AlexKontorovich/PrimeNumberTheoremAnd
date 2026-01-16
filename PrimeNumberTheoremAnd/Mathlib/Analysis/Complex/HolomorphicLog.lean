import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.TaxicabPrimitive

/-!
# Holomorphic Logarithms on Convex Domains

This file proves that every nonvanishing holomorphic function on a convex open subset
of ℂ has a holomorphic logarithm. This is a key ingredient for proving that the
Gamma function takes values in the slit plane.

## Main Results

* `DifferentiableOn.exists_log_of_convex`: On a convex open set, a nonvanishing
  holomorphic function has a holomorphic logarithm.

## References

* [Ahlfors, Complex Analysis] Chapter 4
* [Rudin, Real and Complex Analysis] Chapter 10

-/

open Complex Set Filter Topology MeasureTheory
open scoped Topology Interval

noncomputable section

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ## Part 1: Primitives on Convex Open Sets

On a convex open set, a holomorphic function has primitives.
We import this from TaxicabPrimitive.lean. -/

-- Re-export the key result
theorem DifferentiableOn.isExactOn_rectangularConvex' {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) (hU_rect : RectangularConvex U) (hU_ne : U.Nonempty)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) : IsExactOn f U :=
  hf.isExactOn_rectangularConvex hU_open hU_convex hU_rect hU_ne

/-! ## Part 2: Logarithmic Derivative -/

/-- The logarithmic derivative f'/f of a function. -/
def logDeriv (f : ℂ → ℂ) : ℂ → ℂ := fun z => deriv f z / f z

/-- The logarithmic derivative is holomorphic when f is holomorphic and nonvanishing. -/
theorem differentiableOn_logDeriv {U : Set ℂ} (hU_open : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf_ne : ∀ z ∈ U, f z ≠ 0) :
    DifferentiableOn ℂ (logDeriv f) U := by
  intro z hz
  have hf_at : DifferentiableAt ℂ f z := hf.differentiableAt (hU_open.mem_nhds hz)
  have hf_ne_z : f z ≠ 0 := hf_ne z hz
  unfold logDeriv
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · have : DifferentiableOn ℂ (deriv f) U := hf.deriv hU_open
    exact this.differentiableAt (hU_open.mem_nhds hz)
  · exact hf_at
  · exact hf_ne_z

/-! ## Part 3: Zero Derivative Implies Constant on Convex Sets -/

-- Re-export from TaxicabPrimitive
theorem eq_of_deriv_eq_zero_on_convex' {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, deriv f z = 0) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    f x = f y :=
  eq_of_deriv_eq_zero_on_convex hU_open hU_convex hf hf' hx hy

/-! ## Part 4: Holomorphic Logarithm -/

/-- On a convex open set that is also rectangularly convex, a nonvanishing holomorphic function has a holomorphic logarithm. -/
theorem DifferentiableOn.exists_log_of_rectangularConvex {U : Set ℂ} (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U) (hU_rect : RectangularConvex U) (hU_ne : U.Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf_ne : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, exp (g z) = f z := by
  -- Step 1: The logarithmic derivative f'/f is holomorphic
  have hlogDeriv : DifferentiableOn ℂ (logDeriv f) U :=
    differentiableOn_logDeriv hU_open hf hf_ne
  -- Step 2: Find a primitive g₀ of the logarithmic derivative
  obtain ⟨g₀, hg₀⟩ := hlogDeriv.isExactOn_rectangularConvex hU_open hU_convex hU_rect hU_ne
  -- Step 3: Show that f(z) * exp(-g₀(z)) is constant
  obtain ⟨z₀, hz₀⟩ := hU_ne
  let h := fun z => f z * exp (-g₀ z)
  have hh_diff : DifferentiableOn ℂ h U := by
    apply DifferentiableOn.mul hf
    apply DifferentiableOn.cexp
    apply DifferentiableOn.neg
    intro z hz; exact (hg₀ z hz).differentiableAt.differentiableWithinAt
  have hh_deriv_zero : ∀ z ∈ U, deriv h z = 0 := by
    intro z hz
    have hf_at := hf.differentiableAt (hU_open.mem_nhds hz)
    have hg₀_at : HasDerivAt g₀ (logDeriv f z) z := hg₀ z hz
    have hexp_at : DifferentiableAt ℂ (fun w => exp (-g₀ w)) z := by
      apply DifferentiableAt.cexp; apply DifferentiableAt.neg; exact hg₀_at.differentiableAt
    have hh_eq : h = f * (fun w => exp (-g₀ w)) := rfl
    rw [hh_eq, deriv_mul hf_at hexp_at]
    have hexp_deriv : deriv (fun w => exp (-g₀ w)) z = -logDeriv f z * exp (-g₀ z) := by
      have h1 : deriv (fun w => exp (-g₀ w)) z = exp (-g₀ z) * deriv (fun w => -g₀ w) z := by
        apply deriv_cexp; exact hg₀_at.differentiableAt.neg
      have h2 : deriv (fun w => -g₀ w) z = -deriv g₀ z := by
        rw [show (fun w => -g₀ w) = -g₀ from rfl, deriv.neg]
      rw [h1, h2, hg₀_at.deriv]; ring
    rw [hexp_deriv]; unfold logDeriv
    have hf_ne_z : f z ≠ 0 := hf_ne z hz
    field_simp; ring
  -- Step 4: h is constant on U
  have h_const : ∀ z ∈ U, h z = h z₀ := fun z hz =>
    eq_of_deriv_eq_zero_on_convex hU_open hU_convex hh_diff hh_deriv_zero hz hz₀
  -- Step 5: Extract the constant and build the logarithm
  let c := h z₀
  have hc_ne : c ≠ 0 := mul_ne_zero (hf_ne z₀ hz₀) (exp_ne_zero _)
  let L₀ := log c
  have hexp_L₀ : exp L₀ = c := exp_log hc_ne
  -- Step 6: The logarithm is g(z) = g₀(z) + L₀
  use fun z => g₀ z + L₀
  refine ⟨?_, ?_⟩
  · apply DifferentiableOn.add
    · intro z hz; exact (hg₀ z hz).differentiableAt.differentiableWithinAt
    · exact differentiableOn_const L₀
  · intro z hz
    have heq : h z = c := h_const z hz
    calc exp (g₀ z + L₀) = exp (g₀ z) * exp L₀ := exp_add (g₀ z) L₀
      _ = exp (g₀ z) * c := by rw [hexp_L₀]
      _ = exp (g₀ z) * (f z * exp (-g₀ z)) := by rw [← heq]
      _ = f z * (exp (g₀ z) * exp (-g₀ z)) := by ring
      _ = f z * exp (g₀ z + (-g₀ z)) := by rw [exp_add]
      _ = f z * exp 0 := by ring_nf
      _ = f z * 1 := by rw [exp_zero]
      _ = f z := mul_one _

end Complex

/-! ## Part 5: Application to the Right Half-Plane -/

namespace HolomorphicLog

open Complex Set

def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const continuous_re

lemma convex_rightHalfPlane : Convex ℝ rightHalfPlane := by
  intro x hx y hy a b ha hb _
  simp only [rightHalfPlane, mem_setOf_eq, add_re, smul_re] at hx hy ⊢
  rcases ha.lt_or_eq with ha_pos | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx) (mul_nonneg hb hy.le)
  · simp only [zero_smul, zero_add, (show b = 1 by linarith), one_smul]; exact hy

lemma rectangularConvex_rightHalfPlane : RectangularConvex rightHalfPlane := by
  intro x y hx hy
  simp only [rightHalfPlane, mem_setOf_eq, add_re, mul_re, I_re, I_im, mul_zero, mul_one,
    Complex.ofReal_re, Complex.ofReal_im, sub_self, add_zero] at hx hy ⊢
  exact ⟨hx, hy⟩

lemma nonempty_rightHalfPlane : rightHalfPlane.Nonempty := ⟨1, by simp [rightHalfPlane]⟩

/-- On the right half-plane, a nonvanishing holomorphic function has a holomorphic logarithm. -/
theorem exists_log_of_rightHalfPlane {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f rightHalfPlane)
    (hf_ne : ∀ z ∈ rightHalfPlane, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
      ∀ z ∈ rightHalfPlane, exp (g z) = f z :=
  hf.exists_log_of_rectangularConvex isOpen_rightHalfPlane convex_rightHalfPlane
    rectangularConvex_rightHalfPlane nonempty_rightHalfPlane hf_ne

end HolomorphicLog

end
