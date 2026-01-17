import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula


/-!
# Robbins' Bounds for Stirling's Approximation

This file proves Robbins' sharp two-sided bounds for the factorial:

  √(2πn) (n/e)^n e^{1/(12n+1)} ≤ n! ≤ √(2πn) (n/e)^n e^{1/(12n)}

These bounds are derived from Binet's formula and the bounds on the Binet integral J(z).

## Main Results

* `Stirling.factorial_upper_robbins`: n! ≤ √(2πn)(n/e)^n e^{1/(12n)}
* `Stirling.factorial_lower_robbins`: n! ≥ √(2πn)(n/e)^n e^{1/(12n+1)}
* `Stirling.log_factorial_theta`: log(n!) = n log n - n + log(2πn)/2 + θ/(12n)
* `Stirling.factorial_asymptotic`: n! ~ √(2πn)(n/e)^n

## Dependencies

This file builds on:
- `BinetKernel.lean`: The kernel K̃(t) with bounds 0 ≤ K̃(t) ≤ 1/12
- `BinetFormula.lean`: The Binet integral J(z) with bound |J(z)| ≤ 1/(12·Re(z))



## Strategy

1. Apply Binet's formula to Γ(n+1) = n!
2. Use the bounds 0 ≤ J(n+1) ≤ 1/(12(n+1))
3. For the lower bound, use the refined estimate J(n+1) ≥ 1/(12(n+1)+1)

## References

* Robbins, H. "A Remark on Stirling's Formula." Amer. Math. Monthly 62 (1955): 26-29.
* Feller, W. "An Introduction to Probability Theory and Its Applications", Vol. 1
* NIST DLMF 5.11.3
-/

open Real Set MeasureTheory Filter Topology
open scoped BigOperators Nat

noncomputable section

namespace Stirling

/-! ## Section 1: Setup and basic facts -/

/-- For n ≥ 1, Γ(n+1) = n!. -/
lemma Gamma_nat_eq_factorial (n : ℕ) : Real.Gamma (n + 1) = n.factorial := by
  exact_mod_cast Real.Gamma_nat_eq_factorial n

/-- log(n!) = log Γ(n+1) for n ≥ 1. -/
lemma log_factorial_eq_log_Gamma {n : ℕ} (_hn : 0 < n) :
    Real.log (n.factorial : ℝ) = Real.log (Real.Gamma (n + 1)) := by
  rw [Gamma_nat_eq_factorial]

/-! ## Section 2: The theta parameter -/

/-- For n ≥ 1, there exists θ ∈ (0, 1) such that
log(n!) = n log n - n + log(2πn)/2 + θ/(12n).

This is the precise form of Stirling's approximation with explicit error. -/
theorem log_factorial_theta {n : ℕ} (hn : 0 < n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      Real.log (n.factorial : ℝ) =
        n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + θ / (12 * n) := by
  have h_fact : Real.log (n.factorial) = Real.log n + Real.log (Real.Gamma n) := by
    rw [← Real.log_mul (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr hn)).ne']
    rw [← Real.Gamma_add_one (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
    rw [Real.Gamma_nat_eq_factorial]
  let x : ℝ := n
  have hx : 0 < x := Nat.cast_pos.mpr hn
  -- Binet formula for log Gamma(x)
  have h_binet : Real.log (Real.Gamma x) = (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (Binet.J x).re := by
    exact BinetFormula.Real_log_Gamma_eq_Binet hx
  -- Bounds on J(x)
  have h_J_bounds : 0 < (Binet.J x).re ∧ (Binet.J x).re < 1 / (12 * x) := by
    constructor
    · exact BinetFormula.re_J_pos hx
    · exact BinetFormula.re_J_lt_one_div_twelve hx
  rcases h_J_bounds with ⟨hJ_pos, hJ_ub⟩
  let θ := 12 * x * (Binet.J x).re
  use θ
  constructor
  · exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 12) hx) hJ_pos
  constructor
  · have h12x_pos : 0 < 12 * x := mul_pos (by norm_num : (0 : ℝ) < 12) hx
    have h12x_ne : (12 * x) ≠ 0 := ne_of_gt h12x_pos
    calc θ = 12 * x * (Binet.J x).re := rfl
      _ < 12 * x * (1 / (12 * x)) := by
          exact mul_lt_mul_of_pos_left hJ_ub h12x_pos
      _ = 1 := by
          field_simp [h12x_ne]
  rw [h_fact, h_binet]
  have h_theta : θ / (12 * x) = (Binet.J x).re := by field_simp [θ]; ring
  rw [h_theta]
  have h_log_term : Real.log (2 * Real.pi * n) / 2 = Real.log (2 * Real.pi) / 2 + Real.log n / 2 := by
    rw [Real.log_mul (by positivity) (by positivity)]
    ring
  rw [h_log_term]
  ring

/-! ## Section 3: Upper bound -/

/-- Helper for exp(log x / 2) = sqrt x. -/
lemma exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- Exponentiating the Stirling formula with θ < 1 gives the upper bound.

This completes the sorry in `GammaStirlingAux.factorial_asymptotic`. -/
theorem factorial_upper_robbins (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_log_le : Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) := by
    rw [hlog]
    apply add_le_add_right
    apply div_le_div_of_nonneg_right (le_of_lt hθ_lt_one)
    exact mul_nonneg (by norm_num) hn_pos.le
  have h_exp := Real.exp_le_exp.mpr h_log_le
  rw [Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos n))] at h_exp
  -- Simplify RHS
  have h_pow_eq : (n : ℝ) ^ (n : ℝ) / Real.exp n = ((n : ℝ) / Real.exp 1) ^ n := by
    have h1 : Real.exp n = (Real.exp 1) ^ n := by rw [← Real.exp_one_rpow, Real.rpow_natCast]
    rw [h1]
    have h2 : (n : ℝ) ^ (n : ℝ) = (n : ℝ) ^ n := Real.rpow_natCast n n
    rw [h2, div_pow]
  have h_exp_n : Real.exp ((n : ℝ) * Real.log n) = (n : ℝ) ^ (n : ℝ) := by
    rw [mul_comm, Real.rpow_def_of_pos hn_pos]
  have h_sqrt : Real.exp (Real.log (2 * Real.pi * n) / 2) = Real.sqrt (2 * Real.pi * n) :=
    exp_half_log (by positivity : 0 < 2 * Real.pi * n)
  convert h_exp using 1
  -- Split off the `exp(1/(12n))` factor on the RHS, then cancel it.
  rw [Real.exp_add]
  have hexp_ne : Real.exp (1 / (12 * (n : ℝ))) ≠ 0 := Real.exp_ne_zero _
  apply mul_right_cancel₀ hexp_ne
  -- Now show `exp(n log n - n + log(2πn)/2) = sqrt(2πn) * (n/exp 1)^n`.
  have hA :
      (n : ℝ) * Real.log n - n + Real.log (2 * Real.pi * n) / 2
        = ((n : ℝ) * Real.log n - n) + Real.log (2 * Real.pi * n) / 2 := by
    ring
  -- Expand the exponential of a sum and rewrite the `sqrt` factor.
  rw [hA, Real.exp_add, h_sqrt]
  -- Rewrite `exp(n log n - n)` as `(n/exp 1)^n`.
  have hExpMain :
      Real.exp ((n : ℝ) * Real.log n - n) = ((n : ℝ) / Real.exp 1) ^ n := by
    -- `exp(a - b) = exp a / exp b`
    rw [Real.exp_sub]
    -- `exp(n log n) = n^n` (as a real power)
    rw [h_exp_n]
    -- turn `/(exp n)` into the `((n/exp 1)^n)` form
    simpa [div_eq_mul_inv, Real.exp_nat_mul] using h_pow_eq
  -- Finish by commutativity.
  simp [hExpMain, mul_left_comm, mul_comm]

/-! ## Section 4: Lower bound -/

/-- For the lower bound, we need J(n+1) ≥ 1/(12(n+1)+1).

This refined lower bound on the Binet integral uses monotonicity of K̃. -/
lemma J_lower_bound (n : ℕ) :
    1 / (12 * (n + 1 : ℝ) + 1) ≤ (Binet.J (n + 1 : ℂ)).re := by
  -- The proof only uses `n+1 > 0`.
  let x : ℝ := n + 1
  have hx : 0 < x := by
    dsimp [x]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  -- rewrite the real part of `J` using the `x` notation
  have hJ : (Binet.J (n + 1 : ℂ)).re =
      ∫ t in Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
    simpa [x] using (BinetFormula.re_J_eq_integral_Ktilde (x := x) hx)
  rw [hJ]
  -- We use the bound K̃(t) ≥ (1/12) * e^{-t/12}
  have h_bound : ∀ t ∈ Ioi 0, (1/12) * Real.exp (-t/12) ≤ BinetKernel.Ktilde t := by
    intro t ht
    -- Robbins-type pointwise lower bound for the Binet kernel, proved in `BinetKernel.lean`.
    simpa using (BinetKernel.Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve (t := t) (by simpa using ht))

  -- We integrate the inequality
  have h_int_le : ∫ t in Ioi 0, (1/12) * Real.exp (-t/12) * Real.exp (-t * x) ≤
                  ∫ t in Ioi 0, BinetKernel.Ktilde t * Real.exp (-t * x) := by
    -- integrability of the LHS integrand
    have h_left_int :
        IntegrableOn (fun t : ℝ => (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x))
          (Ioi (0 : ℝ)) volume := by
      -- rewrite as a constant times a single exponential `exp (-(x+1/12)*t)`
      have hx' : 0 < x + 1 / 12 := by linarith [hx]
      have hExp :
          IntegrableOn (fun t : ℝ => Real.exp (-(x + 1 / 12) * t)) (Ioi (0 : ℝ)) volume := by
        apply integrableOn_exp_mul_Ioi (a := -(x + 1 / 12)) (c := 0)
        nlinarith [hx']
      have hConst :
          IntegrableOn (fun t : ℝ => (1 / 12 : ℝ) * Real.exp (-(x + 1 / 12) * t))
            (Ioi (0 : ℝ)) volume := by
        simpa [IntegrableOn] using
          (MeasureTheory.Integrable.const_mul (μ := volume.restrict (Ioi (0 : ℝ))) (h := hExp) (c := (1 / 12 : ℝ)))
      refine hConst.congr_fun ?_ measurableSet_Ioi
      intro t ht
      have hexp : Real.exp (-(x + 1 / 12) * t) = Real.exp (-t / 12) * Real.exp (-t * x) := by
        have : (-(x + 1 / 12) * t) = (-t / 12) + (-t * x) := by ring
        calc
          Real.exp (-(x + 1 / 12) * t) = Real.exp ((-t / 12) + (-t * x)) := by simpa [this]
          _ = Real.exp (-t / 12) * Real.exp (-t * x) := by simp [Real.exp_add]
      -- rewrite without `simpa` to avoid simp-normal-form mismatches
      have h1 :
          (1 / 12 : ℝ) * Real.exp (-(x + 1 / 12) * t)
            = (1 / 12 : ℝ) * (Real.exp (-t / 12) * Real.exp (-t * x)) :=
        congrArg (fun y => (1 / 12 : ℝ) * y) hexp
      calc
        (1 / 12 : ℝ) * Real.exp (-(x + 1 / 12) * t)
            = (1 / 12 : ℝ) * (Real.exp (-t / 12) * Real.exp (-t * x)) := h1
        _ = (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x) := by simp [mul_assoc]
    -- apply monotonicity under `ae` on the restricted measure
    refine MeasureTheory.setIntegral_mono_ae_restrict h_left_int
      (BinetFormula.integrable_Ktilde_mul_exp_neg_mul hx) ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi)] with t ht
    gcongr
    exact h_bound t ht

  -- Calculate the LHS integral
  have h_lhs : ∫ t in Ioi 0, (1/12) * Real.exp (-t/12) * Real.exp (-t * x) = 1 / (12 * x + 1) := by
    -- rewrite integrand as `(1/12) * exp (-(x+1/12)*t)` and use `Binet.integral_exp_neg_mul_Ioi`
    have hx' : 0 < x + 1 / 12 := by linarith [hx]
    have hexp : ∀ t : ℝ,
        (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x)
          = (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12)) := by
      intro t
      have hmul : Real.exp (-t / 12) * Real.exp (-t * x) = Real.exp (-t * (x + 1 / 12)) := by
        calc
          Real.exp (-t / 12) * Real.exp (-t * x) = Real.exp ((-t / 12) + (-t * x)) := by
            symm
            simp [Real.exp_add]
          _ = Real.exp (-t * (x + 1 / 12)) := by
            congr 1
            ring
      have h1 :
          (1 / 12 : ℝ) * (Real.exp (-t / 12) * Real.exp (-t * x))
            = (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12)) :=
        congrArg (fun y => (1 / 12 : ℝ) * y) hmul
      calc
        (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x)
            = (1 / 12 : ℝ) * (Real.exp (-t / 12) * Real.exp (-t * x)) := by simp [mul_assoc]
        _ = (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12)) := by simpa using h1
    -- apply the pointwise rewrite inside the integral
    have hbase : ∫ t in Ioi (0 : ℝ), Real.exp (-t * (x + 1 / 12)) = 1 / (x + 1 / 12) := by
      simpa using (Binet.integral_exp_neg_mul_Ioi (x := x + 1 / 12) hx')
    calc
      (∫ t in Ioi (0 : ℝ), (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x))
          = ∫ t in Ioi (0 : ℝ), (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12)) := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
              intro t ht
              -- `hexp` is pointwise equality of the integrands
              simpa using (hexp t)
      _ = (1 / 12 : ℝ) * ∫ t in Ioi (0 : ℝ), Real.exp (-t * (x + 1 / 12)) := by
              simp [MeasureTheory.integral_const_mul]
      _ = (1 / 12 : ℝ) * (1 / (x + 1 / 12)) := by simp only [one_div, neg_mul,
        mul_eq_mul_left_iff, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]; simp_all
      _ = 1 / (12 * x + 1) := by
              field_simp

  rw [h_lhs] at h_int_le
  exact h_int_le

/-- The Robbins lower bound. -/
theorem factorial_lower_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_J_ge : (1 + (n : ℝ) * 12)⁻¹ ≤ (Binet.J n).re := by
    -- apply the bound to `n = (n-1)+1`
    have h0 : (1 / (12 * (n : ℝ) + 1) : ℝ) ≤ (Binet.J n).re := by
      simpa [Nat.add_sub_cancel, Nat.cast_sub (Nat.succ_le_of_lt hn)] using (J_lower_bound (n := n - 1))
    have h0' : (12 * (n : ℝ) + 1)⁻¹ ≤ (Binet.J n).re := by
      simpa [one_div] using h0
    -- rewrite `(12*n+1)⁻¹` to `(1+n*12)⁻¹`
    convert h0' using 1; ring_nf
  have h_log_ge : n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n + 1) ≤ Real.log (n.factorial : ℝ) := by
    have h_fact : Real.log (n.factorial) = Real.log n + Real.log (Real.Gamma n) := by
      rw [← Real.log_mul (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr hn)).ne']
      rw [← Real.Gamma_add_one (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
      rw [Real.Gamma_nat_eq_factorial]
    have h_binet : Real.log (Real.Gamma n) = (n - 1/2) * Real.log n - n + Real.log (2 * Real.pi) / 2 + (Binet.J n).re := by
      exact BinetFormula.Real_log_Gamma_eq_Binet hn_pos
    rw [h_fact, h_binet]
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
    rw [Real.log_mul h2pi_pos.ne' (Nat.cast_pos.mpr hn).ne']
    ring_nf
    simp only [add_le_add_iff_left]
    exact h_J_ge
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi * n) := by
    apply Real.sqrt_pos.mpr
    -- `0 < 2 * π * n`
    simpa [mul_assoc] using (mul_pos h2pi_pos hn_pos)
  rw [← Real.log_le_log_iff
    (mul_pos (mul_pos h_sqrt_pos (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)) (Real.exp_pos _))
    (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  convert h_log_ge using 1
  rw [Real.log_mul (mul_pos h_sqrt_pos (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)).ne' (Real.exp_pos _).ne']
  rw [Real.log_exp]
  rw [Real.log_mul h_sqrt_pos.ne' (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n).ne']
  rw [Real.log_sqrt (le_of_lt (mul_pos h2pi_pos hn_pos))]
  rw [Real.log_pow, Real.log_div hn_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-! ## Section 5: Two-sided bound -/

/-- The complete Robbins bound. -/
theorem factorial_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial ∧
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨factorial_lower_robbins n hn, factorial_upper_robbins n hn⟩

/-! ## Section 6: Asymptotic equivalence -/

/-- The ratio n! / (√(2πn)(n/e)^n) → 1 as n → ∞. -/
theorem factorial_asymptotic :
    Tendsto (fun n : ℕ => (n.factorial : ℝ) /
      (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n)) atTop (𝓝 1) := by
  let lower (n : ℕ) := (1 : ℝ)
  let upper (n : ℕ) := Real.exp (1 / (12 * n))
  have h_squeeze : ∀ᶠ n in atTop, lower n ≤ (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ∧
                                  (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ≤ upper n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
    let stirling := Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n
    have h_stirling_pos : 0 < stirling := by
      apply mul_pos
      ·
        have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        exact Real.sqrt_pos.mpr (mul_pos h2pi_pos hn_pos)
      · apply pow_pos; apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
    rw [le_div_iff₀ h_stirling_pos, div_le_iff₀ h_stirling_pos]
    have h_log_stirling : Real.log stirling = n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 := by
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [Real.log_mul (Real.sqrt_pos.mpr (mul_pos h2pi_pos hn_pos)).ne'
        (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n).ne']
      rw [Real.log_sqrt (le_of_lt (mul_pos h2pi_pos hn_pos))]
      rw [Real.log_pow, Real.log_div (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.exp_pos 1).ne']
      rw [Real.log_exp]; ring
    constructor
    · -- `lower n = 1`, so this is `stirling ≤ n!`
      simp [lower]
      rw [← Real.log_le_log_iff h_stirling_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)), h_log_stirling]
      -- rewrite `log (n!)` using the Robbins/Binet expansion
      rw [hlog]
      simp only [le_add_iff_nonneg_right]
      positivity
    · -- `upper n = exp (1/(12n))`
      simp [upper]
      rw [← Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.factorial_pos n)) (mul_pos (Real.exp_pos _) h_stirling_pos)]
      rw [Real.log_mul (Real.exp_pos _).ne' h_stirling_pos.ne', Real.log_exp, h_log_stirling]
      -- rewrite `log (n!)` using the Robbins/Binet expansion
      rw [hlog]
      -- reduce to `θ / (12n) ≤ 1 / (12n)` and use `θ < 1`
      have hn' : (0 : ℝ) < 12 * (n : ℝ) := by
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        nlinarith
      have hθle : θ ≤ 1 := le_of_lt hθ_lt_one
      have hθ_div : θ / (12 * (n : ℝ)) ≤ 1 / (12 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hθle (le_of_lt hn')
      -- isolate the common term and use `add_le_add_left`
      set c : ℝ := (n : ℝ) * Real.log n - n + Real.log (2 * Real.pi * n) / 2
      have hc : c + θ / (12 * (n : ℝ)) ≤ c + 1 / (12 * (n : ℝ)) := by
        simpa [c, add_assoc, add_left_comm, add_comm] using add_le_add_left hθ_div c
      -- goal is the same inequality, up to commutativity and rewriting `1/(12n)` as an inverse
      simpa [one_div, c, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hc
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n : ℕ =>
      (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n))
    (g := lower) (h := upper) tendsto_const_nhds ?_ ?_ ?_)
  · -- `upper n = exp (1/(12n)) → exp 0 = 1`
    have h_lim : Tendsto (fun n : ℕ => 1 / (12 * (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      -- first show `12 * n → +∞`, then compose with `x ↦ x⁻¹ → 0`
      have h_to : Tendsto (fun n : ℕ => (12 : ℝ) * (n : ℝ)) atTop atTop := by
        have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
          simpa using (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)
        simpa [mul_comm] using
          (Filter.Tendsto.const_mul_atTop (β := ℕ) (α := ℝ) (r := (12 : ℝ)) (by positivity) hn)
      have h_inv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)) := by
        simpa using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)))
      have : Tendsto (fun n : ℕ => ((12 : ℝ) * (n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
        h_inv.comp h_to
      simpa [one_div] using this
    have h_exp : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp (0 : ℝ))) :=
      Real.continuous_exp.tendsto (0 : ℝ)
    have : Tendsto (fun n : ℕ => Real.exp (1 / (12 * (n : ℝ)))) atTop (𝓝 (Real.exp (0 : ℝ))) :=
      h_exp.comp h_lim
    simpa [upper, Real.exp_zero] using this
  · filter_upwards [h_squeeze] with n hn
    exact hn.1
  · filter_upwards [h_squeeze] with n hn
    exact hn.2

/-- Stirling's approximation: n! ~ √(2πn)(n/e)^n. -/
theorem stirling_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (n.factorial : ℝ))
      (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · exact factorial_asymptotic
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    apply ne_of_gt
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    apply mul_pos (Real.sqrt_pos.mpr _) (pow_pos _ _)
    · positivity
    · have : 0 < n / Real.exp 1 := div_pos hn_pos (Real.exp_pos 1)
      linarith

end Stirling

/-! ## Section 7: Convenient API -/

namespace Nat

/-- Upper bound: n! ≤ √(2πn)(n/e)^n · e^{1/(12n)} for n ≥ 1. -/
theorem factorial_le_stirling_upper (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  Stirling.factorial_upper_robbins n hn

/-- Lower bound: √(2πn)(n/e)^n · e^{1/(12n+1)} ≤ n! for n ≥ 1. -/
theorem factorial_ge_stirling_lower (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial :=
  Stirling.factorial_lower_robbins n hn

end Nat

end
