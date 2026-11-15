import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Elementary finite tails of the prime logarithms

Finite Abel summation and the elementary Chebyshev bound
`θ(x) ≤ log(4) * x` give the two tail estimates below. There is no
prime-number asymptotic, zero hypothesis, or infinite-sum interchange.

The exact-source compiler receipt and transitive axiom audit are recorded
separately in `verification/prime-log-tail-run.json`.
-/

open Finset Real MeasureTheory

namespace TernaryGoldbach.RSBounds.PrimeLogTail

private noncomputable def primeLog (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

private theorem theta_eq_sum (x : ℝ) :
    Chebyshev.theta x = ∑ n ∈ Icc 0 ⌊x⌋₊, primeLog n := by
  simp [Chebyshev.theta_eq_sum_Icc, primeLog, sum_filter]

private theorem hasDerivAt_inv_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => 1 / u ^ 2) (-2 / t ^ 3) t := by
  convert (hasDerivAt_pow 2 t).fun_inv (pow_ne_zero 2 ht) using 1
  · funext u
    simp only [one_div]
  · norm_num
    field_simp [ht] <;> ring

private theorem continuousOn_const_div_pow {a b c : ℝ} (ha : 0 < a) (k : ℕ) :
    ContinuousOn (fun t : ℝ => c / t ^ k) (Set.Icc a b) := by
  apply continuousOn_const.div (continuousOn_id.pow k)
  intro t ht
  exact pow_ne_zero k (ne_of_gt (ha.trans_le ht.1))

private theorem intervalIntegrable_theta_div_cube {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 2 * Chebyshev.theta t / t ^ 3) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hi : IntegrableOn (fun t : ℝ => 2 / t ^ 3) (Set.Icc a b) :=
    (continuousOn_const_div_pow ha 3).integrableOn_Icc
  have hs := integrableOn_mul_sum_Icc primeLog (m := 0) ha.le hi
  apply hs.congr_fun ?_ measurableSet_Icc
  intro t ht
  change (2 / t ^ 3) * (∑ k ∈ Icc 0 ⌊t⌋₊, primeLog k) =
    2 * Chebyshev.theta t / t ^ 3
  rw [← theta_eq_sum]
  ring

/-- The exact finite Abel identity underlying the elementary tail bound. -/
theorem sum_prime_log_div_sq_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2) =
      Chebyshev.theta b / b ^ 2 - Chebyshev.theta a / a ^ 2 +
        ∫ t in a..b, 2 * Chebyshev.theta t / t ^ 3 := by
  have hd : ∀ t ∈ Set.Icc a b,
      deriv (fun u : ℝ => 1 / u ^ 2) t = -2 / t ^ 3 := by
    intro t ht
    exact (hasDerivAt_inv_sq (ne_of_gt (ha.trans_le ht.1))).deriv
  have hi : IntegrableOn (deriv (fun u : ℝ => 1 / u ^ 2)) (Set.Icc a b) := by
    apply (continuousOn_const_div_pow (c := -2) ha 3).integrableOn_Icc.congr_fun
      (fun t ht => (hd t ht).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul primeLog ha.le hab
    (fun t ht => (hasDerivAt_inv_sq (ne_of_gt (ha.trans_le ht.1))).differentiableAt) hi
  simp_rw [← theta_eq_sum] at habel
  have hsum :
      (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (1 / (p : ℝ) ^ 2) * primeLog p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime <;> simp [primeLog, hprime, div_eq_mul_inv, mul_comm]
  have hint :
      (∫ t in Set.Ioc a b, deriv (fun u : ℝ => 1 / u ^ 2) t * Chebyshev.theta t) =
      -(∫ t in a..b, 2 * Chebyshev.theta t / t ^ 3) := by
    rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change deriv (fun u : ℝ => 1 / u ^ 2) t * Chebyshev.theta t =
      -(2 * Chebyshev.theta t / t ^ 3)
    rw [hd t ht]
    ring
  rw [hsum, habel, hint]
  ring

private theorem integral_const_div_sq {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, c / t ^ 2) = c * (1 / a - 1 / b) := by
  have hi : IntervalIntegrable (fun t : ℝ => c / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const_div_pow ha 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(c * t⁻¹)) (f' := fun t : ℝ => c / t ^ 2)
    (a := a) (b := b) (fun t ht => by
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
      convert ((hasDerivAt_inv ht0).const_mul c).neg using 1 <;> ring) hi
  calc
    _ = -(c * b⁻¹) - -(c * a⁻¹) := h
    _ = c * (1 / a - 1 / b) := by ring

/-- A finite reciprocal-square prime-log tail, with arbitrary real endpoints. -/
theorem sum_prime_log_div_sq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2) ≤
      2 * Real.log 4 / a := by
  have hb : 0 < b := ha.trans_le hab
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hi :
      (∫ t in a..b, 2 * Chebyshev.theta t / t ^ 3) ≤
      ∫ t in a..b, (2 * Real.log 4) / t ^ 2 := by
    apply intervalIntegral.integral_mono_on hab (intervalIntegrable_theta_div_cube ha hab)
      (ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hab]
        exact continuousOn_const_div_pow ha 2))
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    calc
      2 * Chebyshev.theta t / t ^ 3 ≤ 2 * (Real.log 4 * t) / t ^ 3 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x ht0.le) (by norm_num))
          (by positivity)
      _ = (2 * Real.log 4) / t ^ 2 := by field_simp [ht0.ne'] <;> ring
  rw [integral_const_div_sq ha hab] at hi
  have htop : Chebyshev.theta b / b ^ 2 ≤ Real.log 4 / b := by
    calc
      _ ≤ (Real.log 4 * b) / b ^ 2 :=
        div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x hb.le) (by positivity)
      _ = _ := by field_simp [hb.ne'] <;> ring
  have hbottom : 0 ≤ Chebyshev.theta a / a ^ 2 :=
    div_nonneg (Chebyshev.theta_nonneg _) (sq_nonneg _)
  have hnonneg : 0 ≤ Real.log 4 / b := div_nonneg hlog hb.le
  rw [sum_prime_log_div_sq_eq ha hab]
  have halg : 2 * Real.log 4 * (1 / a - 1 / b) =
      2 * Real.log 4 / a - 2 * (Real.log 4 / b) := by ring
  rw [halg] at hi
  linarith

/-- The denominator `p(p−1)` costs only the factor `a/(a−1)` above the cutoff. -/
theorem sum_prime_log_div_mul_pred_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
      Real.log p / ((p : ℝ) * (p - 1))) ≤ 2 * Real.log 4 / (a - 1) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hpoint : ∀ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
      Real.log p / ((p : ℝ) * (p - 1)) ≤
        (a / (a - 1)) * (Real.log p / (p : ℝ) ^ 2) := by
    intro p hp
    have hpa : a < (p : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hp0 : (0 : ℝ) < p := ha0.trans hpa
    have hp1 : (0 : ℝ) < p - 1 := by linarith
    have hfrac : (p : ℝ) / (p - 1) ≤ a / (a - 1) := by
      rw [div_le_div_iff₀ hp1 ha1]
      nlinarith
    calc
      _ = ((p : ℝ) / (p - 1)) * (Real.log p / (p : ℝ) ^ 2) := by
        field_simp [hp0.ne', hp1.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac
        (div_nonneg (Real.log_natCast_nonneg p) (sq_nonneg _))
  calc
    _ ≤ ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
        (a / (a - 1)) * (Real.log p / (p : ℝ) ^ 2) := sum_le_sum hpoint
    _ = (a / (a - 1)) *
        ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime,
          Real.log p / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (a / (a - 1)) * (2 * Real.log 4 / a) :=
      mul_le_mul_of_nonneg_left (sum_prime_log_div_sq_le ha0 hab) (div_nonneg ha0.le ha1.le)
    _ = 2 * Real.log 4 / (a - 1) := by field_simp [ha0.ne', ha1.ne'] <;> ring

end TernaryGoldbach.RSBounds.PrimeLogTail
