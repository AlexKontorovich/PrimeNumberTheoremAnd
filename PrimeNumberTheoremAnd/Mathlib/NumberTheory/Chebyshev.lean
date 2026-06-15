import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Chebyshev

open Nat hiding log
open scoped Nat.Prime
open Real Finset
open ArithmeticFunction hiding log id

/-- The primes up to $n$. -/
abbrev primesLE (n : ℕ) : Finset ℕ := filter Nat.Prime (range (n + 1))

theorem mem_primesLE_prime {p n : ℕ} (hp : p ∈ primesLE n) : p.Prime := by simp_all

theorem mem_primesLE_le {p n : ℕ} (hp : p ∈ primesLE n) : p ≤ n := by simp_all

theorem mem_primesLE_gt {p n : ℕ} (hp : p ∈ primesLE n) : 1 < p := (mem_primesLE_prime hp).one_lt

theorem mem_primesLE_ge {p n : ℕ} (hp : p ∈ primesLE n) : 2 ≤ p := (mem_primesLE_prime hp).two_le

theorem primesLE_mono : Monotone primesLE := by
  intros n m _ p
  simp; grind

theorem primesLE_eq_filter_Icc_zero (n : ℕ) : primesLE n = filter Nat.Prime (Icc 0 n) := by
  ext p
  simp

theorem primesLE_eq_filter_Icc_one (n : ℕ) : primesLE n = filter Nat.Prime (Icc 1 n) := by
  ext p
  simp +contextual [Nat.Prime.one_le]

theorem primesLE_eq_filter_Icc_two (n : ℕ) : primesLE n = filter Nat.Prime (Icc 2 n) := by
  ext p
  simp +contextual [Nat.Prime.two_le]

@[simp]
theorem card_primesLE (n : ℕ) : (primesLE n).card = π n := by
  simp only [primesLE, primeCounting, primeCounting', count_eq_card_filter_range]

theorem log_prime_pos {p : ℕ} (hp : p.Prime) : 0 < log p := by
  rw [Real.log_pos_iff (mod_cast p.zero_le)]
  exact_mod_cast hp.one_lt

theorem log_prime_ne {p : ℕ} (hp : p.Prime) : log p ≠ 0 := ne_of_gt (log_prime_pos hp)

theorem log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ log p := le_of_lt (log_prime_pos hp)

/-- Least common multiple of $\{1, \dots, n\}$. -/
abbrev lcmUpto (n : ℕ) : ℕ := (Icc 1 n).lcm id

theorem lcmUpto_ne_zero (n : ℕ) : lcmUpto n ≠ 0 := by
  simp

theorem lcmUpto_pos (n : ℕ) : 0 < lcmUpto n := pos_of_ne_zero <| lcmUpto_ne_zero n

theorem factorization_lcmUpto (n : ℕ) {p : ℕ} (hp : p.Prime) : (lcmUpto n).factorization p = p.log n := calc
  _ = (Icc 1 n).sup (fun k => k.factorization p) := Finset.factorization_lcm (fun k hk => by aesop) p
  _ = _ := by
    have := hp.one_lt
    refine le_antisymm ?_ ?_
    · simp only [Finset.sup_le_iff, mem_Icc, and_imp]
      intro m h1 h2
      exact le_log_of_pow_le this
        (le_of_dvd (Order.one_le_iff_pos.mp h1) (ordProj_dvd m p) |>.trans h2)
    rcases le_or_gt p n with _ | h
    · have := pow_log_le_self p (x := n) (by linarith)
      grw [← le_sup (b := p ^ p.log n) (by grind)]
      simp [hp]
    simp [log_of_lt h]

theorem lcmUpto_dvd_factorial (n : ℕ) : lcmUpto n ∣ n ! := by
  simp +contextual [dvd_factorial, Order.one_le_iff_pos]

theorem primeFactors_lcmUpto (n : ℕ) : primeFactors (lcmUpto n) = primesLE n := by
  ext p
  constructor
  · intro h
    have := prime_of_mem_primeFactors h
    rw [←support_factorization, Finsupp.mem_support_iff, factorization_lcmUpto _ this] at h
    simp_all
  intro h
  simp_all only [mem_filter, mem_range, Order.lt_add_one_iff, lcmUpto, mem_primeFactors, ne_eq,
    Finset.lcm_eq_zero_iff, mem_Icc, id_eq, exists_eq_right, nonpos_iff_eq_zero, one_ne_zero,
    _root_.zero_le, and_true, not_false_eq_true, true_and]
  convert dvd_lcm (b := p) ?_ <;> simp_all [h.2.one_le]

theorem primorial_dvd_lcmUpto (n : ℕ) : primorial n ∣ lcmUpto n := by
  simp only [primorial]
  convert prod_primeFactors_dvd _
  rw [primeFactors_lcmUpto]

theorem lcmUpto_eq_prod (n : ℕ) : lcmUpto n = ∏ p ∈ primesLE n, p ^ ((lcmUpto n).factorization p) := by
-- note: this method is deprecated and should be changed to prod_factorization_pow_eq_self when Mathlib bumps
  symm; convert prod_factorization_pow_eq_self (lcmUpto_ne_zero n)
  rw [Finsupp.prod_of_support_subset _ _ _ (by simp)]
  simp +contextual only [support_factorization, subset_iff, mem_primeFactors, ne_eq,
    Finset.lcm_eq_zero_iff, mem_Icc, id_eq, exists_eq_right, nonpos_iff_eq_zero, one_ne_zero,
    _root_.zero_le, and_true, not_false_eq_true, mem_filter, mem_range, Order.lt_add_one_iff,
    and_imp]
  intro p pp dp
  rw [← pp.dvd_factorial]
  exact dp.trans <| lcmUpto_dvd_factorial n

theorem lcmUpto_eq_prod_pow_log (n : ℕ) : lcmUpto n = ∏ p ∈ primesLE n, p ^ p.log n := by
  convert lcmUpto_eq_prod n using 3 with p hp
  simp only [mem_filter, mem_range, Order.lt_add_one_iff] at hp
  exact factorization_lcmUpto n hp.2 |>.symm

theorem lcmUpto_eq_prod_pow_floor (n : ℕ) : lcmUpto n = ∏ p ∈ primesLE n, p ^ ⌊log n / log p⌋₊ := by
  convert lcmUpto_eq_prod_pow_log n using 3
  rw [← natFloor_logb_natCast, ← log_div_log]

theorem primeCounting_ge (n : ℕ) : (n * log 2 - log (n + 1))/ log n ≤ π n := by
  rcases (show n=0 ∨ n=1 ∨ 1<n by omega) with rfl | rfl | h
  · simp
  · simp
  grw [div_le_iff₀ (log_pos (mod_cast h)), ←psi_le_primeCounting_mul_log, psi_ge]

theorem primeCounting_ge' {x : ℝ} (hx : 1 < x) :
  ((x-1) * log 2 - log (x + 2))/ log x ≤ π ⌊x⌋₊ := by
  grw [div_le_iff₀ (log_pos hx), ←psi_le_primeCounting_mul_log', psi_ge']
  positivity

theorem theta_eq_sum_log (n : ℕ) : theta n = ∑ p ∈ primesLE n, log p := by
  rw [theta_eq_sum_Icc, floor_natCast, primesLE_eq_filter_Icc_zero]

theorem theta_le_primeCounting_mul_log (n : ℕ) : theta n ≤ (primeCounting n) * log n :=
  (theta_le_psi n).trans (psi_le_primeCounting_mul_log n)

theorem theta_le_primeCounting_mul_log' (x : ℝ) : theta x ≤ (primeCounting ⌊x⌋₊) * log x := by
  grw [←psi_le_primeCounting_mul_log', theta_le_psi]

private theorem pi_mul_log_sqrt_le {x : ℝ} (hx : 1 ≤ x) : (primeCounting ⌊x⌋₊) * log √x ≤ log 4 * x + √x * log √x
  := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log √x := by simp
  _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, (log p + (if p ≤ √x then log √x else 0)) := by
    apply sum_le_sum; intro p hp
    split_ifs with h
    · simp [log_prime_nonneg (mem_primesLE_prime hp)]
    have : log √x < log p := by
      apply log_lt_log (by positivity) (not_le.mp h)
    nth_grw 1 [this]
    simp
  _ ≤ _ := by
    grw [← theta_le_log4_mul_x (by positivity)]
    rw [sum_add_distrib, theta_eq_theta_coe_floor, theta_eq_sum_log, ←sum_filter]
    simp only [sum_const, nsmul_eq_mul, add_le_add_iff_left]
    gcongr
    · exact log_nonneg (one_le_sqrt.mpr hx)
    calc
      _ ≤ ((Icc 1 ⌊√x⌋₊).card : ℝ) := by
        norm_cast; apply Finset.card_mono
        intro p
        simp only [mem_filter, mem_range, Order.lt_add_one_iff, and_imp]
        intro _ hp h; simp only [mem_Icc]
        exact ⟨ hp.one_le, le_floor h⟩
      _ ≤ _ := by
        simp only [card_Icc, add_tsub_cancel_right]
        apply floor_le
        positivity

end Chebyshev
