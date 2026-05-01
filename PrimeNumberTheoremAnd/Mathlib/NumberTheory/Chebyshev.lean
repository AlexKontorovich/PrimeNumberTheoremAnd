import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Finset


open Classical _root_.Nat in
/-- An analogue of `Nat.factorization_lcm` for `Finset.lcm`. -/
theorem factorization_lcm {β : Type*} {f : β → ℕ} {s : Finset β}
    (hf : ∀ k ∈ s, f k ≠ 0) (p : ℕ) :
    (s.lcm f).factorization p = s.sup fun a => (f a).factorization p := by
  induction s using Finset.induction with
  | empty =>
    simp [lcm, fold_empty, factorization_one, Finsupp.coe_zero, sup_empty]
  | insert _ _ _ _ =>
    simp_all [lcm_eq_nat_lcm, Nat.factorization_lcm]

end Finset

namespace Chebyshev

open Nat hiding log
open Real Finset
open ArithmeticFunction hiding log id


/-- Least common multiple of $\{1, \dots, n\}$. -/
abbrev lcmUpto (n : ℕ) : ℕ := (Icc 1 n).lcm id

theorem lcmUpto_ne_zero (n : ℕ) : lcmUpto n ≠ 0 := by simp

theorem lcmUpto_pos (n : ℕ) : 0 < lcmUpto n := pos_of_ne_zero <| lcmUpto_ne_zero n

/-- The primes up to $n$. -/
abbrev primesLE (n : ℕ) : Finset ℕ := filter Nat.Prime (range (n + 1))

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
theorem card_primesLE (n : ℕ) : (primesLE n).card = primeCounting n := by
  simp only [primesLE, primeCounting, primeCounting', count_eq_card_filter_range]

theorem factorization_lcmUpto (n : ℕ) {p : ℕ} (hp : p.Prime) : (lcmUpto n).factorization p = p.log n := calc
  _ = (Icc 1 n).sup (fun k => k.factorization p) := Finset.factorization_lcm (fun k hk => by grind) p
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
  simp +contextual [lcmUpto, dvd_factorial, Order.one_le_iff_pos]

theorem lcmUpto_eq_prod (n : ℕ) : lcmUpto n = ∏ p ∈ primesLE n, p ^ ((lcmUpto n).factorization p) := by
-- note: this method is deprecated and should be cfix leanhanged to prod_factorization_pow_eq_self when Mathlib bumps
  symm; convert factorization_prod_pow_eq_self (lcmUpto_ne_zero n)
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

theorem psi_eq_sum_mul_log_prime (n : ℕ) : psi n = ∑ p ∈ primesLE n, p.log n * log p := calc
  _ = ∑ m ∈ Icc 1 n, vonMangoldt m := by unfold psi; aesop
  _ = ∑ m ∈ Finset.biUnion (filter Nat.Prime (Icc 1 n))
    (fun p => image (fun k => p ^ k) (Icc 1 (p.log n))), vonMangoldt m := by
    symm; apply sum_subset
    · intro q
      simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, forall_exists_index, and_imp]
      intro p _ _ _ m _ hm rfl
      exact ⟨by grind, pow_le_of_le_log (by linarith) hm⟩
    intro x hx
    simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, not_exists, not_and, and_imp,
      vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
    contrapose!
    rintro ⟨p, k, hp, hk, rfl⟩
    simp only [mem_Icc] at hx
    refine ⟨p, ⟨hp.one_le, ?_, hp, ⟨k, ⟨by linarith, ?_, rfl⟩⟩⟩⟩
    · linarith [le_of_dvd (by linarith) (dvd_pow_self p hk.ne')]
    exact le_log_of_pow_le hp.one_lt hx.2
  _ = ∑ p ∈ Icc 1 n with Nat.Prime p, ∑ q ∈ image (fun k ↦ p ^ k) (Icc 1 (p.log n)), Λ q := by
    convert sum_biUnion ?_
    intros p hp q hq hpq
    simp_all only [ne_eq, coe_filter, mem_Icc, Set.mem_setOf_eq, disjoint_left, mem_image,
      not_exists, not_and, and_imp, forall_exists_index, one_le_iff_ne_zero]
    intro a n hn _ rfl m hm _ h
    apply hpq
    exact Nat.Prime.pow_inj' hp.2 hq.2 hn hm h.symm |>.1
  _ = ∑ p ∈ primesLE n, ∑ k ∈ Icc 1 (p.log n), vonMangoldt (p ^ k) := by
    apply sum_congr (primesLE_eq_filter_Icc_one n).symm
    intro p hp
    apply sum_image
    intro a _ b _ hab
    exact Nat.pow_right_injective (Nat.Prime.two_le (by aesop)) hab
  _ = ∑ p ∈ primesLE n, ∑ k ∈ Icc 1 (p.log n), log p := by
    apply sum_congr rfl; intro p hp
    apply sum_congr rfl; intro k hk
    simp only [primesLE, mem_filter, mem_range, Order.lt_add_one_iff, mem_Icc] at hp hk
    rw [vonMangoldt_apply_pow (by linarith), vonMangoldt_apply_prime hp.2]
  _ = _ := by simp

/-- $\psi(n) = \log(\mathrm{lcm}(1, \dots, n))$. -/
theorem psi_eq_log_lcmUpto (n : ℕ) : psi n = log (lcmUpto n) := by
  rw [lcmUpto_eq_prod_pow_log, Nat.cast_prod, log_prod]
  · simp [psi_eq_sum_mul_log_prime]
  · simp +contextual

/-- $\mathrm{lcm}(1, \dots, n)$ is divisible by $\binom{n}{k}$ for all $k \le n$. -/
theorem choose_dvd_lcmUpto {n k : ℕ} (hkn : k ≤ n) : choose n k ∣ lcmUpto n := by
  rw [← factorization_prime_le_iff_dvd (choose_ne_zero hkn) (lcmUpto_ne_zero n)]
  intro p hp
  rw [factorization_lcmUpto n hp]
  exact factorization_choose_le_log

theorem two_pow_le_mul_lcmUpto (n : ℕ) : 2 ^ n ≤ (n + 1) * lcmUpto n := calc
  _ = ∑ m ∈ range (n + 1), n.choose m := (sum_range_choose _).symm
  _ ≤ ∑ k ∈ Finset.range (n + 1), lcmUpto n := by
    refine sum_le_sum fun k hk => ?_
    simp only [mem_range, Order.lt_add_one_iff] at hk
    exact Nat.le_of_dvd (lcmUpto_pos n) (choose_dvd_lcmUpto hk)
  _ = _ := by simp

/-- The Chebyshev lower bound for $\psi$. -/
theorem psi_ge (n : ℕ) : n * log 2 - log (n + 1) ≤ psi n := by
  have : log (2 ^ n) ≤ log ((n + 1) * lcmUpto n) := by
    apply log_le_log (by positivity)
    exact_mod_cast two_pow_le_mul_lcmUpto n
  rwa [Real.log_pow, Real.log_mul (by positivity) (by simp), ← psi_eq_log_lcmUpto,
   ← sub_le_iff_le_add'] at this

@[simp]
theorem theta_zero : theta 0 = 0 := theta_eq_zero_of_lt_two (by norm_num)

@[simp]
theorem theta_one : theta 1 = 0 := theta_eq_zero_of_lt_two (by norm_num)

/-- The Chebyshev lower bound for $\theta$. -/
theorem theta_ge (n : ℕ) : n * log 2 - log (n + 1) - 2 * √n * log n ≤ theta n:= by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have : psi n - theta n ≤ 2 * √n * log n := by
    grw [← abs_psi_sub_theta_le_sqrt_mul_log]
    · exact le_abs_self (ψ n - θ n)
    simp; omega
  linarith [psi_ge n]

theorem theta_eq_sum_log (n : ℕ) : theta n = ∑ p ∈ primesLE n, log p := by
  rw [theta_eq_sum_Icc, floor_natCast, primesLE_eq_filter_Icc_zero]

theorem theta_le_primeCounting_mul_log (n : ℕ) : theta n ≤ (primeCounting n) * log n := calc
  _ ≤ ∑ p ∈ primesLE n, log n := by
    rw [theta_eq_sum_log n]
    apply sum_le_sum; intro p hp; simp only [mem_filter, mem_range, Order.lt_add_one_iff] at hp
    exact log_le_log (mod_cast hp.2.pos) (mod_cast hp.1)
  _ = _ := by
    simp [card_primesLE]

end Chebyshev
