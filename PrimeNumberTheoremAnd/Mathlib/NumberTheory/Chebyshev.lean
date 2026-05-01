import Mathlib.NumberTheory.Chebyshev

namespace Finset


open Classical _root_.Nat in
/-- An analogue of `Nat.factorization_lcm` for `Finset.lcm`. -/
theorem factorization_lcm {α : Type _} {f : α → ℕ} {s : Finset α}
    (hf : ∀ k ∈ s, f k ≠ 0) (p : ℕ) :
    (s.lcm f).factorization p = s.sup fun a => (f a).factorization p := by
  induction s using Finset.induction with
  | empty =>
    simp [lcm, fold_empty, factorization_one, Finsupp.coe_zero, sup_empty]
  | insert _ _ _ _ =>
    simp_all +decide only [lcm_insert, sup_insert]
    erw [ Nat.factorization_lcm ] <;> simp_all

end Finset

namespace Nat

theorem log_eq_log_div_log (a b : ℕ) : a.log b = ⌊ Real.log b / Real.log a ⌋₊ := by
  rcases (show a=0 ∨ a=1 ∨ 1<a by omega) with rfl | rfl | ha
  · simp
  · simp
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  symm; rw [floor_eq_iff (by positivity)]
  have : 0 < Real.log a := Real.log_pos (by norm_cast)
  constructor
  · rw [le_div_iff₀ this, ←Real.log_pow ]
    exact Real.log_le_log (by positivity) (mod_cast pow_log_le_self _ (by aesop))
  rw [div_lt_iff₀ this, ← Real.log_rpow ( by norm_cast; linarith) ]
  exact Real.log_lt_log ( mod_cast pos_of_ne_zero (by aesop) )
    (mod_cast lt_pow_succ_log_self ( by aesop ) _)

end Nat

namespace Chebyshev

open Nat hiding log
open Real Finset
open ArithmeticFunction hiding log id


/-- Least common multiple of $\{1, \dots, n\}$. -/
abbrev lcm_upto (n : ℕ) : ℕ := (Icc 1 n).lcm id

theorem lcm_upto_ne (n : ℕ) : lcm_upto n ≠ 0 := by simp

theorem lcm_upto_pos (n : ℕ) : 0 < lcm_upto n := by grind [lcm_upto_ne n]

/-- The primes up to $n$. -/
abbrev primes_le (n : ℕ) : Finset ℕ := filter Nat.Prime (range (n+1))

lemma primes_le_eq (n : ℕ) : primes_le n = filter Nat.Prime (Icc 1 n) := by
  ext p
  simp only [mem_filter, mem_range, Order.lt_add_one_iff, mem_Icc,
    and_congr_left_iff, iff_and_self]
  intro hp; grind [hp.one_lt]

lemma primes_le_eq' (n : ℕ) : primes_le n = filter Nat.Prime (Icc 2 n) := by
  ext p
  simp only [mem_filter, mem_range, Order.lt_add_one_iff, mem_Icc,
    and_congr_left_iff, iff_and_self]
  intro hp; grind [hp.one_lt]

theorem factorization_lcm_upto (n : ℕ) {p : ℕ} (hp : p.Prime) : (lcm_upto n).factorization p = p.log n := calc
  _ = (Icc 1 n).sup (fun k => k.factorization p) := Finset.factorization_lcm (fun k hk => by grind) p
  _ = _ := by
    have := hp.one_lt
    refine le_antisymm ?_ ?_ <;> norm_num at *;
    · intro m _ _
      exact le_log_of_pow_le this (by linarith [le_of_dvd (by linarith) (ordProj_dvd m p)])
    rcases le_or_gt p n with _ | h
    · have := pow_log_le_self p (x := n) (by linarith)
      grw [←le_sup (b := p ^ Nat.log p n) (by grind), factorization_pow]
      simp [hp]
    simp [log_of_lt h]

theorem lcm_eq_prod (n : ℕ) : lcm_upto n = ∏ p ∈ primes_le n, p ^ ((lcm_upto n).factorization p) := by
  symm; convert factorization_prod_pow_eq_self ( lcm_upto_ne n )
  rw [ Finsupp.prod_of_support_subset ] <;> norm_num [ subset_iff ]
  exact fun p pp dp => ⟨ pp.dvd_factorial.mp ( dvd_trans dp <| lcm_dvd fun x hx => dvd_factorial ( mem_Icc.mp hx |>.1 ) ( mem_Icc.mp hx |>.2 ) ), pp ⟩

theorem lcm_eq_prod' (n : ℕ) : lcm_upto n = ∏ p ∈ primes_le n, p ^ (p.log n) := by
  convert lcm_eq_prod n using 3 with p hp
  simp only [mem_filter, mem_range, Order.lt_add_one_iff] at hp
  rw [ factorization_lcm_upto n hp.2 ]

theorem lcm_eq_prod'' (n : ℕ) : lcm_upto n = ∏ p ∈ primes_le n, p ^ ⌊log n / log p⌋₊ := by
  convert lcm_eq_prod' n using 3
  rw [ log_eq_log_div_log ]

theorem psi_eq_sum_mul_log_prime (n : ℕ) : psi n = ∑ p ∈ primes_le n, p.log n * log p := calc
  _ = ∑ m ∈ Icc 1 n, vonMangoldt m := by unfold psi; aesop
  _ = ∑ m ∈ Finset.biUnion (filter Nat.Prime (Icc 1 n))
    (fun p => image (fun k => p ^ k) (Icc 1 (p.log n))), vonMangoldt m := by
    symm; apply sum_subset
    · intro q;
      simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, forall_exists_index,
      and_imp]
      intro p _ _ _ m _ _ rfl
      refine ⟨ by grind, pow_le_of_le_log ( by linarith ) ( by linarith ) ⟩
    intro x hx
    simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, not_exists, not_and, and_imp,
      vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
    intro this; contrapose! this; obtain ⟨ p, k, hp, hk, rfl ⟩ := this
    simp at hx
    refine ⟨ p, ⟨ by linarith [hp.one_lt], ?_, hp, ⟨ k, ⟨ by linarith, ?_, rfl ⟩ ⟩ ⟩ ⟩
    · linarith [ le_of_dvd ( by linarith ) ( dvd_pow_self p hk.ne' ) ]
    exact le_log_of_pow_le hp.one_lt ( by linarith )
  _ = ∑ p ∈ Icc 1 n with Nat.Prime p, ∑ q ∈ image (fun k ↦ p ^ k) (Icc 1 (p.log n)), Λ q := by
    convert sum_biUnion ?_
    intros p hp q hq hpq; simp_all +decide only [ne_eq, coe_filter, mem_Icc,
                  Set.mem_setOf_eq, disjoint_left, mem_image, not_exists, not_and, and_imp,
                  forall_exists_index]
    intro a x _ _ rfl y _ _ hy₃
    have := Nat.Prime.dvd_of_dvd_pow hp.2 ( hy₃.symm ▸ dvd_pow_self _ ( by linarith ) )
    simp_all +decide [ prime_dvd_prime_iff_eq ]
  _ = ∑ p ∈ primes_le n, ∑ k ∈ Icc 1 (p.log n), vonMangoldt (p ^ k) := by
    apply sum_congr (primes_le_eq n).symm
    intro p hp
    rw [ sum_image ]
    intros a _ b _ hab
    exact Nat.pow_right_injective ( Nat.Prime.one_lt ( by aesop ) ) hab
  _ = ∑ p ∈ primes_le n, ∑ k ∈ Icc 1 (p.log n), log p := by
    apply sum_congr rfl; intro p hp
    apply sum_congr rfl; intro k hk
    simp only [primes_le, mem_filter, mem_range, Order.lt_add_one_iff, mem_Icc] at hp hk
    rw [vonMangoldt_apply_pow (by linarith), vonMangoldt_apply_prime hp.2]
  _ = _ := by aesop

theorem log_lcm_upto_eq_psi (n : ℕ) : psi n = log (lcm_upto n) := by
  rw [ lcm_eq_prod' ];
  rw [ Nat.cast_prod, log_prod ] <;> norm_num;
  · rw [ psi_eq_sum_mul_log_prime ];
  · aesop

theorem choose_dvd_lcm_upto {n k : ℕ} (hkn : k ≤ n) : choose n k ∣ lcm_upto n := by
  rw [←factorization_prime_le_iff_dvd (choose_ne_zero hkn) _]
  · intro p hp;
    rw [factorization_lcm_upto n hp]
    exact factorization_choose_le_log
  linarith [lcm_upto_pos n]

theorem two_pow_le_lcm_upto_mul (n : ℕ) : 2 ^ n ≤ (n+1) * lcm_upto n := calc
  _ ≤ ∑ k ∈ Finset.range (n+1), lcm_upto n := by
    rw [←sum_range_choose]
    apply sum_le_sum; intro k hk; simp only [mem_range, Order.lt_add_one_iff] at hk
    exact Nat.le_of_dvd (lcm_upto_pos n) (choose_dvd_lcm_upto hk)
  _ ≤ _ := by simp

/-- The Chebyshev lower bound for $\psi$. -/
theorem psi_ge (n : ℕ) : psi n ≥ n * log 2 - log (n+1) := by
  have : log (2 ^ n) ≤ log ((n+1) * lcm_upto n) := by
    apply log_le_log (by positivity)
    have : (2:ℝ)^n = (2^n:ℕ) := by norm_num
    rw [this]; grw [two_pow_le_lcm_upto_mul n]; grind
  rw [Real.log_pow, Real.log_mul (by positivity) (by simp), ←log_lcm_upto_eq_psi] at this
  linarith

theorem theta_ge (n : ℕ) : theta n ≥ n * log 2 - log (n+1) - 2 * √n * log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [theta]
  have : psi n - theta n ≤ 2 * √n * log n := by
    grw [← abs_psi_sub_theta_le_sqrt_mul_log]
    · exact le_abs_self (ψ n - θ n)
    norm_num; omega
  linarith [psi_ge n]

@[simp]
theorem theta_zero : theta 0 = 0 := theta_eq_zero_of_lt_two (by norm_num)

@[simp]
theorem theta_one : theta 1 = 0 := theta_eq_zero_of_lt_two (by norm_num)

theorem theta_le_primeCounting_mul_log (n : ℕ) : theta n ≤ (primeCounting n) * log n := calc
  _ ≤ ∑ p ∈ Icc 0 n with Nat.Prime p, log n := by
    rw [theta_eq_sum_Icc, floor_natCast]
    apply sum_le_sum; intro p hp; simp only [mem_Icc, mem_filter] at hp
    have := hp.2.one_lt
    apply log_le_log  (by norm_num; linarith) (by norm_num; tauto)
  _ = _ := by
    simp only [sum_const, nsmul_eq_mul, mul_eq_mul_right_iff, Nat.cast_inj, log_eq_zero,
      cast_eq_zero, cast_eq_one, primeCounting, primeCounting', count_eq_card_filter_range]; left
    congr; aesop

end Chebyshev
