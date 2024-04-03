/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Complex.ExponentialBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds

open Sieve
open scoped Nat ArithmeticFunction BigOperators

noncomputable section
namespace BrunTitchmarsh

/- Sifting primes ≤ z from the interval [x, x+y] -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z): SelbergSieve := {
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp[if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp[hp.ne_zero]
    apply inv_lt_one
    norm_cast
    exact hp.one_lt
  level := z
  one_le_level := hz
}

/- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (Nat.Prime) |>.card

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    (primeInterSieve x y z hz).siftedSum =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply Sieve.siftedSum_eq
  exact fun _ _ => rfl
  exact hz
  rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (Nat.Prime) ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
    (Finset.Icc 1 (Nat.floor z)) := by
  intro p
  simp
  intro hx hxy hp
  by_cases hpz : p ≤ z
  · right
    rw[Nat.le_floor_iff (by linarith)]
    have := hp.ne_zero
    exact ⟨by omega, hpz⟩
  · left
    refine ⟨⟨hx, hxy⟩, ?_⟩
    intro q hq hqz
    rw[hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤ (primeInterSieve x y z hz).siftedSum + z := by
  classical
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪ (Finset.Icc 1 (Nat.floor z))).card
  · rw[primesBetween]
    norm_cast
    apply Finset.card_le_card
    apply primesBetween_subset _ _ _ hx
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card
    + ↑(Finset.Icc 1 (Nat.floor z)).card
  · norm_cast
    apply Finset.card_union_le
  rw[siftedSum_eq_card]
  gcongr
  rw[Nat.card_Icc]
  simp
  apply Nat.floor_le
  linarith

section Remainder

theorem Ioc_filter_dvd_eq (d a b: ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x => d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x => x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.ceil_le, Finset.mem_image,
    Nat.le_floor_iff (show 0 ≤ x+y by linarith)]
  constructor
  · intro hn
    use  n/d
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_lt_div_of_lt_of_dvd hd han
    · exact Nat.div_le_div_right (Nat.le_floor hnb)
    · exact Nat.div_mul_cancel hd
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (Nat.div_lt_iff_lt_mul ?_).mp ha
      omega
    · exact Nat.mul_le_of_le_div d r b ha'
    · exact Nat.dvd_mul_left d r

theorem BrunTitchmarsh.card_Ioc_filter_dvd (d a b: ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x => d ∣ x) (Finset.Ioc a b)).card = b / d - a / d  := by
  rw [Ioc_filter_dvd_eq _ _ _ hd]
  rw [Finset.card_image_of_injective _ <| mul_left_injective₀ hd]
  simp

theorem multSum_eq (d : ℕ) (hd : d ≠ 0):
    (primeInterSieve x y z hz).multSum d = ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold Sieve.multSum
  rw[primeInterSieve]
  simp
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [←Nat.Icc_succ_left]
    congr
    rw [←Nat.succ_sub]; rfl
    simp [hx]
  · rw[BrunTitchmarsh.card_Ioc_filter_dvd _ _ _ hd]

theorem rem_eq (d : ℕ) (hd : d ≠ 0) : (primeInterSieve x y z hz).rem d = ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold Sieve.rem
  rw[multSum_eq x y z hx hz d hd]
  simp [primeInterSieve, if_neg hd]

theorem Nat.ceil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · norm_cast
    exact Nat.ceil_le_floor_add_one x
  gcongr
  apply Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  simp
  rw[abs_le]
  constructor
  · simp only [neg_le_sub_iff_le_add]
    linarith [Nat.lt_floor_add_one x]
  · simp only [tsub_le_iff_right]
    linarith [Nat.floor_le hx]

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  simp
  rw[abs_le]
  constructor
  · simp only [neg_le_sub_iff_le_add]
    linarith [Nat.le_ceil x]
  · simp only [tsub_le_iff_right]
    rw[add_comm]
    exact Nat.ceil_le_self_add_one x hx

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw[←Nat.floor_div_eq_div (α:=ℝ)]
  apply floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) : ∃ C, |C| ≤ 2 ∧  ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
  rw[hC₁, hC₂]
  use  C₁ + C₂/d
  refine ⟨?_, by ring⟩
  have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add C₁ (C₂ / ↑d)
  have : |C₂/d| ≤ |C₂| := by
    rw[abs_div]
    apply div_le_self
    · exact abs_nonneg C₂
    · simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
  linarith

theorem abs_rem_le {d : ℕ} (hd : d ≠ 0) : |(primeInterSieve x y z hz).rem d| ≤ 5 := by
  rw[rem_eq _ _ _ hx hz _ hd]

  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) = ( ↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw[Nat.le_floor_iff]
    rw[←add_le_add_iff_right 1]
    norm_cast
    rw [Nat.sub_add_cancel (by simp [hx])]
    linarith [Nat.ceil_le_self_add_one x (le_of_lt hx)]
    linarith

  rw[hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw[hC₁, hC₂, Nat.cast_sub, hC₃]
  ring_nf
  have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| ≤ |(↑d)⁻¹ - (↑d)⁻¹*C₃| + |C₁ - C₂| := by
    apply (abs_add _ _)
  have : |(↑d)⁻¹ - (↑d)⁻¹*C₃| ≤ |(↑d)⁻¹| + |(↑d)⁻¹*C₃| := abs_sub _ _
  have : |C₁ - C₂| ≤ |C₁| + |C₂| := abs_sub _ _
  have : |(d:ℝ)⁻¹| ≤ 1 := by
    rw[abs_inv]
    simp only [Nat.abs_cast]
    apply Nat.cast_inv_le_one
  have : |(↑d)⁻¹*C₃| ≤ |C₃| := by
    rw[inv_mul_eq_div, abs_div]
    apply div_le_self
    · exact abs_nonneg _
    · simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
  linarith
  · simp [hx]

end Remainder

theorem boudingSum_ge : (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    apply Nat.le_floor
    exact hp
    exact hpp

theorem primeSieve_rem_sum_le :
    ∑ d in (primeInterSieve x y z hz).prodPrimes.divisors, (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d * |(primeInterSieve x y z hz).rem d| else 0)
      ≤ 5 * z * (1+Real.log z)^3 := by
  apply rem_sum_le_of_const (primeInterSieve x y z hz) 5 ?_
  intro d hd
  apply abs_rem_le <;> linarith

theorem siftedSum_le (hz : 1 < z) :
    (primeInterSieve x y z (le_of_lt hz)).siftedSum ≤ 2 * y / Real.log z + 5 * z * (1+Real.log z)^3  := by
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1+Real.log z)^3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · apply boudingSum_ge
  · apply primeSieve_rem_sum_le x y z hx hy

theorem primesBetween_le (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := by
  have : z ≤ z * (1+Real.log z)^3 := by
    apply le_mul_of_one_le_right
    · linarith
    apply one_le_pow_of_one_le _ _
    linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le _ _ _ hx hy hz, primesBetween_le_siftedSum_add x y z hx (le_of_lt hz)]

theorem aux0 (z : ℝ) (hz : 0 < z) : 1 + 3 * Real.log z ≤ 3 * z := by
  linarith [Real.log_le_sub_one_of_pos hz]

theorem one_add_mul_log_le_rpow {x r : ℝ} (hx : 0 < x) (hr : 0 < r) : r * Real.log x ≤ x ^ r - 1 := by
  simpa [Real.log_rpow, hx, hr] using Real.log_le_sub_one_of_pos (show 0 < x ^ r by positivity)

theorem aux1 {x : ℝ} (hx : 0 < x) : 1 + 1/2 * Real.log x ≤ 4 * x ^ (1/8 : ℝ) := by
  have := one_add_mul_log_le_rpow hx (show 0 < 1/8 by norm_num)
  linarith
#eval 4^4
theorem help2 {x : ℝ} (hx : 1 < x) :
    (1 + 1/2 * Real.log x)^4 ≤ 256 * x ^ (1/2 : ℝ) := by
  convert_to (1 + 1/2 * Real.log x)^4 ≤ (4 * x ^ (1/8 : ℝ))^4
  · ring_nf
    rw [← Real.rpow_mul_natCast (by linarith)]
    norm_num
  gcongr
  · linarith [Real.log_pos hx]
  exact aux1 (by linarith only [hx])

theorem help1 {x : ℝ} (hx : 1 < x) :
    ((1 + 1/2 * Real.log x)^3 * Real.log x) ≤ 512 * x ^ (1/2 : ℝ) := by
  calc _ ≤ 2 * (1 + 1/2 * Real.log x)^4 := ?_
       _ ≤ _ := by linarith [help2 hx]
  have : 0 ≤ 1 + 1/2 * Real.log x := by linarith [Real.log_pos hx]
  rw [pow_succ _ 3, mul_comm, ← mul_assoc]
  gcongr
  linarith


theorem help0 {x : ℝ} (hx : 1 < x) :
    x ^ (1/2 : ℝ) * ((1 + 1/2 * Real.log x)^3 * Real.log x) ≤ 512 * x := by
  have : 512 * x = x ^ (1/2 : ℝ) * (512 * x ^ (1/2:ℝ)) := by
    ring_nf
    rw [← Real.rpow_mul_natCast (by linarith)]
    norm_num
  rw [this]
  have := Real.log_pos hx
  gcongr _ * ?_
  apply help1 hx

theorem error_le {x : ℝ} (hx : 1 < x) :
    x ^ (1/2 : ℝ) * (1 + 1/2 * Real.log x)^3 ≤ 512 * (x / Real.log x) := by
  rw [← mul_le_mul_iff_of_pos_right (Real.log_pos hx)]
  convert help0 hx using 1
  · ring
  · field_simp [(Real.log_pos hx).ne.symm]

theorem primesBetween_one (n : ℕ) : primesBetween 1 n = ((Finset.range (n+1)).filter Nat.Prime).card := by
  rw [primesBetween]
  congr 1
  ext p
  simp only [Nat.ceil_one, Nat.floor_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    and_congr_left_iff]
  intro hp
  refine ⟨?_, ?_⟩
  · exact fun h => by omega
  · refine fun h => ⟨by have := hp.pos; omega, by omega⟩

theorem primesBetween_mono_right (a b c : ℝ) (hbc : b ≤ c) : primesBetween a b ≤ primesBetween a c := by
  dsimp only [primesBetween]
  apply Finset.card_le_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, and_imp]
  intro ha hb hp
  refine ⟨⟨ha, hb.trans (Nat.floor_mono hbc)⟩, hp⟩


#eval 6 * 512 +4
theorem aux4 (x : ℝ) (hx : 1 < x) : primesBetween 1 (x+1) ≤ 3076 * (x / Real.log x) := by
  have h : primesBetween 1 (1 + x) ≤
      2 * (x / Real.log (x^(1/2:ℝ))) + 6 * (x ^ (1 / 2 : ℝ) * (1 + Real.log (x ^ (1 / 2 : ℝ))) ^ 3) := by
    convert (primesBetween_le 1 x (x ^ (1/2 : ℝ)) (by norm_num) (by norm_cast; linarith)
      (Real.one_lt_rpow (by norm_cast) (by norm_num))) using 1
    ring
  norm_num at h
  have := error_le hx
  have hdiv : x / Real.log (x ^ (1/2:ℝ)) = 2 * (x / Real.log x) := by
    rw [Real.log_rpow (by linarith) ]
    ring
  have : Real.log (x ^ (1 / 2 : ℝ)) = 1 / 2 * Real.log x := by
    rw [Real.log_rpow (by linarith)]
  rw [hdiv, this]  at h
  rw [add_comm x 1]
  linarith


theorem card_range_filter_prime_le_aux (n : ℕ) (hn : 1 < n) :
    ((Finset.range n).filter Nat.Prime).card ≤ 3076 * (n / Real.log n) := calc
  _ ≤ (((Finset.range (n+1)).filter Nat.Prime).card : ℝ) := by
    norm_cast; apply Finset.card_le_card; apply Finset.filter_subset_filter; simp
  _ = primesBetween 1 n := by norm_cast; exact (primesBetween_one n).symm
  _ ≤ primesBetween 1 (n+1) := by
    norm_cast;
    apply primesBetween_mono_right
    simp
  _ ≤ 3076 * (n / Real.log n) := by
    convert aux4 (n) _
    norm_cast

theorem card_range_filter_prime_le (n : ℕ) :
    ((Finset.range n).filter Nat.Prime).card ≤ 3076 * (n / Real.log n) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1, show Finset.filter Nat.Prime {0} = ∅ by rfl]
  apply card_range_filter_prime_le_aux n (by omega)

theorem card_range_filter_prime_isBigO : (fun N ↦ ((Finset.range N).filter Nat.Prime).card : ℕ → ℝ) =O[Filter.atTop] (fun N ↦ N / Real.log N) := by
  apply Asymptotics.isBigO_of_le' (c:=3076)
  simp only [IsROrC.norm_natCast, norm_div, Real.norm_eq_abs]
  intro N
  by_cases hN : N = 0
  · simp [hN]
  convert card_range_filter_prime_le N using 3
  simp only [abs_eq_self]
  apply Real.log_nonneg
  norm_cast; omega

theorem prime_or_pow (N n : ℕ) (hnN : n < N) (hnprime : IsPrimePow n) :
    Nat.Prime n ∨ (∃ (m : ℕ), m < Real.sqrt N ∧ ∃ k ≤ Nat.log 2 N, n = m ^ k) := by
  obtain ⟨p, hpn, k, hkn, hp, hk_pos, hpkn⟩ := (isPrimePow_nat_iff_bounded n).to_eq ▸ hnprime
  by_cases hk : k = 1
  · left
    rw [← hpkn, hk, pow_one]
    exact hp
  right
  refine ⟨p, ?_, k, ?_, ?_⟩
  · rw [Real.lt_sqrt]
    norm_cast
    · calc
        p^2 ≤ p^k := by
          gcongr; exact hp.one_le;omega
      _ = n := hpkn
      _ < N := hnN
    · positivity
  · calc
      _ ≤ Nat.log p n := by
        apply Nat.le_log_of_pow_le hp.one_lt hpkn.le
      _ ≤ Nat.log 2 n := by
        apply Nat.log_anti_left (by norm_num) hp.two_le
      _ ≤ Nat.log 2 N := by
        apply Nat.log_mono_right hnN.le
  · norm_cast
    exact hpkn.symm

example (a : ℝ) (n : ℕ) : a ^ n = a ^ (n : ℝ) := by
  exact (Real.rpow_nat_cast a n).symm

theorem Nat.log_eq_floor_logb (b n : ℕ) (hb : 1 < b) : Nat.log b n = Nat.floor (Real.logb b n) := by
  by_cases hn : n = 0
  · simp [hn]
  have hlogb_nonneg : 0 ≤ Real.logb b n := by
    apply Real.logb_nonneg
    · norm_cast
    · norm_cast; exact Nat.one_le_iff_ne_zero.mpr hn
  apply le_antisymm
  · rw [Nat.le_floor_iff, Real.le_logb_iff_rpow_le]
    norm_cast
    apply Nat.pow_log_le_self
    · exact hn
    · norm_cast
    · norm_cast; exact Nat.zero_lt_of_ne_zero hn
    · exact hlogb_nonneg
  · apply Nat.le_log_of_pow_le hb
    exact_mod_cast calc
      (b:ℝ) ^ ⌊Real.logb ↑b ↑n⌋₊ ≤ (b : ℝ)^ (Real.logb b n) := by
        rw [← Real.rpow_nat_cast]
        gcongr
        · norm_cast; omega
        apply Nat.floor_le hlogb_nonneg
      _ = n := by
        rw [Real.rpow_logb] <;> norm_cast <;> omega

theorem range_filter_isPrimePow_subset_union (N : ℕ) :
  ((Finset.range N).filter IsPrimePow) ⊆ (Finset.range N).filter Nat.Prime ∪
    ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)
    := by
  intro n
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
    Finset.mem_product, Prod.exists, and_imp]
  intro hnN hnprime
  rcases prime_or_pow N n hnN hnprime with hp | ⟨m, hm, k, hk, h⟩
  · left; exact ⟨hnN, hp⟩
  · right
    refine ⟨m, k, ?_⟩
    by_cases hm : m = 0
    · rw [hm, zero_pow] at h
      exact False.elim (hnprime.ne_zero h)
      rintro rfl
      simp only [pow_zero] at h
      exact False.elim (hnprime.ne_one h)
    rw [Nat.lt_ceil, Nat.lt_succ_iff]
    have : 1 ≤ m := by omega
    aesop

-- example (a b c : ℝ) (hc : 0 < c) (h : a / c ≤ b) : a ≤ b * c := by exact
--   (mul_inv_le_iff' hc).mp h

theorem IsBigO.nat_Top_of_atTop (f g : ℕ → ℝ) (h : f =O[Filter.atTop] g) (h0 : ∀ n, g n = 0 → f n = 0) :
    f =O[⊤] g := by
  simp only [Asymptotics.isBigO_top, Real.norm_eq_abs]
  rw [Asymptotics.isBigO_atTop_iff_eventually_exists] at h
  simp only [ge_iff_le, Real.norm_eq_abs, Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  specialize hN N le_rfl
  obtain ⟨c, hc⟩ := hN
  let C := Finset.max' (insert c ((Finset.range N).image (fun n ↦ |f n| * |g n|⁻¹))) (by simp)
  refine ⟨C, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · calc |f n| ≤ c * |g n| := hc n hn
      _ ≤ C * |g n| := by
        gcongr
        apply Finset.le_max'
        simp
  · by_cases hg : g n = 0
    · simp [hg, h0]
    rw [← mul_inv_le_iff']
    apply Finset.le_max'
    simp
    exact .inr ⟨n, by omega, rfl⟩
    · simp [hg]

theorem pows_small_primes_le (N : ℕ) :
  (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card
    ≤ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2):= calc
  _ ≤ (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).card : ℝ) := by
    norm_cast
    exact Finset.card_image_le
  _ ≤ _ := by
    simp only [Finset.card_product, Nat.card_Ico, Finset.card_range, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    by_cases hN : N = 0
    · simp [hN]
    have : 1 ≤ Nat.ceil (Real.sqrt N) := by
      simp only [Nat.one_le_ceil_iff, Real.sqrt_pos, Nat.cast_pos]
      omega
    gcongr ?_ * ?_
    · rw [← Real.sqrt_eq_rpow, Nat.cast_sub this, Nat.cast_one]
      have := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt N by positivity)
      linarith
    rw [Nat.log_eq_floor_logb _ _ (by norm_num), Real.log_div_log, Nat.cast_two]
    have hlogb_nonneg : 0 ≤ Real.logb 2 N := by
      apply Real.logb_nonneg
      · norm_cast
      · norm_cast; omega
    linarith [Nat.floor_le hlogb_nonneg]

open Filter Asymptotics

theorem one_isBigO_log : (fun (_:ℝ) ↦ (1:ℝ)) =O[atTop] Real.log := by
  refine (isBigO_const_left_iff_pos_le_norm ?hc).mpr ?_
  · simp
  use 1
  simp
  use (Real.exp 1)
  intro b hb
  have : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le]
    exact hb
    · have := Real.exp_one_gt_d9
      norm_num at this
      linarith
  rw [abs_of_nonneg (by linarith)]
  exact this

theorem one_add_log_div_log_two_isBigO :
    (fun N ↦ (1 + Real.log N / Real.log 2)) =O[atTop] (fun N ↦ Real.log N) := by
  refine IsBigO.add ?h₁ ?h₂
  · convert one_isBigO_log
  simp_rw [div_eq_inv_mul]
  apply IsBigO.const_mul_left
  apply isBigO_refl
example (N : ℕ) : ∀ᶠ (n:ℕ) in atTop, n ≥ N := by
  apply Filter.eventually_ge_atTop


theorem pow_half_mul_one_add_log_div_isBigO :
    (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[Filter.atTop]
      (fun N ↦ N / Real.log N) := calc
  (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[atTop] (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * Real.log N) := by
    apply IsBigO.mul
    · apply isBigO_refl
    apply one_add_log_div_log_two_isBigO
  _ =O[atTop] (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * N ^ (1/4 : ℝ)) := by
    apply IsBigO.mul (isBigO_refl ..)
    apply (isLittleO_log_rpow_atTop (show 0 < (1/4 : ℝ) by norm_num) ..).isBigO
  _ =ᶠ[atTop] (fun N ↦ (N : ℝ) * (N ^ (1/4 : ℝ))⁻¹) := by
    filter_upwards [Filter.eventually_gt_atTop 0]
    intro N hN
    trans (N ^ (1 : ℝ) * (N ^ (1/4 : ℝ))⁻¹)
    · rw [← Real.rpow_add hN, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
      norm_num
    · rw [← Nat.cast_one, Real.rpow_nat_cast, pow_one]
  _ =O[atTop] (fun N ↦ (N : ℝ) * (Real.log N)⁻¹) := by
    apply IsBigO.mul (isBigO_refl ..)
    apply IsBigO.inv_rev
    apply (isLittleO_log_rpow_atTop (show 0 < (1/4 : ℝ) by norm_num) ..).isBigO
    · filter_upwards [Filter.eventually_gt_atTop 1]
      intro N hN hcontra
      linarith [Real.log_pos hN]
  _ = (fun N ↦ (N : ℝ)/(Real.log N)) := by
    simp_rw [div_eq_mul_inv]


theorem card_pows_aux :  (fun N ↦(((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℕ → ℝ) =O[atTop] fun N ↦ N / Real.log N := by
  apply IsBigO.trans ?_ pow_half_mul_one_add_log_div_isBigO.natCast
  apply isBigO_of_le
  intro N
  simp only [IsROrC.norm_natCast, one_div, norm_mul, Real.norm_eq_abs]
  rw [Real.abs_rpow_of_nonneg (by positivity), Nat.abs_cast, abs_of_nonneg]
  convert pows_small_primes_le N using 3
  norm_num
  by_cases hN : N = 0
  · simp [hN]
  rw [Real.log_div_log]
  linarith [Real.logb_nonneg (show 1 < (2:ℝ) by norm_num) (show (1 : ℝ) ≤ N by norm_num; omega)]

theorem card_isPrimePow_isBigO :
  (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop] (fun N ↦ N / Real.log N) := calc
  (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop] (fun N ↦ (((Finset.range N).filter Nat.Prime ∪
    ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card:ℝ)) := by
    apply isBigO_of_le
    simp only [IsROrC.norm_natCast, Nat.cast_le]
    intro N
    apply Finset.card_le_card
    apply range_filter_isPrimePow_subset_union
  _ =O[atTop] fun N ↦ (((Finset.range N).filter Nat.Prime).card + (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℝ):= by
    apply isBigO_of_le
    simp only [IsROrC.norm_natCast, Real.norm_eq_abs]
    intro N
    rw [abs_of_nonneg (by positivity)]
    norm_cast
    apply Finset.card_union_le
  _ =O[atTop] fun N ↦ N / Real.log N := by
    apply IsBigO.add
    · exact card_range_filter_prime_isBigO
    apply card_pows_aux

theorem card_range_filter_isPrimePow_le : ∃ C, ∀ N, ((Finset.range N).filter IsPrimePow).card ≤ C * (N / Real.log N) := by
  convert_to (fun N ↦ ((Finset.range N).filter IsPrimePow).card : ℕ → ℝ) =O[⊤] (fun N ↦ (N / Real.log N))
  · simp
    peel with C N
    by_cases hN : N = 0
    · simp [hN]
    rw [abs_of_nonneg]
    apply Real.log_nonneg
    norm_cast; omega
  apply IsBigO.nat_Top_of_atTop _ _ card_isPrimePow_isBigO
  simp
  refine ⟨rfl, ?_⟩
  intro a ha
  exfalso
  linarith [show 0 ≤ (a : ℝ) by positivity]

#print axioms card_isPrimePow_isBigO
