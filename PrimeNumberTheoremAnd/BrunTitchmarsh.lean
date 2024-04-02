/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Complex.ExponentialBounds
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
  apply PrimeUpperBound.siftedSum_eq
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

#print axioms primesBetween_le
