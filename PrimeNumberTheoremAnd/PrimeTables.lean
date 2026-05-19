import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Prime.Defs
import PrimeCert
import PrimeNumberTheoremAnd.Tactic.Simprocs

set_option linter.style.nativeDecide false

/-!
# Primality certificates and prime-counting tables

This file collects based primality proofs and prime-counting bounds
that are expensive to check and may rely on `native_decide` for performance. By isolating them in their own file, the cost is paid
only once (when this file is first built), rather than every time a downstream file
is edited.
-/

/-! ## Primality certificates for large numbers -/

theorem prime_211 : Nat.Prime 211 := PrimeCert.prime_211

theorem prime_313 : Nat.Prime 313 := PrimeCert.prime_313

theorem prime_3999999999999999791 : Nat.Prime 3999999999999999791 := prime_cert%
  [small {3; 5; 23; 211},
   pock3 (239851, 3, 1, 0, 2 * 3 ^ 2 * 5 ^ 2),
   pock3 (399999999999999979, 2, 1, 0, 2 * 3 ^ 3 * 23 * 211 * 239851),
   pock3 (3999999999999999791, 11, 1, 0, 2 * 5 * 399999999999999979)]

theorem prime_3999999999999999691 : Nat.Prime 3999999999999999691 := prime_cert%
  [small {3; 5; 11; 29; 41; 389},
   pock3 (18913, 7, 1, 3, 2 ^ 5 * 3),
   pock3 (37379684141669, 2, 1, 0, 2 ^ 2 * 11 * 389 * 18913),
   pock3 (3999999999999999691, 3, 1, 0, 2 * 3 ^ 2 * 5 * 29 * 41 * 37379684141669)]

/-! ## Prime-counting bounds

`Nat.count Nat.Prime m` counts the number of primes strictly below `m`.
These lemmas witness that the n-th prime (1-indexed) is at least `m`, via
`Nat.count Nat.Prime m ≤ n - 1`.
-/

theorem count_prime_3_le_1 : Nat.count Nat.Prime 3 ≤ 1 := by simp only [count_ofNat]; norm_num
theorem count_prime_5_le_2 : Nat.count Nat.Prime 5 ≤ 2 := by simp only [count_ofNat]; norm_num
theorem count_prime_7_le_3 : Nat.count Nat.Prime 7 ≤ 3 := by simp only [count_ofNat]; norm_num
theorem count_prime_11_le_4 : Nat.count Nat.Prime 11 ≤ 4 := by simp only [count_ofNat]; norm_num
theorem count_prime_13_le_5 : Nat.count Nat.Prime 13 ≤ 5 := by simp only [count_ofNat]; norm_num
theorem count_prime_17_le_6 : Nat.count Nat.Prime 17 ≤ 6 := by simp only [count_ofNat]; norm_num
theorem count_prime_19_le_7 : Nat.count Nat.Prime 19 ≤ 7 := by simp only [count_ofNat]; norm_num
theorem count_prime_23_le_8 : Nat.count Nat.Prime 23 ≤ 8 := by simp only [count_ofNat]; norm_num
theorem count_prime_29_le_9 : Nat.count Nat.Prime 29 ≤ 9 := by simp only [count_ofNat]; norm_num
theorem count_prime_31_le_10 : Nat.count Nat.Prime 31 ≤ 10 := by simp only [count_ofNat]; norm_num
theorem count_prime_37_le_11 : Nat.count Nat.Prime 37 ≤ 11 := by simp only [count_ofNat]; norm_num
theorem count_prime_41_le_12 : Nat.count Nat.Prime 41 ≤ 12 := by simp only [count_ofNat]; norm_num
theorem count_prime_43_le_13 : Nat.count Nat.Prime 43 ≤ 13 := by simp only [count_ofNat]; norm_num
theorem count_prime_47_le_14 : Nat.count Nat.Prime 47 ≤ 14 := by simp only [count_ofNat]; norm_num
theorem count_prime_53_le_15 : Nat.count Nat.Prime 53 ≤ 15 := by simp only [count_ofNat]; norm_num
theorem count_prime_59_le_16 : Nat.count Nat.Prime 59 ≤ 16 := by simp only [count_ofNat]; norm_num
theorem count_prime_61_le_17 : Nat.count Nat.Prime 61 ≤ 17 := by simp only [count_ofNat]; norm_num
theorem count_prime_67_le_18 : Nat.count Nat.Prime 67 ≤ 18 := by simp only [count_ofNat]; norm_num
theorem count_prime_71_le_19 : Nat.count Nat.Prime 71 ≤ 19 := by simp only [count_ofNat]; norm_num
theorem count_prime_73_le_20 : Nat.count Nat.Prime 73 ≤ 20 := by simp only [count_ofNat]; norm_num
theorem count_prime_79_le_21 : Nat.count Nat.Prime 79 ≤ 21 := by simp only [count_ofNat]; norm_num
theorem count_prime_83_le_22 : Nat.count Nat.Prime 83 ≤ 22 := by simp only [count_ofNat]; norm_num
theorem count_prime_89_le_23 : Nat.count Nat.Prime 89 ≤ 23 := by simp only [count_ofNat]; norm_num
theorem count_prime_97_le_24 : Nat.count Nat.Prime 97 ≤ 24 := by simp only [count_ofNat]; norm_num
theorem count_prime_101_le_25 : Nat.count Nat.Prime 101 ≤ 25 := by simp only [count_ofNat]; norm_num
theorem count_prime_103_le_26 : Nat.count Nat.Prime 103 ≤ 26 := by simp only [count_ofNat]; norm_num
theorem count_prime_107_le_27 : Nat.count Nat.Prime 107 ≤ 27 := by simp only [count_ofNat]; norm_num
theorem count_prime_109_le_28 : Nat.count Nat.Prime 109 ≤ 28 := by simp only [count_ofNat]; norm_num
theorem count_prime_113_le_29 : Nat.count Nat.Prime 113 ≤ 29 := by simp only [count_ofNat]; norm_num
theorem count_prime_127_le_30 : Nat.count Nat.Prime 127 ≤ 30 := by simp only [count_ofNat]; norm_num
