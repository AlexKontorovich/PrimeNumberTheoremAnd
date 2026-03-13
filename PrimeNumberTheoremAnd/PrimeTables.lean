import Mathlib.Data.Nat.Prime.Defs

/-!
# Primality certificates for large numbers

This file collects `native_decide`-based primality proofs for large numbers that are
expensive to check. By isolating them in their own file, the cost is paid only once
(when this file is first built or when new primes are added), rather than every time
a downstream file is edited.
-/

theorem prime_211 : Nat.Prime 211 := by native_decide

theorem prime_313 : Nat.Prime 313 := by native_decide

theorem prime_3999999999999999791 : Nat.Prime 3999999999999999791 := by native_decide

theorem prime_3999999999999999691 : Nat.Prime 3999999999999999691 := by native_decide
