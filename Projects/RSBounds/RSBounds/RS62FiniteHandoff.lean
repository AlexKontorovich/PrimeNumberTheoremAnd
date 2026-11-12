import RSBounds.Totient
import TernaryGoldbach.Prelim.SmallMertensProd

/-!
# Reusing the unconditional finite RS62 prime-product certificate

The pinned upstream kernel computation proves the exact RS62 prime-product
inequality at every prime from 5 through 100000.  This module exposes that
certificate through the local definitions and combines it with an explicit
analytic-tail hypothesis.  It imports neither `MertensProduct` nor its RH or
Büthe assumptions.  The global totient conclusion still requires the stated
tail estimate; no analytic estimate is declared as an axiom.
-/

open Finset Real

namespace TernaryGoldbach.RSBounds.RS62FiniteHandoff

open Totient

/-- Exact RS62 constant, at all prime cutoffs covered by the upstream kernel. -/
theorem prime_product_le_100000 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hmax : p ≤ 100000) :
    primeProduct p < Real.exp eulerMascheroniConstant * Real.log (primeTheta p) +
      2.50637 / Real.log (primeTheta p) := by
  exact TernaryGoldbach.Prelim.MertProd.mertens_product_kernel p hp h5 (by norm_num; omega)

/-- The analytic handoff may be anywhere at or below 100001. -/
theorem prime_product_of_tail {X : ℕ} (hX : X ≤ 100001)
    (htail : ∀ p : ℕ, p.Prime → X ≤ p →
      primeProduct p < Real.exp eulerMascheroniConstant * Real.log (primeTheta p) +
        2.50637 / Real.log (primeTheta p))
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    primeProduct p < Real.exp eulerMascheroniConstant * Real.log (primeTheta p) +
      2.50637 / Real.log (primeTheta p) := by
  by_cases hmax : p ≤ 100000
  · exact prime_product_le_100000 hp h5 hmax
  · exact htail p hp (by omega)

/-- An unrestricted totient reduction with the finite range discharged.
The only unproved mathematical input is the explicit prime-product tail. -/
theorem totient_ratio_lt_of_tail {X : ℕ} (hX : X ≤ 100001)
    (htail : ∀ p : ℕ, p.Prime → X ≤ p →
      primeProduct p < Real.exp eulerMascheroniConstant * Real.log (primeTheta p) +
        2.50637 / Real.log (primeTheta p))
    {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) / Nat.totient n <
      Real.exp eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  apply Totient.totient_ratio_lt_of_prime_product_at_rank
    (by omega) (by exact_mod_cast hn) le_rfl
  intro hcard
  apply prime_product_of_tail hX htail (Nat.prime_nth_prime _)
  rw [← Nat.nth_prime_two_eq_five]
  exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)

end TernaryGoldbach.RSBounds.RS62FiniteHandoff
