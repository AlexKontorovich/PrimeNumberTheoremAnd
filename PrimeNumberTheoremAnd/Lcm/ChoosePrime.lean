import Architect
import PrimeNumberTheoremAnd.Lcm.Base
import PrimeNumberTheoremAnd.Lcm.Cert

namespace Lcm

open ArithmeticFunction hiding log
open Real Finset Nat
open scoped BigOperators

namespace ChoosePrime

/-!
This file defines the “Main-layer” criterion (six primes + inequalities),
and proves existence/building lemmas from `Lcm.Cert.Criterion`.

So: `Cert.Criterion  ⟹  (build a ChoosePrime.Criterion)`
-/

/-- The six primes + inequalities contract used by Main. -/
structure Criterion where
  n : ℕ
  hn : n ≥ 1
  p : Fin 3 → ℕ
  hp : ∀ i, Nat.Prime (p i)
  hp_mono : StrictMono p
  q : Fin 3 → ℕ
  hq : ∀ i, Nat.Prime (q i)
  hq_mono : StrictMono q
  h_ord_1 : √(n : ℝ) < p 0
  h_ord_2 : p 2 < q 0
  h_ord_3 : q 2 < n
  h_crit : ∏ i, (1 + (1 : ℝ) / q i) ≤
    (∏ i, (1 + (1 : ℝ) / (p i * (p i + 1)))) * (1 + (3 : ℝ) / (8 * n)) *
      (1 - 4 * (∏ i, (p i : ℝ)) / ∏ i, (q i : ℝ))

/- Prime selection lemmas live here (they assume `Ccert : Lcm.Cert.Criterion`). -/
theorem exists_p_primes (Ccert : Lcm.Numerical.Criterion) {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧ √(n : ℝ) < p 0 := by
  sorry

theorem exists_q_primes (Ccert : Lcm.Numerical.Criterion) {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧ q 2 < n := by
  sorry

-- theorem h_crit_of_choice (Ccert : Lcm.Numerical.Criterion) {n : ℕ} (hn : n ≥ X₀ ^ 2)
--     (p : Fin 3 → ℕ) (q : Fin 3 → ℕ) := by sorry
--   -- or keep as a theorem producing the inequality directly

/-- The main constructor: from certified numeric hypotheses, build the 6-prime Criterion. -/
-- noncomputable def Criterion.mk' {n : ℕ} (hn : n ≥ X₀ ^ 2) : Criterion where
--   n := n
--   p := sorry --(exists_p_primes hn).choose
--   q := sorry --(exists_q_primes hn).choose
--   hn := sorry --le_trans (by decide : 1 ≤ X₀ ^ 2) hn
--   hp := sorry --(exists_p_primes hn).choose_spec.1
--   hp_mono := sorry --(exists_p_primes hn).choose_spec.2.1
--   hq := sorry --(exists_q_primes hn).choose_spec.1
--   hq_mono := sorry --(exists_q_primes hn).choose_spec.2.1
--   h_ord_1 := sorry --(exists_p_primes hn).choose_spec.2.2.2
--   h_ord_2 := sorry
--   h_ord_3 := sorry
--   h_crit := sorry

noncomputable def build (Ccert : Lcm.Numerical.Criterion) {n : ℕ} (hn : n ≥ X₀ ^ 2) :
  Criterion := by
  classical
  -- choose p, q using exists_p_primes / exists_q_primes
  -- fill ordering + h_crit using your lemmas
  sorry


end ChoosePrime
end Lcm
