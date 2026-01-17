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
theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  -- define the “base point”
  let x : ℝ := √(n : ℝ)
  have hxX : (X₀ : ℝ) ≤ x := by
    simpa [x] using Numerical.sqrt_ge_X₀ (n := n) hn
  -- define ε once (this is where `hε` comes from if you use `set`)
  let ε : ℝ := gap.δ x

  -- (1) first prime at x
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ :=
    gap.prime_in_Icc (x := x) hxX
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := by
    simpa [ε] using hp₀_ub

  -- (2) second prime at x*(1+ε)
  have hx1X : (X₀ : ℝ) ≤ x * (1 + ε) := by
    -- Cert lemma C4, rewritten to use `x`/`ε`
    -- (since x = √n and ε = δ x)
    simpa [x, ε] using Numerical.step1_ge_X₀ (n := n) hn

  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε)) hx1X

  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    -- provider gives `p₁ ≤ (x*(1+ε)) * (1 + δ(x*(1+ε)))`
    -- Cert lemma C6 turns that into `≤ x*(1+ε)^2`
    refine le_trans (by simpa [ε] using hp₁_ub) ?_
    simpa [x, ε] using Numerical.step1_upper (n := n) hn

  -- (3) third prime at x*(1+ε)^2
  have hx2X : (X₀ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    simpa [x, ε] using Numerical.step2_ge_X₀ (n := n) hn

  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ :=
    gap.prime_in_Icc (x := x * (1 + ε) ^ 2) hx2X

  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    refine le_trans (by simpa [ε] using hp₂_ub) ?_
    simpa [x, ε] using Numerical.step2_upper (n := n) hn

  -- package the primes
  refine ⟨![p₀, p₁, p₂], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · -- StrictMono via "prev upper < next lower"
    refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i
    fin_cases i
    · -- p0 < p1
      exact cast_lt.mp (hp₀_ub'.trans_lt hp₁_lb)
    · -- p1 < p2
      exact cast_lt.mp (hp₁_ub'.trans_lt hp₂_lb)
  · -- upper bounds by cases
    intro i
    fin_cases i <;> norm_num
    · -- i = 0 : exponent is 1
      simpa [x, ε] using hp₀_ub'
    · -- i = 1 : exponent is 2
      simpa [x, ε] using hp₁_ub'
    · -- i = 2 : exponent is 3
      simpa [x, ε] using hp₂_ub'
  · -- √n < p0
    simpa [x] using hp₀_lb

theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ)) ≤ q i) ∧
      q 2 < n := by
  let x : ℝ := √(n : ℝ)
  let ε : ℝ := gap.δ x
  let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
  let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
  let y2 : ℝ := (n : ℝ) / (1 + ε)

  -- apply provider at y0,y1,y2
  have hy0X : (X₀ : ℝ) ≤ y0 := by simpa [x, ε, y0] using Numerical.y0_ge_X₀ (n := n) hn
  have hy1X : (X₀ : ℝ) ≤ y1 := by simpa [x, ε, y1] using Numerical.y1_ge_X₀ (n := n) hn
  have hy2X : (X₀ : ℝ) ≤ y2 := by simpa [x, ε, y2] using Numerical.y2_ge_X₀ (n := n) hn

  obtain ⟨q₀, hq₀_prime, hq₀_lb, hq₀_ub⟩ := gap.prime_in_Icc (x := y0) hy0X
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ := gap.prime_in_Icc (x := y1) hy1X
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ := gap.prime_in_Icc (x := y2) hy2X

  -- chain the upper bounds
  have hq₀_ub' : (q₀ : ℝ) ≤ y1 := by
    -- q₀ ≤ y0*(1+δ y0) ≤ y1
    refine le_trans (by simpa [y0] using hq₀_ub) ?_
    simpa [x, ε, y0, y1] using Numerical.y0_mul_one_add_delta_le_y1 (n := n) hn

  have hq₁_ub' : (q₁ : ℝ) ≤ y2 := by
    refine le_trans (by simpa [y1] using hq₁_ub) ?_
    simpa [x, ε, y1, y2] using Numerical.y1_mul_one_add_delta_le_y2 (n := n) hn

  have hq₂_lt_n : q₂ < n := by
    -- q₂ ≤ y2*(1+δ y2) < n
    have hq₂_lt : (q₂ : ℝ) < (n : ℝ) := by
      have : (q₂ : ℝ) ≤ y2 * (1 + gap.δ y2) := by simpa [y2] using hq₂_ub
      exact lt_of_le_of_lt this (by simpa [x, ε, y2] using Numerical.y2_mul_one_add_delta_lt_n (n := n) hn)
    exact Nat.cast_lt.mp hq₂_lt

  -- package as Fin 3 → ℕ and prove StrictMono using lb/ub
  refine ⟨![q₀, q₁, q₂], ?_, ?_, ?_, hq₂_lt_n⟩
  · intro i; fin_cases i <;> assumption
  · refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i; fin_cases i
    · exact Nat.cast_lt.mp (hq₀_ub'.trans_lt hq₁_lb)
    · exact Nat.cast_lt.mp (hq₁_ub'.trans_lt hq₂_lb)
  · intro i
    fin_cases i <;> simp [x, ε, y0, y1, y2]
    · -- i=0 : y0 ≤ q0
      exact (le_of_lt hq₀_lb)
    · -- i=1 : y1 ≤ q1
      exact (le_of_lt hq₁_lb)
    · -- i=2 : y2 ≤ q2
      exact (le_of_lt hq₂_lb)


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
