import Architect
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting

namespace Erdos392

blueprint_comment /--
\section{Erdos problem 392}

The proof here is adapted from \url{https://www.erdosproblems.com/forum/thread/392#post-2696} which
in turn is inspired by the arguments in \url{https://arxiv.org/abs/2503.20170}
-/

open Real

@[blueprint
  "factorization-def"
  (statement := /--
  We work with (approximate) factorizations $a_1 \dots a_t$ of a factorial $n!$.
  -/)]
structure Factorization (n : ℕ) where
  a : Multiset ℕ
  ha : ∀ m ∈ a, m ≤ n

def Factorization.sum {n : ℕ} (f : Factorization n) {R : Type*} [AddCommMonoid R] (F : ℕ → R) : R := (f.a.map F).sum

def Factorization.prod {n : ℕ} (f : Factorization n) {R : Type*} [CommMonoid R] (F : ℕ → R) : R := (f.a.map F).prod

@[blueprint
  "waste-def"
  (statement := /--
  The waste of a factorizations $a_1 \dots a_t$ is defined as $\sum_i \log (n / a_i)$.
  -/)]
noncomputable def Factorization.waste {n : ℕ} (f : Factorization n) : ℝ := f.sum (fun m ↦ log (n / m : ℝ))

@[blueprint
  "balance-def"
  (statement := /--
  The balance of a factorization $a_1 \dots a_t$ at a prime $p$ is defined as the number of times $p$ divides $a_1 \dots a_t$, minus the number of times $p$ divides $n!$.
  -/)]
def Factorization.balance {n : ℕ} (f : Factorization n) (p : ℕ) : ℤ := f.sum (fun m ↦ m.factorization p) - (n.factorial.factorization p:ℤ)

@[blueprint
  "balance-def"
  (statement := /--
  The total imbalance of a factorization $a_1 \dots a_t$ is the sum of absolute values of the balances at each prime.
  -/)]
def Factorization.total_imbalance {n : ℕ} (f : Factorization n) : ℕ :=
  ∑ p ∈ (n+1).primesBelow, (f.balance p).natAbs

@[blueprint
  "balance-zero"
  (statement := /--
  If a factorization has zero total imbalance, then it exactly factors $n!$.
  -/)]
theorem Factorization.zero_total_imbalance {n : ℕ} (f : Factorization n) (hf : f.total_imbalance = 0) : f.prod id = n.factorial := by sorry

@[blueprint
  "waste-eq"
  (statement := /--
  The waste of a factorization is equal to $t \log n - \log n!$, where $t$ is the number of elements.
  -/)]
theorem Factorization.waste_eq {n : ℕ} (f : Factorization n) (hf : f.total_imbalance = 0) : f.a.card * (log n) = log n.factorial + f.waste := by sorry

@[blueprint
  "score-def"
  (statement := /--
  The score of a factorization (relative to a cutoff parameter $L$) is equal to its waste, plus $\log p$ for every surplus prime $p$, $\log (n/p)$ for every deficit prime above $L$, $\log L$ for every deficit prime below $L$ and an additional $\log n$ if one is not in total balance.
  -/)]
noncomputable def Factorization.score {n : ℕ} (f : Factorization n) (L : ℕ) : ℝ :=
  f.waste
  + (if f.total_imbalance > 0 then log n else 0)
  + ∑ p ∈ (n+1).primesBelow,
    if f.balance p > 0 then (f.balance p) * (log p)
    else if p ≤ L then (-f.balance p) * (log L)
    else (-f.balance p) * (log (n/p))

@[blueprint
  "score-eq"
  (statement := /--
  If one is in total balance, then the score is equal to the waste.
  -/)]
theorem Factorization.score_eq {n : ℕ} {f : Factorization n} (hf : f.total_imbalance = 0) (L : ℕ) : f.score L = f.waste := by sorry

@[blueprint
  "score-lower-1"
  (statement := /--
  If there is a prime $p$ in surplus, one can remove it without increasing the score.
  -/)
  (proof := /-- Locate a factor $a_i$ that contains the surplus prime $p$, then replace $a_i$ with $a_i/p$.-/)]
theorem Factorization.lower_score_1 {n : ℕ} (f : Factorization n) (L : ℕ) (hf : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0) : ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by sorry

@[blueprint
  "score-lower-2"
  (statement := /--
  If there is a prime $p$ in deficit larger than $L$, one can remove it without increasing the score.
  -/)
  (proof := /-- Add an additional factor of $p$ to the factorization.-/)]
theorem Factorization.lower_score_2 {n : ℕ} (f : Factorization n) (L : ℕ) (hf : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0) : ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by sorry

@[blueprint
  "score-lower-3"
  (statement := /--
  If there is a prime $p$ in deficit less than $L$, one can remove it without increasing the score.
  -/)
  (proof := /-- Without loss of generality we may assume that one is not in the previous two situations, i.e., wlog there are no surplus primes and all primes in deficit are at most $L$.

  If all deficit primes multiply to $n$ or less, add that product to the factorization (this increases the waste by at most $\log n$, but we save a $\log n$ from now being in balance).  Otherwise, greedily multiply all primes together while staying below $n$ until one cannot do so any further; add this product to the factorization, increasing the waste by at most $\log L$.-/)]
theorem Factorization.lower_score_3 {n : ℕ} (f : Factorization n) (L : ℕ) (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) : ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by sorry

@[blueprint
  "score-lowest"
  (statement := /--
  One can bring any factorization into balance without increasing the score.
  -/)
  (proof := /-- Apply strong induction on the total imbalance of the factorization and use the previous three theorems.-/)]
theorem Factorization.lowest_score {n : ℕ} (f : Factorization n) (L : ℕ) : ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ f.score L := by sorry


@[blueprint
  "card-bound"
  (statement := /--
  Starting from any factorization $f$, one can find a factorization $f'$ in balance whose cardinality is at most $\log n!$ plus the score of $f$, divided by $\log n$.-/)
  (proof := /-- Combine Theorem \ref{score-lowest}, Theorem \ref{score-eq}, and Theorem \ref{waste-eq}.-/)]
theorem Factorization.card_bound {n : ℕ} (f : Factorization n) (L : ℕ) : ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ (f'.a.card : ℝ) * (log n) ≤ log n.factorial + (f.score L) := by sorry

@[blueprint
  "params-set"
  (statement := /-- Now let $M,L$ be additional parameters with $n > L^2$. -/)]
structure Params where
  n : ℕ
  M : ℕ
  L : ℕ
  hL : n > L * L

@[blueprint
  "initial-factorization-def"
  (statement := /-- We perform an initial factorization by taking the natural numbers between $n-n/M$ and $n$ repeated $M$ times, deleting those elements that are not $n/L$-smooth. -/)]
def Params.initial (P : Params) : Factorization P.n := {
  a := (Multiset.replicate P.M (Multiset.Ico (P.n - P.n/P.M) P.n)).join.filter (fun m ↦ m ∈ (P.n/P.L).smoothNumbers)
  ha := by
    intro m hm
    simp only [Multiset.mem_filter, Multiset.mem_join] at hm
    obtain ⟨ s, hs, hs2 ⟩ := hm.1
    replace hs := Multiset.eq_of_mem_replicate hs
    simp [hs] at hs2
    grind
}

@[blueprint
  "initial-factorization-card"
  (statement := /-- The number of elements in this initial factorization is at most $n$. -/)]
theorem Params.initial.card (P : Params) : P.initial.a.card ≤ P.n := by sorry

@[blueprint
  "initial-factorization-waste"
  (statement := /-- The total waste in this initial factorization is at most $n \log \frac{1}{1-1/M}$. -/)]
theorem Params.initial.waste (P : Params) : P.initial.waste ≤ P.n * log (1 - 1/P.M)⁻¹ := by sorry

@[blueprint
  "initial-factorization-large-prime-le"
  (statement := /-- A large prime $p > n/L$ cannot be in surplus. -/)
  (proof := /-- No such prime can be present in the factorization.-/)]
theorem Params.initial.balance_large_prime_le (P : Params) {p : ℕ} (hq : p > P.n / P.L) : P.initial.balance p ≤ 0 := by sorry

@[blueprint
  "initial-factorization-large-prime-le"
  (statement := /-- A large prime $p > n/L$ can be in deficit by at most $n/p$. -/)
  (proof := /-- This is the number of times $p$ can divide $n!$. -/)]
theorem Params.initial.balance_large_prime_ge (P : Params) {p : ℕ} (hp : p > P.n / P.L) : P.initial.balance p ≥ - (P.n/p) := by sorry

@[blueprint
  "initial-factorization-medium-prime-le"
  (statement := /-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in surplus by at most $M$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_medium_prime_le (P : Params) {p : ℕ} (hp : p ≤ P.n / P.L) (hp' : p > sqrt P.n) : P.initial.balance p ≤ P.M := by sorry

@[blueprint
  "initial-factorization-medium-prime-ge"
  (statement := /-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in deficit by at most $M$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_medium_prime_ge (P : Params) {p : ℕ} (hp : p ≤ P.n / P.L) (hp' : p > sqrt P.n) : P.initial.balance p ≥ -P.M := by sorry

@[blueprint
  "initial-factorization-small-prime-le"
  (statement := /-- A small prime $p \leq \sqrt{n}$ can be in surplus by at most $M\log n$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_small_prime_le (P : Params) {p : ℕ} (hp : p ≤ sqrt P.n) : P.initial.balance p ≤ P.M * (log P.n) := by sorry

@[blueprint
  "initial-factorization-small-prime-ge"
  (statement := /-- A small prime $L < p \leq \sqrt{n}$ can be in deficit by at most $M\log n$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_small_prime_ge (P : Params) {p : ℕ} (hp : p ≤ sqrt P.n) (hp' : p > P.L) : P.initial.balance p ≥ - P.M * (log P.n) := by sorry

@[blueprint
  "initial-factorization-tiny-prime-ge"
  (statement := /-- A tiny prime $p \leq L$ can be in deficit by at most $M\log n + ML\pi(n)$.-/)
  (proof := /-- In addition to the Legendre calculations, one potentially removes factors of the form $plq$ with $l \leq L$ and $q \leq n$ a prime up to $M$ times each, with at most $L$ copies of $p$ removed at each factor.-/)]
theorem Params.initial.balance_tiny_prime_ge (P : Params) {p : ℕ} (hp : p ≤ P.L) : P.initial.balance p ≥ - P.M * (log P.n) - P.M * P.L^2 * (Nat.primeCounting P.n) := by sorry

@[blueprint
  "initial-score"
  (statement := /-- The score of the initial factorization can be taken to be $o(n)$.-/)
  (proof := /-- Pick $M$ large depending on $\varepsilon$, then $L = M^2$, then assume $n$ large.  Using the prime number theorem and Theorem \ref{initial-factorization-waste}, Theorem \ref{initial-factorization-large-prime-le}, Theorem \ref{initial-factorization-large-prime-ge}, Theorem \ref{initial-factorization-medium-prime-le}, Theorem \ref{initial-factorization-medium-prime-ge}, Theorem \ref{initial-factorization-small-prime-le}, Theorem \ref{initial-factorization-small-prime-ge}, and Theorem \ref{initial-factorization-tiny-prime-ge}, one can hold all losses to be of size $O(\varepsilon n)$.-/)]
theorem Params.initial.score (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in Filter.atTop, ∃ P : Params, P.n = n ∧ P.initial.score P.L ≤ ε * n := by sorry

@[blueprint
  "erdos-sol-1"
  (statement := /-- One can find a balanced factorization of $n!$ with cardinality at least $n - n / \log n - o(n / \log n)$.--/)
  (proof := /-- Combine Theorem \ref{initial-score} with Theorem \ref{card-bound} and the Stirling approximation.-/)]
theorem Solution_1 (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in Filter.atTop, ∃ f : Factorization n, f.total_imbalance = 0 ∧ f.a.card ≥ n - n / (log n) - ε * n / (log n) := by sorry

@[blueprint
  "erdos-sol-2"
  (statement := /-- One can find a factor $n!$ into at least $n/2 - n / 2\log n - o(n / \log n)$ numbers of size at most $n^2$.--/)
  (proof := /-- Group the factorization arising in Theorem \ref{erdos-sol-1} into pairs, using Theorem \ref{balance-zero}.-/)]
theorem Solution_2 (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in Filter.atTop, ∃ (t : ℕ) (a : Fin t → ℕ), ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n^2 ∧ t ≥ (n/2) - n/(2*log n) - ε * n / (log n) := by sorry


end Erdos392
