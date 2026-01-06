import Architect
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting

namespace Erdos392

blueprint_comment /--
\section{Erdos problem 392}

The proof here is adapted from \url{https://www.erdosproblems.com/forum/thread/392\#post-2696} which
in turn is inspired by the arguments in \url{https://arxiv.org/abs/2503.20170}.
-/

open Finset Real Multiset

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
theorem Factorization.score_eq {n : ℕ} {f : Factorization n} (hf : f.total_imbalance = 0) (L : ℕ) :
    f.score L = f.waste := by
  simp_all [total_imbalance, score]

/-- Given a factorization `f`, an element `m` in it, and a new number `m' ≤ n`,
`replace` returns a new factorization with `m` replaced by `m'`. -/
def Factorization.replace {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (_hm : m ∈ f.a) (hm' : m' ≤ n) : Factorization n where
  a := (f.a.erase m).cons m'
  ha x hx := by
    simp only [Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hm'
    · exact f.ha x (Multiset.mem_of_mem_erase hx)

/-- If the balance of a prime `p` is positive in factorization `f`, then there exists
a number `m` in `f` that is divisible by `p`. -/
lemma Factorization.exists_mem_dvd_of_balance_pos {n : ℕ} (f : Factorization n)
    (p : ℕ) (_hp : p.Prime) (h : f.balance p > 0) : ∃ m ∈ f.a, p ∣ m := by
  contrapose! h
  simp only [balance, sum, sub_nonpos, Nat.cast_le]
  calc (f.a.map fun m => m.factorization p).sum
      = (f.a.map fun _ => (0 : ℕ)).sum := by
          congr 1; exact Multiset.map_congr rfl fun x hx =>
            Nat.factorization_eq_zero_of_not_dvd (h x hx)
    _ = 0 := by simp
    _ ≤ _ := zero_le _

/-- The sum of a function `F` over a factorization after replacing `m` with `m'`
equals the original sum minus `F m` plus `F m'`. -/
lemma Factorization.replace_sum {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (hm : m ∈ f.a) (hm' : m' ≤ n) {R : Type*} [AddCommGroup R] (F : ℕ → R) :
    (f.replace m m' hm hm').sum F = f.sum F - F m + F m' := by
  simp only [replace, sum, Multiset.map_cons, Multiset.sum_cons]
  conv_rhs => rw [← cons_erase hm, Multiset.map_cons, Multiset.sum_cons]
  grind

/-- The balance of a prime `q` after replacing `m` with `m'` equals the original balance
minus the exponent of `q` in `m` plus the exponent of `q` in `m'`. -/
lemma Factorization.replace_balance {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (hm : m ∈ f.a) (hm' : m' ≤ n) (q : ℕ) :
    (f.replace m m' hm hm').balance q =
      f.balance q - m.factorization q + m'.factorization q := by
  simp only [balance, replace, sum, Multiset.map_cons, Multiset.sum_cons]
  conv_rhs => rw [← Multiset.cons_erase hm, Multiset.map_cons, Multiset.sum_cons]
  grind

/-- If we replace `m` with `m/p` where `p` divides `m`, the balance of `p` decreases by 1,
and the balance of any other prime remains unchanged. -/
lemma Factorization.replace_div_balance {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime) (q : ℕ) :
    let m' := m / p
    have hm' : m' ≤ n := (Nat.div_le_self m p).trans (f.ha m hm)
    (f.replace m m' hm hm').balance q = if q = p then f.balance q - 1 else f.balance q := by
  have hm_ne : m ≠ 0 := pos_of_ne_zero (fun h ↦ by simp [h] at h_fac_pos) |> pos_iff_ne_zero.mp
  have hp_dvd : p ∣ m := hp.dvd_iff_one_le_factorization hm_ne |>.mpr h_fac_pos
  simp only [replace_balance, Nat.factorization_div hp_dvd]
  split_ifs with hq
  · subst hq
    simp only [Nat.Prime.factorization_self hp, Finsupp.coe_tsub, Pi.sub_apply]
    grind
  · have : p.factorization q = 0 := by rw [Nat.Prime.factorization hp]; grind
    simp only [this, Finsupp.coe_tsub, Pi.sub_apply, tsub_zero]
    grind

/-- Replacing `m` with `m/p` strictly decreases the total imbalance
when `p` has positive balance. -/
lemma Factorization.replace_div_total_imbalance {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime)
    (hp_mem : p ∈ (n + 1).primesBelow) (h_bal_pos : f.balance p > 0) :
    let m' := m / p
    have hm' : m' ≤ n := (Nat.div_le_self m p).trans (f.ha m hm)
    (f.replace m m' hm hm').total_imbalance < f.total_imbalance := by
  refine Finset.sum_lt_sum (fun q _ ↦ ?_) <| ⟨p, hp_mem, by
    rw [replace_div_balance f m p hm h_fac_pos hp p, if_pos rfl]; grind⟩
  rw [replace_div_balance f m p hm h_fac_pos hp q]
  split_ifs with hq <;> grind

/-- Replacing `m` with `m/p` decreases the score (or keeps it equal) if `p` has positive balance.
The waste increases by `log p`, but the sum term decreases by `log p`,
and the imbalance term is non-increasing. -/
lemma Factorization.replace_div_score_le {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime)
    (hp_mem : p ∈ (n + 1).primesBelow) (_h_bal_pos : f.balance p > 0) (L : ℕ) :
    let m' := m / p
    have hm' : m' ≤ n := (Nat.div_le_self m p).trans (f.ha m hm)
    (f.replace m m' hm hm').score L ≤ f.score L := by
  simp only
  set m' := m / p with hm'_def
  have hm' : m' ≤ n := (Nat.div_le_self m p).trans (f.ha m hm)
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero fun h ↦ by simp [h] at h_fac_pos)
  have hp_dvd : p ∣ m := hp.dvd_iff_one_le_factorization hm_ne |>.mpr h_fac_pos
  have h_waste : (f.replace m m' hm hm').waste ≤ f.waste + Real.log p := by
    have h_waste_eq : (f.replace m m' hm hm').waste =
        f.waste - Real.log (n / m) + Real.log (n / m') :=
      replace_sum f m m' hm hm' (fun x => Real.log (n / x))
    rw [h_waste_eq]
    by_cases hn : n = 0
    · simp [hn]; positivity
    · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm_ne)
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have hm'_pos : (0 : ℝ) < m' := by
        simp only [hm'_def]
        have : p ≤ m := hp.dvd_iff_one_le_factorization hm_ne |>.mpr h_fac_pos |> Nat.le_of_dvd
          (Nat.pos_of_ne_zero hm_ne)
        exact Nat.cast_pos.mpr (Nat.div_pos this hp.pos)
      simp only [hm'_def]
      rw [Real.log_div (by linarith) (by linarith),
          Real.log_div (by linarith) (by linarith),
          Nat.cast_div hp_dvd (Nat.cast_ne_zero.mpr hp.ne_zero),
          Real.log_div (by linarith) (by linarith)]
      ring_nf
      rfl
  have h_pointwise : ∀ q ∈ (n + 1).primesBelow,
      (if (f.replace m m' hm hm').balance q > 0
       then ((f.replace m m' hm hm').balance q : ℝ) * Real.log q
       else if q ≤ L then -((f.replace m m' hm hm').balance q : ℝ) * Real.log L
       else -((f.replace m m' hm hm').balance q : ℝ) * Real.log (n / q)) ≤
      (if f.balance q > 0 then (f.balance q : ℝ) * Real.log q
       else if q ≤ L then -(f.balance q : ℝ) * Real.log L
       else -(f.balance q : ℝ) * Real.log (n / q)) -
      (if q = p then Real.log p else 0) := fun q _ ↦ by
    by_cases hq_eq_p : q = p
    · have h_bal : (f.replace m m' hm hm').balance q = f.balance q - 1 := by
        rw [replace_div_balance f m p hm h_fac_pos hp q, if_pos hq_eq_p]
      have hbp : 0 < f.balance q := hq_eq_p ▸ _h_bal_pos
      simp only [hq_eq_p, ↓reduceIte]
      rcases Int.lt_or_eq_of_le hbp with h1 | h1
      · split_ifs with h2 h3 <;> simp_all; nlinarith
      · rw [← hq_eq_p, h_bal, ← h1]
        simp
    · have h_bal_eq : (f.replace m m' hm hm').balance q = f.balance q := by
        rw [replace_div_balance f m p hm h_fac_pos hp q, if_neg hq_eq_p]
      simp only [hq_eq_p, ↓reduceIte, sub_zero, h_bal_eq, le_refl]
  have h_sum_term := Finset.sum_le_sum h_pointwise
  simp only [Finset.sum_ite] at h_sum_term
  simp only [Finset.sum_sub_distrib] at h_sum_term
  have h_sum_term' : ∑ q ∈ (n + 1).primesBelow,
      (if (f.replace m m' hm hm').balance q > 0
       then ((f.replace m m' hm hm').balance q : ℝ) * Real.log q
       else if q ≤ L then -((f.replace m m' hm hm').balance q : ℝ) * Real.log L
       else -((f.replace m m' hm hm').balance q : ℝ) * Real.log (n / q)) ≤
      ∑ q ∈ (n + 1).primesBelow,
      (if f.balance q > 0 then (f.balance q : ℝ) * Real.log q
       else if q ≤ L then -(f.balance q : ℝ) * Real.log L
       else -(f.balance q : ℝ) * Real.log (n / q)) - Real.log p := by
    calc _ ≤ ∑ q ∈ (n + 1).primesBelow,
        ((if f.balance q > 0 then (f.balance q : ℝ) * Real.log q
         else if q ≤ L then -(f.balance q : ℝ) * Real.log L
         else -(f.balance q : ℝ) * Real.log (n / q)) -
        (if q = p then Real.log p else 0)) := Finset.sum_le_sum h_pointwise
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [← Finset.sum_filter]
        simp only [Finset.filter_eq', hp_mem, ↓reduceIte, Finset.sum_singleton]
  -- Combine waste and sum term bounds
  unfold score at *
  split_ifs <;> norm_num at *
  · linarith
  · unfold total_imbalance at *; aesop
  · have hp_ge_one : (p : ℝ) ≥ 1 := Nat.one_le_cast.mpr hp.pos
    have hp_le_n : (p : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_succ_le (Nat.succ_le_of_lt
        (Nat.lt_of_mem_primesBelow hp_mem)))
    linarith [Real.log_nonneg hp_ge_one, Real.log_le_log (Nat.cast_pos.mpr hp.pos) hp_le_n]
  · linarith

@[blueprint
  "score-lower-1"
  (statement := /-- If there is a prime $p$ in surplus, one can remove it without increasing the
  score. -/)
  (proof := /-- Locate a factor $a_i$ that contains the surplus prime $p$, then
  replace $a_i$ with $a_i/p$.-/)]
theorem Factorization.lower_score_1 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0) :
    ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p, hp_mem, hp_pos⟩ := hf
  obtain ⟨m, hm, h_fac_pos⟩ : ∃ m ∈ f.a, 0 < m.factorization p := by
    contrapose! hp_pos
    simp_all [balance, sum]
  exact ⟨_, replace_div_total_imbalance f m p hm h_fac_pos (Nat.prime_of_mem_primesBelow hp_mem)
    hp_mem hp_pos, Erdos392.Factorization.replace_div_score_le f m p hm h_fac_pos
      (Nat.prime_of_mem_primesBelow hp_mem) hp_mem hp_pos L⟩

@[blueprint
  "score-lower-2"
  (statement := /-- If there is a prime $p$ in deficit larger than $L$, one can remove it without increasing the
  score.-/)
  (proof := /-- Add an additional factor of $p$ to the factorization.-/)]
theorem Factorization.lower_score_2 {n : ℕ} (f : Factorization n) (L : ℕ) (hf : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0) : ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p, hp_prime, hp_gt_L, hp_balance⟩ := hf;
  set f' : Erdos392.Factorization n := ⟨f.a + {p}, by
    simp at *;
    rintro m ( hm | rfl ) <;> [ exact f.ha m hm; exact Nat.le_of_lt_succ ( Nat.lt_of_mem_primesBelow hp_prime ) ]⟩
  generalize_proofs at *;
  have h_total_imbalance : f'.total_imbalance < f.total_imbalance := by
    have h_balance_change : f'.balance p = f.balance p + 1 := by
      unfold Erdos392.Factorization.balance;
      simp +zetaDelta at *;
      unfold Erdos392.Factorization.sum; simp +decide [ add_comm, add_left_comm, add_assoc ] ;
      rw [ Nat.Prime.factorization ( Nat.prime_of_mem_primesBelow hp_prime ) ] ; norm_num ; ring;
    fapply Finset.sum_lt_sum;
    · intro q hq; by_cases hq' : q = p <;> simp_all +decide [ Erdos392.Factorization.balance ] ;
      · omega;
      · simp_all +decide [ Factorization.sum ];
        rw [ Nat.primesBelow ] at * ; aesop;
    · grind;
  have h_score : f'.waste + (if f'.total_imbalance > 0 then log n else 0) + ∑ p ∈ (n + 1).primesBelow, (if f'.balance p > 0 then (f'.balance p) * (log p) else if p ≤ L then (-f'.balance p) * (log L) else (-f'.balance p) * (log (n / p))) ≤ f.waste + (if f.total_imbalance > 0 then log n else 0) + ∑ p ∈ (n + 1).primesBelow, (if f.balance p > 0 then (f.balance p) * (log p) else if p ≤ L then (-f.balance p) * (log L) else (-f.balance p) * (log (n / p))) := by
    have h_sum_term : ∑ p ∈ (n + 1).primesBelow, (if f'.balance p > 0 then (f'.balance p) * (log p) else if p ≤ L then (-f'.balance p) * (log L) else (-f'.balance p) * (log (n / p))) ≤ ∑ p ∈ (n + 1).primesBelow, (if f.balance p > 0 then (f.balance p) * (log p) else if p ≤ L then (-f.balance p) * (log L) else (-f.balance p) * (log (n / p))) - Real.log (n / p) := by
      have h_sum_term : ∀ q ∈ (n + 1).primesBelow, q ≠ p → (if f'.balance q > 0 then (f'.balance q) * (log q) else if q ≤ L then (-f'.balance q) * (log L) else (-f'.balance q) * (log (n / q))) = (if f.balance q > 0 then (f.balance q) * (log q) else if q ≤ L then (-f.balance q) * (log L) else (-f.balance q) * (log (n / q))) := by
        intro q hq hqp; simp +decide [ *, mul_comm, Erdos392.Factorization.balance ] ;
        simp +decide [ f', Erdos392.Factorization.sum ];
        rw [ Nat.factorization_eq_zero_of_not_dvd ( show ¬ q ∣ p from fun h => hqp <| by have := Nat.prime_dvd_prime_iff_eq ( Nat.prime_of_mem_primesBelow hq ) ( Nat.prime_of_mem_primesBelow hp_prime ) ; aesop ) ] ; norm_num;
      have h_term_p : (if f'.balance p > 0 then (f'.balance p) * (log p) else if p ≤ L then (-f'.balance p) * (log L) else (-f'.balance p) * (log (n / p))) ≤ (if f.balance p > 0 then (f.balance p) * (log p) else if p ≤ L then (-f.balance p) * (log L) else (-f.balance p) * (log (n / p))) - Real.log (n / p) := by
        have h_balance_p : f'.balance p = f.balance p + 1 := by
          unfold Erdos392.Factorization.balance at *;
          unfold Erdos392.Factorization.sum at *;
          simp +zetaDelta at *;
          rw [ Nat.Prime.factorization ( Nat.prime_of_mem_primesBelow hp_prime ) ] ; norm_num ; ring;
        split_ifs <;> try linarith;
        rw [ h_balance_p ] ; push_cast ; ring_nf ; norm_num;
      rw [ Finset.sum_eq_add_sum_diff_singleton hp_prime ];
      rw [ Finset.sum_eq_add_sum_diff_singleton hp_prime ];
      rw [ Finset.sum_congr rfl fun x hx => h_sum_term x ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop ) ] ; linarith;
    have h_penalty_term : (if f'.total_imbalance > 0 then Real.log n else 0) ≤ (if f.total_imbalance > 0 then Real.log n else 0) := by
      split_ifs <;> norm_num;
      · linarith;
      · positivity;
    have h_waste_term : f'.waste ≤ f.waste + Real.log (n / p) := by
      unfold Erdos392.Factorization.waste;
      unfold Erdos392.Factorization.sum; aesop;
    linarith;
  exact ⟨ f', h_total_imbalance, h_score ⟩

@[blueprint
  "score-lower-3"
  (statement := /--
  If there is a prime $p$ in deficit less than $L$, one can remove it without increasing the score.
  -/)
  (proof := /-- Without loss of generality we may assume that one is not in the previous two
  situations, i.e., wlog there are no surplus primes and all primes in deficit are at most $L$.
  If all deficit primes multiply to $n$ or less, add that product to the factorization (this
  increases the waste by at most $\log n$, but we save a $\log n$ from now being in balance).
  Otherwise, greedily multiply all primes together while staying below $n$ until one cannot do so
  any further; add this product to the factorization, increasing the waste by at most $\log L$.-/)]
theorem Factorization.lower_score_3 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) : ∃ f' :
    Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  sorry

@[blueprint
  "score-lowest"
  (statement := /-- One can bring any factorization into balance without increasing the score. -/)
  (proof := /-- Apply strong induction on the total imbalance of the factorization and use the
  previous three theorems.-/)]
theorem Factorization.lowest_score {n : ℕ} (f : Factorization n) (L : ℕ) :
    ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ f.score L := by
  induction h : f.total_imbalance using Nat.strong_induction_on generalizing f with
  | _ k ih =>
    obtain rfl | hk := k.eq_zero_or_pos
    · exact ⟨f, h, le_refl _⟩
    · have step : ∀ g : Factorization n, g.total_imbalance < k →
          ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ g.score L := fun g hg =>
        ih g.total_imbalance (h ▸ hg) g rfl
      by_cases h1 : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0
      · obtain ⟨f₁, hlt, hle⟩ := lower_score_1 f L h1
        obtain ⟨f', hbal, hle'⟩ := step f₁ (h ▸ hlt)
        exact ⟨f', hbal, hle'.trans hle⟩
      · by_cases h2 : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0
        · obtain ⟨f₁, hlt, hle⟩ := lower_score_2 f L h2
          obtain ⟨f', hbal, hle'⟩ := step f₁ (h ▸ hlt)
          exact ⟨f', hbal, hle'.trans hle⟩
        · have h3 : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0 := by
            simp only [not_exists, not_and, not_lt] at h1 h2; by_contra hc; push_neg at hc
            exact hk.ne' <| h ▸ sum_eq_zero fun p hp ↦ by
              have := h1 p hp; have := if hpL : p ≤ L then hc p hp hpL
                else h2 p hp (Nat.lt_of_not_le hpL); omega
          obtain ⟨f₁, hlt, hle⟩ := lower_score_3 f L h3
          obtain ⟨f', hbal, hle'⟩ := step f₁ (h ▸ hlt)
          exact ⟨f', hbal, hle'.trans hle⟩

@[blueprint
  "card-bound"
  (statement := /--
  Starting from any factorization $f$, one can find a factorization $f'$ in balance whose
  cardinality is at most $\log n!$ plus the score of $f$, divided by $\log n$.-/)
  (proof := /-- Combine Theorem \ref{score-lowest}, Theorem \ref{score-eq}, and
  Theorem \ref{waste-eq}.-/)]
theorem Factorization.card_bound {n : ℕ} (f : Factorization n) (L : ℕ) : ∃ f' :
    Factorization n, f'.total_imbalance = 0 ∧ (f'.a.card : ℝ) * (log n)
      ≤ log n.factorial + (f.score L) := by
  obtain ⟨f', hf'_bal, hf'_score⟩ := lowest_score f L
  exact ⟨f', hf'_bal, by rw [waste_eq f' hf'_bal]; linarith [score_eq hf'_bal L]⟩

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
  (statement := /-- We perform an initial factorization by taking the natural numbers between
  $n-n/M$ and $n$ repeated $M$ times, deleting those elements that are not $n/L$-smooth. -/)]
def Params.initial (P : Params) : Factorization P.n := {
  a := (replicate P.M (.Ico (P.n - P.n/P.M) P.n)).join.filter
    (fun m ↦ m ∈ (P.n/P.L).smoothNumbers)
  ha := fun m hm ↦ by
    simp only [Multiset.mem_filter, mem_join, mem_replicate] at hm
    obtain ⟨⟨_, ⟨_, rfl⟩, hs⟩, _⟩ := hm
    rw [Multiset.mem_Ico, tsub_le_iff_right] at hs
    grind
}

@[blueprint
  "initial-factorization-card"
  (statement := /-- The number of elements in this initial factorization is at most $n$. -/)]
theorem Params.initial.card (P : Params) : P.initial.a.card ≤ P.n := by
  calc Multiset.card (filter (fun m ↦ m ∈ (P.n / P.L).smoothNumbers)
      (replicate P.M (Multiset.Ico (P.n - P.n / P.M) P.n)).join)
    _ ≤ Multiset.card (replicate P.M (Multiset.Ico (P.n - P.n / P.M) P.n)).join :=
        card_le_card (filter_le _ _)
    _ = P.M * Multiset.card (Multiset.Ico (P.n - P.n / P.M) P.n) := by
        rw [card_join, map_replicate, sum_replicate, smul_eq_mul]
    _ = P.M * (P.n - (P.n - P.n / P.M)) := by congr 1; simp [Multiset.Ico]
    _ = P.M * (P.n / P.M) := by congr 1; exact Nat.sub_sub_self (Nat.div_le_self P.n P.M)
    _ ≤ P.n := Nat.mul_div_le P.n P.M

@[blueprint
  "initial-factorization-waste"
  (statement := /-- The total waste in this initial factorization is at most $n \log \frac{1}{1-1/M}$. -/)]
theorem Params.initial.waste (P : Params) : P.initial.waste ≤ P.n * log (1 - 1/P.M)⁻¹ := by sorry

@[blueprint
  "initial-factorization-large-prime-le"
  (statement := /-- A large prime $p > n/L$ cannot be in surplus. -/)
  (proof := /-- No such prime can be present in the factorization.-/)]
theorem Params.initial.balance_large_prime_le (P : Params) {p : ℕ} (hp : p > P.n / P.L) :
    P.initial.balance p ≤ 0 := by
  simp only [Factorization.balance, Factorization.sum, Params.initial, sub_nonpos]
  have : (map (fun m ↦ m.factorization p)
      (filter (fun m ↦ m ∈ (P.n / P.L).smoothNumbers)
      (replicate P.M (Multiset.Ico (P.n - P.n / P.M) P.n)).join)).sum = 0 :=
    sum_eq_zero fun x hx ↦ by
      simp only [Multiset.mem_map, Multiset.mem_filter] at hx
      obtain ⟨m, ⟨_, hsmooth⟩, rfl⟩ := hx
      rw [Nat.factorization_eq_zero_iff]; rw [Nat.mem_smoothNumbers'] at hsmooth; grind
  simp [this]

@[blueprint
  "initial-factorization-large-prime-le"
  (statement := /-- A large prime $p > n/L$ can be in deficit by at most $n/p$. -/)
  (proof := /-- This is the number of times $p$ can divide $n!$. -/)]
theorem Params.initial.balance_large_prime_ge (P : Params) {p : ℕ} (hp : p > P.n / P.L) :
    P.initial.balance p ≥ - (P.n/p) := by
  sorry

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
theorem Params.initial.balance_small_prime_ge (P : Params) {p : ℕ} (hp : p ≤ sqrt P.n) (hp' : p > P.L) : P.initial.balance p ≥ - P.M * (log P.n) := by
  sorry

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
theorem Solution_2 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in Filter.atTop, ∃ (t : ℕ) (a : Fin t → ℕ), ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n^2 ∧ t ≥ (n/2) - n/(2*log n) - ε * n / (log n) := by sorry


end Erdos392
