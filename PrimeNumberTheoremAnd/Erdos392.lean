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

open Finset Nat Real Multiset

@[blueprint
  "factorization-def"
  (statement := /--
  We work with (approximate) factorizations $a_1 \dots a_t$ of a factorial $n!$.
  -/)]
structure Factorization (n : ℕ) where
  a : Multiset ℕ
  ha : ∀ m ∈ a, m ≤ n
  hpos : ∀ m ∈ a, 0 < m

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

/-- The factorization of a multiset product equals the sum of factorizations. -/
private lemma factorization_multiset_prod (s : Multiset ℕ) (h : (0 : ℕ) ∉ s) (p : ℕ) :
    s.prod.factorization p = (s.map (·.factorization p)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have ht : 0 ∉ t := fun h' ↦ h (mem_cons_of_mem h')
    have ha : a ≠ 0 := fun h' ↦ h (h' ▸ Multiset.mem_cons_self 0 t)
    rw [factorization_mul ha (Multiset.prod_ne_zero ht), Finsupp.coe_add, Pi.add_apply, ih ht]

@[blueprint
  "balance-zero"
  (statement := /-- If a factorization has zero total imbalance, then it exactly factors $n!$.-/)]
theorem Factorization.zero_total_imbalance {n : ℕ} (f : Factorization n)
    (hf : f.total_imbalance = 0) : f.prod id = n.factorial := by
  have h_balance_zero : ∀ p ∈ (n + 1).primesBelow, f.balance p = 0 := fun p hp ↦ by
    have := Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _) |>.mp hf p hp; omega
  have h0 : (0 : ℕ) ∉ f.a := fun h ↦ (f.hpos 0 h).false
  simp only [prod, Multiset.map_id]
  refine eq_of_factorization_eq (Multiset.prod_ne_zero h0) (factorial_pos n).ne' fun p ↦ ?_
  by_cases hp : p.Prime <;> by_cases hp_le : p ≤ n
  · have hbal := h_balance_zero p (mem_primesBelow.mpr ⟨lt_succ_of_le hp_le, hp⟩)
    unfold balance sum at hbal
    simp only [factorization_multiset_prod f.a h0]; omega
  · simp only [factorization_multiset_prod f.a h0,
      factorization_factorial_eq_zero_of_lt (lt_of_not_ge hp_le)]
    exact Multiset.sum_eq_zero fun x hx ↦ by
      obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hx
      exact factorization_eq_zero_of_lt ((f.ha m hm).trans_lt (lt_of_not_ge hp_le))
  all_goals aesop

@[blueprint
  "waste-eq"
  (statement := /-- The waste of a factorization is equal to $t \log n - \log n!$, where $t$ is the
  number of elements.-/)]
theorem Factorization.waste_eq {n : ℕ} (f : Factorization n) (hf : f.total_imbalance = 0) :
    f.a.card * (Real.log n) = Real.log n.factorial + f.waste := by
  unfold waste sum
  have hlog : log (n.factorial : ℝ) = (f.a.map (fun m : ℕ ↦ log (m : ℝ))).sum := by
    rw [← f.zero_total_imbalance hf, prod, map_id, cast_multiset_prod, log_multiset_prod,
      Multiset.map_map]
    · rfl
    · exact fun x hx ↦ by
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hx; exact cast_ne_zero.mpr (f.hpos m hm).ne'
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Multiset.eq_zero_of_forall_notMem fun m hm ↦ (f.hpos m hm).ne' (le_zero.mp (f.ha m hm))]
  · have hn_pos : (0 : ℝ) < n := cast_pos.mpr (pos_of_ne_zero hn)
    rw [hlog, ← Multiset.sum_map_add]
    conv_lhs => rw [show f.a.card * log (n : ℝ) = (f.a.map (fun _ ↦ log (n : ℝ))).sum from
      by rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]]
    exact congrArg _ (Multiset.map_congr rfl fun m hm ↦ by
      rw [Real.log_div hn_pos.ne' (cast_ne_zero.mpr (f.hpos m hm).ne')]; ring)

@[blueprint
  "score-def"
  (statement := /--
  The score of a factorization (relative to a cutoff parameter $L$) is equal to its waste, plus $\log p$ for every surplus prime $p$, $\log (n/p)$ for every deficit prime above $L$, $\log L$ for every deficit prime below $L$ and an additional $\log n$ if one is not in total balance.
  -/)]
noncomputable def Factorization.score {n : ℕ} (f : Factorization n) (L : ℕ) : ℝ :=
  f.waste
  + (if f.total_imbalance > 0 then Real.log n else 0)
  + ∑ p ∈ (n+1).primesBelow,
    if f.balance p > 0 then (f.balance p) * (Real.log p)
    else if p ≤ L then (-f.balance p) * (Real.log L)
    else (-f.balance p) * (Real.log (n/p))

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
    (_hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') : Factorization n where
  a := (f.a.erase m).cons m'
  ha x hx := by
    simp only [Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hm'
    · exact f.ha x (Multiset.mem_of_mem_erase hx)
  hpos x hx := by
    simp only [Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hm'_pos
    · exact f.hpos x (Multiset.mem_of_mem_erase hx)

/-- The sum of a function `F` over a factorization after replacing `m` with `m'`
equals the original sum minus `F m` plus `F m'`. -/
lemma Factorization.replace_sum {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') {R : Type*} [AddCommGroup R] (F : ℕ → R) :
    (f.replace m m' hm hm' hm'_pos).sum F = f.sum F - F m + F m' := by
  simp only [replace, sum, Multiset.map_cons, Multiset.sum_cons]
  conv_rhs => rw [← cons_erase hm, Multiset.map_cons, Multiset.sum_cons]
  grind

/-- The balance of a prime `q` after replacing `m` with `m'` equals the original balance
minus the exponent of `q` in `m` plus the exponent of `q` in `m'`. -/
lemma Factorization.replace_balance {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') (q : ℕ) :
    (f.replace m m' hm hm' hm'_pos).balance q =
      f.balance q - m.factorization q + m'.factorization q := by
  simp only [balance, replace, sum, Multiset.map_cons, Multiset.sum_cons]
  conv_rhs => rw [← Multiset.cons_erase hm, Multiset.map_cons, Multiset.sum_cons]
  grind

/-- If we replace `m` with `m/p` where `p` divides `m`, the balance of `p` decreases by 1,
and the balance of any other prime remains unchanged. -/
lemma Factorization.replace_div_balance {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime) (q : ℕ) :
    let m' := m / p
    have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
    have hm'_pos : 0 < m' := div_pos (le_of_dvd (f.hpos m hm)
      (hp.dvd_iff_one_le_factorization (f.hpos m hm).ne' |>.mpr h_fac_pos)) hp.pos
    (f.replace m m' hm hm' hm'_pos).balance q = if q = p then f.balance q - 1 else f.balance q := by
  have hm_pos : 0 < m := f.hpos m hm
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have hp_dvd : p ∣ m := hp.dvd_iff_one_le_factorization hm_ne |>.mpr h_fac_pos
  have hm'_pos : 0 < m / p := div_pos (le_of_dvd hm_pos hp_dvd) hp.pos
  simp only [replace_balance, factorization_div hp_dvd]
  split_ifs with hq
  · subst hq
    simp only [Prime.factorization_self hp, Finsupp.coe_tsub, Pi.sub_apply]
    grind
  · have : p.factorization q = 0 := by rw [Prime.factorization hp]; grind
    simp only [this, Finsupp.coe_tsub, Pi.sub_apply, tsub_zero]
    grind

/-- Replacing `m` with `m/p` strictly decreases the total imbalance
when `p` has positive balance. -/
lemma Factorization.replace_div_total_imbalance {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime)
    (hp_mem : p ∈ (n + 1).primesBelow) (h_bal_pos : f.balance p > 0) :
    let m' := m / p
    have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
    have hm'_pos : 0 < m' := div_pos (le_of_dvd (f.hpos m hm)
      (hp.dvd_iff_one_le_factorization (f.hpos m hm).ne' |>.mpr h_fac_pos)) hp.pos
    (f.replace m m' hm hm' hm'_pos).total_imbalance < f.total_imbalance := by
  have hm_pos : 0 < m := f.hpos m hm
  have hp_dvd : p ∣ m := hp.dvd_iff_one_le_factorization hm_pos.ne' |>.mpr h_fac_pos
  have hm'_pos : 0 < m / p := div_pos (le_of_dvd hm_pos hp_dvd) hp.pos
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
    have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
    have hm'_pos : 0 < m' := div_pos (le_of_dvd (f.hpos m hm)
      (hp.dvd_iff_one_le_factorization (f.hpos m hm).ne' |>.mpr h_fac_pos)) hp.pos
    (f.replace m m' hm hm' hm'_pos).score L ≤ f.score L := by
  simp only
  set m' := m / p with hm'_def
  have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
  have hm_pos : 0 < m := f.hpos m hm
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have hp_dvd : p ∣ m := hp.dvd_iff_one_le_factorization hm_ne |>.mpr h_fac_pos
  have hm'_pos : 0 < m' := div_pos (le_of_dvd hm_pos hp_dvd) hp.pos
  have h_waste : (f.replace m m' hm hm' hm'_pos).waste ≤ f.waste + Real.log p := by
    have h_waste_eq : (f.replace m m' hm hm' hm'_pos).waste =
        f.waste - Real.log (n / m) + Real.log (n / m') :=
      replace_sum f m m' hm hm' hm'_pos (fun x ↦ Real.log (n / x))
    rw [h_waste_eq]
    by_cases hn : n = 0
    · simp only [hn, CharP.cast_eq_zero, zero_div, log_zero, sub_zero, add_zero,
      le_add_iff_nonneg_right, ge_iff_le]; positivity
    · have hn_pos : (0 : ℝ) < n := cast_pos.mpr (pos_of_ne_zero hn)
      have hm_pos : (0 : ℝ) < m := cast_pos.mpr (pos_of_ne_zero hm_ne)
      have hp_pos : (0 : ℝ) < p := cast_pos.mpr hp.pos
      have hm'_pos : (0 : ℝ) < m' := by
        simp only [hm'_def]
        have : p ≤ m := hp.dvd_iff_one_le_factorization hm_ne |>.mpr h_fac_pos |> le_of_dvd
          (pos_of_ne_zero hm_ne)
        exact cast_pos.mpr (div_pos this hp.pos)
      simp only [hm'_def]
      rw [Real.log_div (by linarith) (by linarith),
          Real.log_div (by linarith) (by linarith),
          cast_div hp_dvd (cast_ne_zero.mpr hp.ne_zero),
          Real.log_div (by linarith) (by linarith)]
      ring_nf
      rfl
  have h_pointwise : ∀ q ∈ (n + 1).primesBelow,
      (if (f.replace m m' hm hm' hm'_pos).balance q > 0
       then ((f.replace m m' hm hm' hm'_pos).balance q : ℝ) * Real.log q
       else if q ≤ L then -((f.replace m m' hm hm' hm'_pos).balance q : ℝ) * Real.log L
       else -((f.replace m m' hm hm' hm'_pos).balance q : ℝ) * Real.log (n / q)) ≤
      (if f.balance q > 0 then (f.balance q : ℝ) * Real.log q
       else if q ≤ L then -(f.balance q : ℝ) * Real.log L
       else -(f.balance q : ℝ) * Real.log (n / q)) -
      (if q = p then Real.log p else 0) := fun q _ ↦ by
    by_cases hq_eq_p : q = p
    · have h_bal : (f.replace m m' hm hm' hm'_pos).balance q = f.balance q - 1 := by
        rw [replace_div_balance f m p hm h_fac_pos hp q, if_pos hq_eq_p]
      have hbp : 0 < f.balance q := hq_eq_p ▸ _h_bal_pos
      simp only [hq_eq_p, ↓reduceIte]
      rcases Int.lt_or_eq_of_le hbp with h1 | h1
      · split_ifs with h2 h3 <;> simp_all; nlinarith
      · rw [← hq_eq_p, h_bal, ← h1]
        simp
    · have h_bal_eq : (f.replace m m' hm hm' hm'_pos).balance q = f.balance q := by
        rw [replace_div_balance f m p hm h_fac_pos hp q, if_neg hq_eq_p]
      simp only [hq_eq_p, ↓reduceIte, sub_zero, h_bal_eq, le_refl]
  have h_sum_term := Finset.sum_le_sum h_pointwise
  simp only [Finset.sum_ite] at h_sum_term
  simp only [Finset.sum_sub_distrib] at h_sum_term
  have h_sum_term' : ∑ q ∈ (n + 1).primesBelow,
      (if (f.replace m m' hm hm' hm'_pos).balance q > 0
       then ((f.replace m m' hm hm' hm'_pos).balance q : ℝ) * Real.log q
       else if q ≤ L then -((f.replace m m' hm hm' hm'_pos).balance q : ℝ) * Real.log L
       else -((f.replace m m' hm hm' hm'_pos).balance q : ℝ) * Real.log (n / q)) ≤
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
  unfold score at *
  split_ifs <;> norm_num at *
  · linarith
  · unfold total_imbalance at *; aesop
  · have hp_ge_one : (p : ℝ) ≥ 1 := one_le_cast.mpr hp.pos
    have hp_le_n : (p : ℝ) ≤ n := by
      exact_mod_cast le_of_lt_succ (lt_of_succ_le (succ_le_of_lt
        (lt_of_mem_primesBelow hp_mem)))
    linarith [Real.log_nonneg hp_ge_one, Real.log_le_log (cast_pos.mpr hp.pos) hp_le_n]
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
  exact ⟨_, replace_div_total_imbalance f m p hm h_fac_pos (prime_of_mem_primesBelow hp_mem)
    hp_mem hp_pos, replace_div_score_le f m p hm h_fac_pos (prime_of_mem_primesBelow hp_mem) hp_mem hp_pos L⟩

@[blueprint
  "score-lower-2"
  (statement := /-- If there is a prime $p$ in deficit larger than $L$, one can remove it without
  increasing the score.-/)
  (proof := /-- Add an additional factor of $p$ to the factorization.-/)]
theorem Factorization.lower_score_2 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0) :
    ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p, hp_mem, hp_gt_L, hp_balance⟩ := hf
  have hp := prime_of_mem_primesBelow hp_mem
  set f' : Factorization n := ⟨f.a + {p}, fun m hm => by
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact f.ha m hm
    · exact le_of_lt_succ (lt_of_mem_primesBelow hp_mem),
    fun m hm => by
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact f.hpos m hm
    · exact hp.pos⟩
  have h_balance_p : f'.balance p = f.balance p + 1 := by
    unfold balance sum
    simp only [show f'.a = f.a + {p} from rfl, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, Prime.factorization_self hp]
    omega
  have h_balance_q : ∀ q, q ≠ p → f'.balance q = f.balance q := fun q hq => by
    have hq_fac : p.factorization q = 0 := by rw [Prime.factorization hp]; simp [hq.symm]
    unfold balance sum
    simp only [show f'.a = f.a + {p} from rfl, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, hq_fac, add_zero]
  have h_total_imbalance : f'.total_imbalance < f.total_imbalance := by
    refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, hp_mem, by rw [h_balance_p]; omega⟩
    by_cases hq : q = p
    · subst hq; rw [h_balance_p]; omega
    · rw [h_balance_q q hq]
  have h_waste : f'.waste ≤ f.waste + Real.log (n / p) := by
    unfold waste sum
    simp only [show f'.a = f.a + {p} from rfl, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton]
    linarith
  have h_sum_q : ∀ q ∈ (n + 1).primesBelow, q ≠ p →
      (if f'.balance q > 0 then (f'.balance q : ℝ) * Real.log q
       else if q ≤ L then (-f'.balance q) * Real.log L else (-f'.balance q) * Real.log (n / q)) =
      (if f.balance q > 0 then (f.balance q : ℝ) * Real.log q
       else if q ≤ L then (-f.balance q) * Real.log L else (-f.balance q) * Real.log (n / q)) := by
    intro q _ hqp
    rw [h_balance_q q hqp]
  have h_term_p : (if f'.balance p > 0 then (f'.balance p : ℝ) * Real.log p
      else if p ≤ L then (-f'.balance p) * Real.log L else (-f'.balance p) * Real.log (n / p)) ≤
      (if f.balance p > 0 then (f.balance p : ℝ) * Real.log p
      else if p ≤ L then (-f.balance p) * Real.log L else (-f.balance p) * Real.log (n / p)) -
      Real.log (n / p) := by
    rw [h_balance_p]
    split_ifs <;> try linarith
    push_cast; ring_nf; norm_num
  have h_sum_term : ∑ q ∈ (n + 1).primesBelow,
      (if f'.balance q > 0 then (f'.balance q : ℝ) * Real.log q
       else if q ≤ L then (-f'.balance q) * Real.log L else (-f'.balance q) * Real.log (n / q)) ≤
      ∑ q ∈ (n + 1).primesBelow,
      (if f.balance q > 0 then (f.balance q : ℝ) * Real.log q
       else if q ≤ L then (-f.balance q) * Real.log L else (-f.balance q) * Real.log (n / q)) -
      Real.log (n / p) := by
    rw [Finset.sum_eq_add_sum_diff_singleton hp_mem, Finset.sum_eq_add_sum_diff_singleton hp_mem]
    have h_rest := Finset.sum_congr rfl fun x hx =>
      h_sum_q x (Finset.mem_sdiff.mp hx).1 (fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_singleton.mpr h))
    linarith
  have h_penalty : (if f'.total_imbalance > 0 then Real.log n else 0) ≤
      (if f.total_imbalance > 0 then Real.log n else 0) := by
    split_ifs <;> first | linarith | positivity
  have h_score : f'.score L ≤ f.score L := by
    unfold score
    linarith
  exact ⟨f', h_total_imbalance, h_score⟩

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
                else h2 p hp (lt_of_not_ge hpL); omega
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
    Factorization n, f'.total_imbalance = 0 ∧ (f'.a.card : ℝ) * (Real.log n)
      ≤ Real.log n.factorial + (f.score L) := by
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
  hpos := fun m hm ↦ by
    simp only [Multiset.mem_filter, mem_join, mem_replicate] at hm
    obtain ⟨_, hsmooth⟩ := hm
    exact pos_of_ne_zero (mem_smoothNumbers.mp hsmooth).1
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
    _ = P.M * (P.n / P.M) := by congr 1; exact Nat.sub_sub_self (div_le_self P.n P.M)
    _ ≤ P.n := mul_div_le P.n P.M

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
      rw [factorization_eq_zero_iff]; rw [mem_smoothNumbers'] at hsmooth; grind
  simp [this]

/-- For primes `p > √n`, the `p`-adic valuation of `n!` equals `⌊n/p⌋`. This follows from
Legendre's formula since `p² > n` implies all higher power terms vanish. -/
lemma Params.initial.factorial_factorization_eq_div {n p : ℕ} (hp : p.Prime) (h_sqrt : p > Real.sqrt n) :
    (n.factorial).factorization p = n / p := by
  have h_legendre : (factorial n).factorization p =
      ∑ k ∈ Finset.Ico 1 (log p n + 1), n / p ^ k := by
    rw [factorization_def]
    · have := Fact.mk hp; rw [padicValNat_factorial]; simp_all
    · exact hp
  have h_floor_zero : ∀ k ≥ 2, n / p ^ k = 0 := fun k hk ↦ by
    rw [div_eq_of_lt]
    rw [gt_iff_lt, Real.sqrt_lt (Nat.cast_nonneg n) (Nat.cast_nonneg p)] at h_sqrt
    norm_cast at *
    nlinarith [Nat.pow_le_pow_right hp.one_lt.le hk]
  rcases hlog : log p n with _ | _ | k <;> simp_all only [le_refl, Ico_eq_empty_of_le, sum_empty,
    log_eq_zero_iff, Ico_succ_singleton, Finset.sum_singleton, pow_one, Nat.div_eq_zero_iff]
  · rw [div_eq_of_lt (hlog.resolve_right hp.one_lt.not_ge)]
  · cases h_floor_zero (‹_› + 2) (by linarith) <;> simp_all +decide [log_eq_iff]; grind

@[blueprint
  "initial-factorization-large-prime-ge"
  (statement := /-- A large prime $p > n/L$ can be in deficit by at most $n/p$ (when $L > 0$). -/)
  (proof := /-- This is the number of times $p$ can divide $n!$. -/)]
theorem Params.initial.balance_large_prime_ge (P : Params) (hL : P.L > 0) {p : ℕ}
    (hp : p > P.n / P.L) : P.initial.balance p ≥ -(P.n / p) := by
  have hsum : (P.initial.a.map (·.factorization p)).sum = 0 := sum_eq_zero fun x hx ↦ by
    simp only [Multiset.mem_map, Params.initial, Multiset.mem_filter] at hx
    obtain ⟨m, ⟨_, hsmooth⟩, rfl⟩ := hx
    rw [factorization_eq_zero_iff, mem_smoothNumbers'] at *
    by_cases hprime : p.Prime
    · by_cases hdvd : p ∣ m
      · exact ((hsmooth p hprime hdvd).not_gt hp).elim
      · exact .inr (.inl hdvd)
    · exact .inl hprime
  have hfact : (P.n.factorial.factorization p : ℤ) ≤ P.n / p := by
    rcases eq_or_ne p 0 with rfl | _;
    · simp
    by_cases hprime : p.Prime
    · have hn_pos : (0 : ℝ) < P.n := by
        have := Nat.lt_of_lt_of_le (Nat.mul_pos hL hL) P.hL.le; exact_mod_cast this
      have hL_lt_sqrt : (P.L : ℝ) < Real.sqrt P.n := by
        rw [Real.lt_sqrt (Nat.cast_nonneg _)]; exact_mod_cast by nlinarith [P.hL]
      have hp_gt_sqrt : (p : ℝ) > Real.sqrt P.n := calc
        (p : ℝ) ≥ (P.n / P.L : ℕ) + 1 := by exact_mod_cast hp
        _ > P.n / P.L := by
          have hL_pos : (0 : ℝ) < P.L := by exact_mod_cast hL
          have h := Nat.div_add_mod P.n P.L
          have heq : (P.n : ℝ) = (P.n / P.L : ℕ) * P.L + (P.n % P.L : ℕ) := by
            have : P.L * (P.n / P.L) + P.n % P.L = P.n := h
            have := congrArg (· : ℕ → ℝ) this; simp only [Nat.cast_add, Nat.cast_mul] at this
            grind
          have hmod : ((P.n % P.L : ℕ) : ℝ) < P.L := by exact_mod_cast Nat.mod_lt P.n hL
          have hfloor : (P.n : ℝ) / P.L < (P.n / P.L : ℕ) + 1 := by
            rw [div_lt_iff₀ hL_pos, heq]; grind
          grind
        _ > Real.sqrt P.n := by
          rw [gt_iff_lt, lt_div_iff₀' (by exact_mod_cast hL : (0 : ℝ) < P.L)]
          calc P.L * Real.sqrt P.n < Real.sqrt P.n * Real.sqrt P.n := by nlinarith
            _ = P.n := Real.mul_self_sqrt hn_pos.le
      rw [factorial_factorization_eq_div hprime hp_gt_sqrt,
        Int.le_ediv_iff_mul_le (by exact_mod_cast hprime.pos)]
      exact_mod_cast Nat.div_mul_le_self P.n p
    · simp only [Nat.factorization_eq_zero_of_not_prime _ hprime, Nat.cast_zero]; grind
  simp only [Factorization.balance, Factorization.sum, hsum, Nat.cast_zero, zero_sub,
    neg_le_neg_iff, hfact]

/-- The number of multiples of `p` in `[A, B)` is at most `⌈(B - A)/p⌉`, computed as
`(B - A + p - 1) / p`. -/
lemma Params.initial.count_multiples_le (A B p : ℕ) (hp : p > 0) :
    (Finset.filter (p ∣ ·) (Finset.Ico A B)).card ≤ (B - A + p - 1) / p := by
  have hsub : Finset.filter (p ∣ ·) (.Ico A B) ⊆ image (p * ·) (.Ico ((A + p - 1) / p)
      ((B + p - 1) / p)) := fun m hm ↦ by
    obtain ⟨k, hk⟩ : ∃ k, m = p * k := by aesop
    simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_Ico, mem_image] at *
    exact ⟨k, ⟨le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by rw [tsub_lt_iff_left] <;> grind,
      lt_of_succ_le <| le_div_iff_mul_le hp |>.2 <| by rw [Nat.le_sub_iff_add_le] <;> grind⟩, hk.symm⟩
  refine (card_le_card hsub).trans ?_
  norm_num [card_image_of_injective _ fun x y hxy ↦ mul_left_cancel₀ hp.ne' hxy, card_Ico]
  rcases le_total B A with h | h <;> simp_all only [div_le_iff_le_mul_add_pred, tsub_le_iff_right]
  · rcases p with _ | _ | p <;> simp_all +arith [Nat.div_eq_of_lt]
    linarith [Nat.div_add_mod (A + p + 1) (p + 2), Nat.mod_lt (A + p + 1) (by grind : p + 2 > 0)]
  · linarith [div_add_mod (B - A + p - 1) p, mod_lt (B - A + p - 1) hp, div_add_mod (A + p - 1) p,
      mod_lt (A + p - 1) hp, Nat.sub_add_cancel h, Nat.sub_add_cancel (by grind : 1 ≤ p),
        Nat.sub_add_cancel (by grind : 1 ≤ B - A + p), Nat.sub_add_cancel (by grind : 1 ≤ A + p)]

/-- An auxiliary bound `M · ⌈(n/M)/p⌉ ≤ ⌊n/p⌋ + M`, where the ceiling is computed as
`(n/M + p - 1) / p`. -/
lemma Params.initial.count_bound_aux (n M p : ℕ) (hp : p > 0) : M * ((n / M + p - 1) / p) ≤ n / p + M := by
  have h_ceil_le : (n / M + p - 1) / p ≤ n / M / p + 1 :=
    le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by
      linarith [Nat.sub_add_cancel (show 1 ≤ n / M + p from one_le_iff_ne_zero.mpr (by grind)),
        div_add_mod (n / M) p, mod_lt (n / M) hp]
  have h_mul_div : M * (n / M / p) ≤ n / p := by
    rw [Nat.le_div_iff_mul_le] <;> nlinarith [div_mul_le_self n M, div_mul_le_self (n / M) p]
  nlinarith

/-- For primes `p > √n`, the sum of `p`-adic valuations in the initial factorization is bounded by
`M` times the count of multiples of `p` in `[n - n/M, n)`. -/
lemma Params.initial.sum_valuation_le_M_mul_interval_count (P : Params) {p : ℕ}
    (hp' : (p : ℝ) > Real.sqrt P.n) : (P.initial.a.map (·.factorization p)).sum ≤
      P.M * (Finset.filter (p ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card := by
  set S := Multiset.join (Multiset.replicate P.M (Multiset.Ico (P.n - P.n / P.M) P.n))
  have hle : P.initial.a ≤ S := by unfold Params.initial; aesop
  have hval : ∀ m ∈ S, m.factorization p ≤ if p ∣ m then 1 else 0 := fun m hm ↦ by
    have h1 : m.factorization p ≤ 1 := by
      by_cases hm_zero : m = 0
      · simp [hm_zero]
      · have hm_lt : (m : ℝ) < p ^ 2 := by
          have : (m : ℝ) < P.n := by
            simp only [S, Multiset.mem_join, Multiset.mem_replicate] at hm
            obtain ⟨_, ⟨_, rfl⟩, hs₂⟩ := hm; aesop
          nlinarith [sqrt_nonneg P.n, mul_self_sqrt (cast_nonneg P.n)]
        norm_cast at hm_lt
        exact le_of_not_gt fun h ↦ hm_lt.not_ge <|
          le_of_dvd (pos_of_ne_zero hm_zero) <| dvd_trans (pow_dvd_pow _ h) (ordProj_dvd _ _)
    split_ifs <;> simp_all [factorization_eq_zero_iff]
  have hsub : (P.initial.a.map (·.factorization p)).sum ≤ (S.map (·.factorization p)).sum :=
    Multiset.le_iff_exists_add.mp hle |>.elim fun k hk ↦ by simp [hk]
  calc (P.initial.a.map (·.factorization p)).sum
      _ ≤ (S.map (·.factorization p)).sum := hsub
      _ ≤ (S.map fun m ↦ if p ∣ m then 1 else 0).sum :=
          Multiset.sum_map_le_sum_map _ _ hval
      _ = P.M * (Finset.filter (p ∣ ·) (.Ico (P.n - P.n / P.M) P.n)).card := by
          simp only [S, map_join, sum_join, map_replicate, Multiset.sum_replicate, smul_eq_mul,
            Multiset.Ico, card_filter, sum_eq_multiset_sum]

@[blueprint
  "initial-factorization-medium-prime-le"
  (statement := /-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in surplus by at most $M$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_medium_prime_le (P : Params) {p : ℕ} (hp : p > Real.sqrt P.n) :
    P.initial.balance p ≤ P.M := by
  by_cases hprime : p.Prime
  · have : (P.initial.a.map (·.factorization p)).sum ≤ P.n / p + P.M := by
      calc (P.initial.a.map (·.factorization p)).sum
        _ ≤ P.M * (Finset.filter (p ∣ ·) (.Ico (P.n - P.n / P.M) P.n)).card :=
            sum_valuation_le_M_mul_interval_count P hp
        _ ≤ P.M * ((P.n / P.M + p - 1) / p) := mul_le_mul_left _ <| by
            convert count_multiples_le (P.n - P.n / P.M) P.n p hprime.pos using 1
            rw [Nat.sub_sub_self (div_le_self _ _)]
        _ ≤ P.n / p + P.M := by have := count_bound_aux P.n P.M p; grind
    simp only [Factorization.balance, Factorization.sum, factorial_factorization_eq_div hprime hp]
    omega
  · simp_all [Factorization.balance, Factorization.sum]

@[blueprint
  "initial-factorization-medium-prime-ge"
  (statement := /-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in deficit by at most $M$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_medium_prime_ge (P : Params) {p : ℕ} (hp : p ≤ P.n / P.L) (hp' : p > Real.sqrt P.n) : P.initial.balance p ≥ -P.M := by sorry

@[blueprint
  "initial-factorization-small-prime-le"
  (statement := /-- A small prime $p \leq \sqrt{n}$ can be in surplus by at most $M\log n$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_small_prime_le (P : Params) {p : ℕ} (hp : p ≤ Real.sqrt P.n) :
    P.initial.balance p ≤ P.M * (Real.log P.n) := by sorry

@[blueprint
  "initial-factorization-small-prime-ge"
  (statement := /-- A small prime $L < p \leq \sqrt{n}$ can be in deficit by at most $M\log n$.-/)
  (proof := /-- Routine computation using Legendre's formula.-/)]
theorem Params.initial.balance_small_prime_ge (P : Params) {p : ℕ} (hp : p ≤ Real.sqrt P.n)
    (hp' : p > P.L) : P.initial.balance p ≥ - P.M * (Real.log P.n) := by
  sorry

@[blueprint
  "initial-factorization-tiny-prime-ge"
  (statement := /-- A tiny prime $p \leq L$ can be in deficit by at most $M\log n + ML\pi(n)$.-/)
  (proof := /-- In addition to the Legendre calculations, one potentially removes factors of the
  form $plq$ with $l \leq L$ and $q \leq n$ a prime up to $M$ times each, with at most $L$ copies
  of $p$ removed at each factor.-/)]
theorem Params.initial.balance_tiny_prime_ge (P : Params) {p : ℕ} (hp : p ≤ P.L) :
    P.initial.balance p ≥ - P.M * (Real.log P.n) - P.M * P.L^2 * (primeCounting P.n) := by
  sorry

@[blueprint
  "initial-score"
  (statement := /-- The score of the initial factorization can be taken to be $o(n)$.-/)
  (proof := /-- Pick $M$ large depending on $\varepsilon$, then $L = M^2$, then assume $n$ large.
  Using the prime number theorem and Theorem \ref{initial-factorization-waste},
  Theorem \ref{initial-factorization-large-prime-le},
  Theorem \ref{initial-factorization-large-prime-ge},
  Theorem \ref{initial-factorization-medium-prime-le},
  Theorem \ref{initial-factorization-medium-prime-ge},
  Theorem \ref{initial-factorization-small-prime-le},
  Theorem \ref{initial-factorization-small-prime-ge}, and
  Theorem \ref{initial-factorization-tiny-prime-ge}, one can hold all losses to be of size
  $O(\varepsilon n)$.-/)]
theorem Params.initial.score (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in Filter.atTop, ∃ P : Params, P.n = n ∧ P.initial.score P.L ≤ ε * n := by
  sorry

@[blueprint
  "erdos-sol-1"
  (statement := /-- One can find a balanced factorization of $n!$ with cardinality at least $n - n / \log n - o(n / \log n)$.--/)
  (proof := /-- Combine Theorem \ref{initial-score} with Theorem \ref{card-bound} and the Stirling approximation.-/)]
theorem Solution_1 (ε : ℝ) (_hε : ε > 0) : ∀ᶠ n in Filter.atTop, ∃ f : Factorization n,
    f.total_imbalance = 0 ∧ f.a.card ≥ n - n / Real.log n - ε * n / Real.log n := by
  refine .of_forall fun n ↦ ⟨⟨Multiset.Ico 1 (n + 1), fun _ hm ↦ ?_, fun _ hm ↦ ?_⟩, ?_, ?_⟩
  · exact le_of_lt_succ (Multiset.mem_Ico.mp hm).2
  · exact (Multiset.mem_Ico.mp hm).1
  · rw [Factorization.total_imbalance]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    simp only [Factorization.balance, Factorization.sum, Int.natAbs_eq_zero, sub_eq_zero]
    norm_cast
    simp only [Multiset.Ico, ← sum_eq_multiset_sum]
    have : ∀ {m : ℕ}, m > 0 → m.factorial.factorization p = ∑ k ∈ Ico 1 (m + 1), k.factorization p := by
      intro m hm
      induction hm with
      | refl => simp [factorial]
      | step _ ih =>
        rw [factorial_succ, factorization_mul (by omega) (factorial_pos _).ne',
          Finsupp.coe_add, Pi.add_apply, ih, sum_Ico_succ_top (by omega : 1 ≤ _ + 1)]
        ring
    rcases n with _ | n
    · simp only [mem_primesBelow] at hp; exact (hp.2.one_lt.not_gt hp.1).elim
    · exact (this n.succ_pos).symm
  · simp only [Multiset.Ico, Finset.card_val, ge_iff_le, tsub_le_iff_right, card_Ico,
      add_tsub_cancel_right]
    have : (0 : ℝ) ≤ n / Real.log n ∧ (0 : ℝ) ≤ ε * n / Real.log n := ⟨by positivity, by positivity⟩
    linarith

@[blueprint
  "erdos-sol-2"
  (statement := /-- One can find a factor $n!$ into at least $n/2 - n / 2\log n - o(n / \log n)$
  numbers of size at most $n^2$.--/)
  (proof := /-- Group the factorization arising in Theorem \ref{erdos-sol-1} into pairs, using
  Theorem \ref{balance-zero}.-/)]
theorem Solution_2 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in Filter.atTop, ∃ (t : ℕ) (a : Fin t → ℕ), ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n ^ 2 ∧
        t ≥ (n / 2) - n / (2 * Real.log n) - ε * n / Real.log n := by
  norm_num
  refine ⟨2, fun b _hb ↦ ⟨b, (· + 1), ?_, ?_⟩⟩ <;> norm_num
  · exact prod_range_add_one_eq_factorial b ▸ (prod_range (· + 1)).symm
  · exact fun i ↦ ⟨by nlinarith [i.is_lt],
      le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (by linarith) (by positivity)) (by positivity)⟩

end Erdos392
