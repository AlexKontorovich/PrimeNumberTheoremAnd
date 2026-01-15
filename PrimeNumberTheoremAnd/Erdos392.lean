import Architect
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting
import PrimeNumberTheoremAnd.Consequences

namespace Erdos392

blueprint_comment /--
\section{Erdos problem 392}

The proof here is adapted from \url{https://www.erdosproblems.com/forum/thread/392\#post-2696} which
in turn is inspired by the arguments in \url{https://arxiv.org/abs/2503.20170}.
-/

open Finset Nat Real Multiset Asymptotics

@[blueprint
  "factorization-def"
  (statement := /--
  We work with (approximate) factorizations $a_1 \dots a_t$ of a factorial $n!$.
  -/)]
structure Factorization (n : ℕ) where
  a : Multiset ℕ
  ha : ∀ m ∈ a, m ≤ n
  hpos : ∀ m ∈ a, 0 < m

def Factorization.sum {n : ℕ} (f : Factorization n) {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) : R :=
  (f.a.map F).sum

def Factorization.prod {n : ℕ} (f : Factorization n) {R : Type*} [CommMonoid R]
    (F : ℕ → R) : R :=
  (f.a.map F).prod

@[blueprint
  "waste-def"
  (statement := /--
  The waste of a factorizations $a_1 \dots a_t$ is defined as $\sum_i \log (n / a_i)$.
  -/)]
noncomputable def Factorization.waste {n : ℕ} (f : Factorization n) : ℝ :=
  f.sum (fun m ↦ log (n / m : ℝ))

@[blueprint
  "balance-def"
  (statement := /--
  The balance of a factorization $a_1 \dots a_t$ at a prime $p$ is defined as the number of
  times $p$ divides $a_1 \dots a_t$, minus the number of times $p$ divides $n!$.
  -/)]
def Factorization.balance {n : ℕ} (f : Factorization n) (p : ℕ) : ℤ :=
  f.sum (fun m ↦ m.factorization p) - (n.factorial.factorization p:ℤ)

@[blueprint
  "balance-def"
  (statement := /--
  The total imbalance of a factorization $a_1 \dots a_t$ is the sum of absolute values of
  the balances at each prime.
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
  (statement := /-- If a factorization has zero total imbalance, then it exactly factors $n!$.-/)
  (latexEnv := "lemma")]
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
  number of elements.-/)
  (latexEnv := "lemma")]
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
  The score of a factorization (relative to a cutoff parameter $L$) is equal to its waste,
  plus $\log p$ for every surplus prime $p$, $\log (n/p)$ for every deficit prime above $L$,
  $\log L$ for every deficit prime below $L$ and an additional $\log n$ if one is not in
  total balance.
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
  -/)
  (latexEnv := "lemma")]
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
    (hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') {R : Type*} [AddCommGroup R]
    (F : ℕ → R) :
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

/-- Extends a factorization by adding a new factor `m`. -/
def Factorization.addFactor {n : ℕ} (f : Factorization n) (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) :
    Factorization n where
  a := cons m f.a
  ha x hx := by rcases mem_cons.mp hx with rfl | h <;> [exact hm; exact f.ha x h]
  hpos x hx := by rcases mem_cons.mp hx with rfl | h <;> [exact hm_pos; exact f.hpos x h]

/-- Adding a factor increases balance by the factor's factorization. -/
lemma Factorization.addFactor_balance {n : ℕ} (f : Factorization n) (m : ℕ) (hm : m ≤ n)
    (hm_pos : 0 < m) (p : ℕ) :
    (addFactor f m hm hm_pos).balance p = f.balance p + m.factorization p := by
  simp only [balance, sum, addFactor, Multiset.map_cons, Multiset.sum_cons, Int.natCast_add]; ring

/-- Adding a factor increases waste by `log (n / m)`. -/
lemma Factorization.addFactor_waste {n : ℕ} (f : Factorization n) (m : ℕ) (hm : m ≤ n)
    (hm_pos : 0 < m) : (addFactor f m hm hm_pos).waste = f.waste + Real.log (n / m) := by
  simp only [addFactor, waste, sum, Multiset.map_cons, Multiset.sum_cons, add_comm]

/-- The multiset of deficit primes at most `L`, each repeated `|balance p|` times. -/
def Factorization.deficitMultiset {n : ℕ} (f : Factorization n) (L : ℕ) : Multiset ℕ :=
  ((n + 1).primesBelow.filter (fun p ↦ p ≤ L ∧ f.balance p < 0)).val.bind
    fun p ↦ replicate (f.balance p).natAbs p

/-- Elements of the deficit multiset are primes at most `L`. -/
lemma Factorization.mem_deficitMultiset {n : ℕ} (f : Factorization n) (L : ℕ) (q : ℕ) :
    q ∈ deficitMultiset f L → q.Prime ∧ q ≤ L := by
  simp only [deficitMultiset, mem_bind, mem_val, Finset.mem_filter, forall_exists_index]
  intro x ⟨⟨hx, hx_le, _⟩, hq⟩
  rw [eq_of_mem_replicate hq]
  exact ⟨prime_of_mem_primesBelow hx, hx_le⟩

/-- Given a multiset of numbers `≤ L` with product `> n`, there exists a sub-multiset
whose product `m` satisfies `n / L < m ≤ n`. -/
lemma exists_submultiset_prod_between {n L : ℕ} (D : Multiset ℕ) (hL : 0 < L) (hn : 1 ≤ n)
    (hD_le : ∀ p ∈ D, p ≤ L) (hD_prod : D.prod > n) :
    ∃ M ≤ D, n < M.prod * L ∧ M.prod ≤ n := by
  induction D using Multiset.induction with
  | empty => aesop
  | cons p D ih =>
    by_cases hD_prod' : D.prod > n
    · obtain ⟨M, hM_le, hM⟩ := ih (fun q hq ↦ hD_le q (mem_cons_of_mem hq)) hD_prod'
      exact ⟨M, hM_le.trans (le_cons_self _ _), hM⟩
    · refine ⟨D, le_cons_self _ _, ?_, by omega⟩
      simp only [Multiset.prod_cons, gt_iff_lt] at hD_prod
      nlinarith [hD_le p (mem_cons_self p D)]

/-- A prime with negative balance is at most `n`. -/
lemma Factorization.deficit_implies_le_n {n : ℕ} (f : Factorization n) (p : ℕ)
    (hp : f.balance p < 0) : p ≤ n := by
  contrapose! hp; simp_all [factorization_factorial_eq_zero_of_lt hp, balance]

/-- The factorization of a product of primes at `p` equals the count of `p` in the multiset. -/
lemma factorization_prod_eq_count {D : Multiset ℕ} (hD : ∀ p ∈ D, p.Prime) (p : ℕ) :
    D.prod.factorization p = D.count p := by
  induction D using Multiset.induction with
  | empty => simp
  | cons q D ih =>
    have hq : q.Prime := hD q (mem_cons_self q D)
    have hD' : ∀ r ∈ D, r.Prime := fun r hr ↦ hD r (Multiset.mem_cons_of_mem hr)
    have hprod_ne : D.prod ≠ 0 :=
      fun h ↦ by rw [Multiset.prod_eq_zero_iff] at h; exact not_prime_zero (hD' 0 h)
    simp only [Multiset.prod_cons, factorization_mul hq.ne_zero hprod_ne, Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, Multiset.count_cons, ih hD']
    split_ifs <;> omega

/-- The product of the deficit multiset is positive. -/
lemma Factorization.deficitMultiset_prod_pos {n : ℕ} (f : Factorization n) (L : ℕ) :
    0 < (deficitMultiset f L).prod := by
  apply pos_of_ne_zero; simp only [deficitMultiset, primesBelow]; aesop

/-- The count of `p` in the deficit multiset equals `|balance p|` if `p` is a deficit prime
at most `L`, and `0` otherwise. -/
lemma Factorization.count_deficitMultiset {n : ℕ} (f : Factorization n) (L : ℕ) (p : ℕ) :
    (deficitMultiset f L).count p =
    if p ∈ (n + 1).primesBelow ∧ p ≤ L ∧ f.balance p < 0 then (f.balance p).natAbs else 0 := by
  simp only [deficitMultiset, count_bind, count_replicate]
  split_ifs with h <;> simp_all [sum_map_eq_nsmul_single p, and_self]
  simp [count_eq_one_of_mem (n + 1).primesBelow.nodup h.1, one_mul]

/-- Adding the full deficit multiset product to a factorization with no surplus primes and all
deficit primes at most `L` results in zero balance for all primes. -/
lemma Factorization.addFactor_deficit_balance_eq_zero {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) (h_m_def : m = (deficitMultiset f L).prod) :
    ∀ p, (addFactor f m hm hm_pos).balance p = 0 := fun p ↦ by
  by_cases hp : p.Prime <;> by_cases hp_le_L : p ≤ L <;> simp_all only [addFactor_balance]
  · simp_all only [CanonicallyOrderedAdd.multiset_prod_pos]
    simp only [factorization_prod_eq_count (fun q hq ↦ (mem_deficitMultiset f L q hq).1)]
    by_cases hp_def : f.balance p < 0 <;> simp_all only [cast_ite, cast_natAbs, Int.cast_eq,
      CharP.cast_eq_zero, count_deficitMultiset, abs_of_nonneg (le_of_not_gt hp_def)]
    · split_ifs <;> simp_all only [abs_of_neg hp_def, add_neg_cancel, primesBelow,
        Finset.mem_filter, Finset.mem_range, and_true]
      · linarith [h_deficit_large p hp_def, deficit_implies_le_n f p hp_def]
    · split_ifs <;> grind
  · simp_all only [CanonicallyOrderedAdd.multiset_prod_pos, not_le]
    have h_bal_zero : f.balance p = 0 :=
      le_antisymm (h_surplus p) (not_lt.mp fun h ↦ hp_le_L.not_ge (h_deficit_large p h))
    simp only [factorization_prod_eq_count (fun q hq ↦ (mem_deficitMultiset f L q hq).1),
      count_deficitMultiset]
    grind
  · simp_all [balance, sum]
  · simp_all [balance, sum]

/-- Case 1 of `lower_score_3`: if the product of deficit primes is `≤ n`, adding the full
deficit multiset yields a factorization with zero imbalance and lower score. -/
lemma Factorization.lower_score_3_case1 {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0)
    (h_prod : (deficitMultiset f L).prod ≤ n) :
    ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  set f' := addFactor f (deficitMultiset f L).prod h_prod (deficitMultiset_prod_pos f L) with hf'
  have h_zero_bal : ∀ p, f'.balance p = 0 :=
    addFactor_deficit_balance_eq_zero f L h_surplus h_deficit_large _ h_prod
      (deficitMultiset_prod_pos f L) rfl
  have hf'_imb : f'.total_imbalance = 0 :=
    Finset.sum_eq_zero fun p _ ↦ by simp [h_zero_bal p]
  obtain ⟨p₀, hp₀_mem, _, hp₀_bal⟩ := hf
  have hn_pos : 0 < n := (prime_of_mem_primesBelow hp₀_mem).pos.trans_le
    (Nat.lt_succ_iff.mp (mem_primesBelow.mp hp₀_mem).1)
  have hf'_score : f'.score L ≤ f.score L := by
    rw [score_eq (Finset.sum_eq_zero fun p _ ↦ by simp [h_zero_bal p])]
    unfold score
    split_ifs with h
    · rw [addFactor_waste]
      have h_log_ineq : Real.log (n / (deficitMultiset f L).prod) ≤ Real.log n :=
        Real.log_le_log (div_pos (Nat.cast_pos.mpr hn_pos)
          (Nat.cast_pos.mpr (deficitMultiset_prod_pos f L)))
          (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast deficitMultiset_prod_pos f L))
      have h_sum_nonneg : 0 ≤ ∑ p ∈ (n + 1).primesBelow,
          if f.balance p > 0 then (f.balance p : ℝ) * Real.log p
          else if p ≤ L then (-f.balance p : ℝ) * Real.log L
          else (-f.balance p : ℝ) * Real.log (n / p) :=
        Finset.sum_nonneg fun p hp ↦ by
          split_ifs with h1 h2
          · linarith [h_surplus p]
          · exact mul_nonneg (by simp; linarith [h_surplus p])
              (Real.log_nonneg (by norm_cast; linarith [(prime_of_mem_primesBelow hp).two_le]))
          · have h_bal_zero : f.balance p = 0 :=
              le_antisymm (h_surplus p) (not_lt.mp fun hlt ↦ h2 (h_deficit_large p hlt))
            simp [h_bal_zero]
      linarith
    · simp_all [total_imbalance]
  have h_imb_pos : 0 < f.total_imbalance :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hp₀_mem |>.trans_lt'
      (Int.natAbs_pos.mpr hp₀_bal.ne)
  exact ⟨f', hf'_imb ▸ h_imb_pos, hf'_score⟩

/-- Adding a submultiset `M` of deficit primes to a factorization reduces the total imbalance
by `M.card`. -/
lemma Factorization.addFactor_submultiset_total_imbalance {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (M : Multiset ℕ) (hM : M ≤ deficitMultiset f L)
    (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) (h_m_prod : m = M.prod) :
    (addFactor f m hm hm_pos).total_imbalance = f.total_imbalance - M.card := by
  have h_bal : ∀ p ∈ (n + 1).primesBelow,
      (addFactor f m hm hm_pos).balance p = f.balance p + M.count p := fun p _ ↦ by
    rw [addFactor_balance, h_m_prod, factorization_prod_eq_count]
    exact fun q hq ↦ (mem_deficitMultiset f L q (Multiset.mem_of_le hM hq)).1
  have h_ptwise : ∀ p ∈ (n + 1).primesBelow,
      (f.balance p + M.count p).natAbs = (f.balance p).natAbs - M.count p := fun p _ ↦ by
    have h_count_le : M.count p ≤ (f.balance p).natAbs := by
      have := Multiset.count_le_of_le p hM
      rw [count_deficitMultiset] at this; aesop
    have h_neg : f.balance p ≤ 0 := h_surplus p
    have h1 : ((f.balance p).natAbs : ℤ) = -f.balance p := Int.ofNat_natAbs_of_nonpos h_neg
    have h2 : ((f.balance p + M.count p).natAbs : ℤ) = -(f.balance p + M.count p) :=
      Int.ofNat_natAbs_of_nonpos (by omega : f.balance p + M.count p ≤ 0)
    omega
  have h_sum : ∑ p ∈ (n + 1).primesBelow, (f.balance p + M.count p).natAbs =
      ∑ p ∈ (n + 1).primesBelow, (f.balance p).natAbs -
        ∑ p ∈ (n + 1).primesBelow, M.count p := by
    have h_le : ∀ p ∈ (n + 1).primesBelow, M.count p ≤ (f.balance p).natAbs := fun p _ ↦ by
      have := Multiset.count_le_of_le p hM
      rw [count_deficitMultiset] at this; aesop
    rw [Finset.sum_congr rfl h_ptwise]
    have h_add : ∑ p ∈ (n + 1).primesBelow, ((f.balance p).natAbs - M.count p + M.count p) =
        ∑ p ∈ (n + 1).primesBelow, (f.balance p).natAbs :=
      Finset.sum_congr rfl fun x hx ↦ Nat.sub_add_cancel (h_le x hx)
    rw [Finset.sum_add_distrib] at h_add
    omega
  have h_card_eq : ∀ {M : Multiset ℕ}, (∀ p ∈ M, p ∈ (n + 1).primesBelow) →
      M.card = ∑ p ∈ (n + 1).primesBelow, M.count p := fun {M} hM ↦ by
    induction M using Multiset.induction with
    | empty => simp
    | cons a M ih =>
      simp only [Multiset.card_cons, Multiset.count_cons]
      rw [ih (fun p hp ↦ hM p (Multiset.mem_cons_of_mem hp)), Finset.sum_add_distrib,
          Finset.sum_ite_eq' _ a, if_pos (hM a (Multiset.mem_cons_self a M))]
  convert h_sum using 2
  · simp only [total_imbalance]
    exact Finset.sum_congr rfl fun p hp ↦ congrArg Int.natAbs (h_bal p hp)
  · exact h_card_eq fun p hp ↦ by
      obtain ⟨a, ha, ha'⟩ := Multiset.mem_bind.mp (Multiset.mem_of_le hM hp)
      rw [Multiset.mem_replicate] at ha'
      exact ha'.2 ▸ (Finset.mem_filter.mp ha).1

/-- The change in the score sum when one deficit prime `p` (with `p ≤ L`) has its balance
increased by 1 (still `≤ 0`). -/
lemma Factorization.score_sum_change {n : ℕ} (f f' : Factorization n) (L p : ℕ)
    (hp_mem : p ∈ (n + 1).primesBelow) (hp_le_L : p ≤ L) (h_bal_p : f.balance p < 0)
    (h_bal_p' : f'.balance p = f.balance p + 1)
    (h_bal_eq : ∀ q ∈ (n + 1).primesBelow, q ≠ p → f'.balance q = f.balance q) :
    (∑ q ∈ (n + 1).primesBelow,
      if f'.balance q > 0 then (f'.balance q) * Real.log q
      else if q ≤ L then (-f'.balance q) * Real.log L
      else (-f'.balance q) * Real.log (n / q)) -
    (∑ q ∈ (n + 1).primesBelow,
      if f.balance q > 0 then (f.balance q) * Real.log q
      else if q ≤ L then (-f.balance q) * Real.log L
      else (-f.balance q) * Real.log (n / q)) = -Real.log L := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single p]
  · simp only [h_bal_p', h_bal_p.not_gt, ↓reduceIte, hp_le_L, Int.cast_add, Int.cast_one]
    split_ifs with h
    · omega
    · ring
  · exact fun q hq hqp ↦ by simp only [h_bal_eq q hq hqp, sub_self]
  · exact absurd hp_mem

/-- The change in the score sum when a submultiset of deficit primes `M` is added. -/
lemma Factorization.score_sum_change_multiset {n : ℕ} (f f' : Factorization n) (L : ℕ)
    (M : Multiset ℕ) (hM_le : M ≤ deficitMultiset f L)
    (h_bal_eq : ∀ p ∈ (n + 1).primesBelow, f'.balance p = f.balance p + M.count p) :
    (∑ q ∈ (n + 1).primesBelow,
      if f'.balance q > 0 then (f'.balance q) * Real.log q
      else if q ≤ L then (-f'.balance q) * Real.log L
      else ↑(-f'.balance q) * Real.log (↑n / ↑q)) -
    (∑ q ∈ (n + 1).primesBelow,
      if f.balance q > 0 then ↑(f.balance q) * Real.log ↑q
      else if q ≤ L then (-f.balance q) * Real.log ↑L
      else ↑(-f.balance q) * Real.log (↑n / ↑q)) = -↑(M.card) * Real.log L := by
  have h_term : ∀ p ∈ (n + 1).primesBelow,
      (if f'.balance p > 0 then (f'.balance p : ℝ) * Real.log p
       else if p ≤ L then (-f'.balance p : ℝ) * Real.log L
       else (-f'.balance p : ℝ) * Real.log (n / p)) -
      (if f.balance p > 0 then (f.balance p : ℝ) * Real.log p
       else if p ≤ L then (-f.balance p : ℝ) * Real.log L
       else (-f.balance p : ℝ) * Real.log (n / p)) = -M.count p * Real.log L := by
    intro p hp
    by_cases hdef : f.balance p < 0
    · by_cases hL : p ≤ L <;> simp_all
      · split_ifs <;> try linarith
        have hcnt := Multiset.count_le_of_le p hM_le; rw [count_deficitMultiset] at hcnt
        have : M.count p ≤ (f.balance p).natAbs := by grind
        linarith [abs_of_neg hdef]
      · have : M.count p = 0 := Nat.eq_zero_of_le_zero <|
          (count_deficitMultiset f L p ▸ if_neg (by omega)).symm ▸
            Multiset.count_le_of_le _ hM_le
        aesop
    · have : M.count p = 0 := Nat.eq_zero_of_le_zero <|
        (count_deficitMultiset f L p ▸ if_neg (by tauto)).symm ▸
          Multiset.count_le_of_le _ hM_le
      aesop
  have h_card : ∑ p ∈ (n + 1).primesBelow, M.count p = M.card := by
    have aux : ∀ {S : Multiset ℕ}, (∀ p ∈ S, p ∈ (n + 1).primesBelow) →
        ∑ p ∈ (n + 1).primesBelow, S.count p = S.card := by
      intro S hS; induction S using Multiset.induction <;> aesop
    refine aux fun p hp ↦ ?_
    have hmem := Multiset.mem_of_le hM_le hp
    simp only [deficitMultiset, filter_val, mem_bind, Multiset.mem_filter] at hmem ⊢
    rcases hmem with ⟨a, ⟨ha, _⟩, hp⟩
    exact (Multiset.mem_replicate.mp hp).2 ▸ ha
  simp_all only [gt_iff_lt, Int.cast_add, Int.cast_natCast, neg_add_rev, neg_mul, Int.cast_neg,
    ← sum_sub_distrib, sum_neg_distrib]
  rw [← h_card, Nat.cast_sum, Finset.sum_mul]

/-- Adding a submultiset `M` of deficit primes reduces the score if `n < M.prod * L`. -/
lemma Factorization.score_le_of_add_submultiset {n : ℕ} (f : Factorization n) (L : ℕ)
    (M : Multiset ℕ) (hM_le : M ≤ deficitMultiset f L)
    (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) (h_m_prod : m = M.prod)
    (h_prod_gt : n < m * L) (hM_card_pos : 0 < M.card) (hL_ge_2 : 2 ≤ L) :
    (addFactor f m hm hm_pos).score L ≤ f.score L := by
  unfold score
  let f' := addFactor f m hm hm_pos
  have h_sum_eq : (∑ p ∈ (n + 1).primesBelow,
      if f'.balance p > 0 then (f'.balance p : ℝ) * Real.log p
      else if p ≤ L then -(f'.balance p : ℝ) * Real.log L
      else -(f'.balance p : ℝ) * Real.log (n / p)) -
    (∑ p ∈ (n + 1).primesBelow,
      if f.balance p > 0 then (f.balance p : ℝ) * Real.log p
      else if p ≤ L then -(f.balance p : ℝ) * Real.log L
      else -(f.balance p : ℝ) * Real.log (n / p)) = -M.card * Real.log L := by
    convert score_sum_change_multiset f f' L M hM_le (fun p _ ↦ ?_) using 1
    · norm_num [Finset.sum_ite]
    · simp only [f', addFactor_balance]
      rw [h_m_prod, factorization_prod_eq_count (fun q hq ↦
        (mem_deficitMultiset f L q (Multiset.mem_of_le hM_le hq)).1)]
  have h_waste_eq : f'.waste = f.waste + Real.log (n / m) := addFactor_waste f m hm hm_pos
  have h_score_diff : f'.waste + (∑ p ∈ (n + 1).primesBelow,
      if f'.balance p > 0 then (f'.balance p : ℝ) * Real.log p
      else if p ≤ L then -(f'.balance p : ℝ) * Real.log L
      else -(f'.balance p : ℝ) * Real.log (n / p)) ≤
    (f.waste + (∑ p ∈ (n + 1).primesBelow,
      if f.balance p > 0 then (f.balance p : ℝ) * Real.log p
      else if p ≤ L then -(f.balance p : ℝ) * Real.log L
      else -(f.balance p : ℝ) * Real.log (n / p))) + (Real.log n - Real.log m - Real.log L) := by
    rw [Real.log_div (by norm_cast; omega) (by positivity)] at h_waste_eq
    nlinarith [show (M.card : ℝ) ≥ 1 by norm_cast,
      log_nonneg (show (L : ℝ) ≥ 1 by norm_cast; omega),
        log_le_log (by positivity) (by norm_cast : (m : ℝ) ≤ n)]
  split_ifs with h_imb_pos h_imb_zero <;> norm_num at *
  · have h_log_sum : Real.log m + Real.log L ≥ Real.log n := by
      rw [← log_mul (by positivity) (by positivity)]
      exact log_le_log (by norm_cast; omega) (by norm_cast; omega)
    linarith
  · have h_bal_zero : ∀ p ∈ (n + 1).primesBelow, f.balance p = 0 := by
      unfold total_imbalance at h_imb_zero; aesop
    have h_deficit_empty : deficitMultiset f L = 0 := by unfold deficitMultiset; aesop
    simp [Multiset.le_zero.mp (h_deficit_empty ▸ hM_le)] at hM_card_pos
  · linarith [log_nonneg (show (m : ℝ) ≥ 1 by norm_cast),
      log_nonneg (show (L : ℝ) ≥ 1 by norm_cast; omega)]
  · refine h_score_diff.trans ?_
    norm_num [add_assoc]
    rw [← log_mul (by positivity) (by positivity), log_le_log_iff] <;> norm_cast <;> nlinarith

@[blueprint
  "score-lower-1"
  (statement := /-- If there is a prime $p$ in surplus, one can remove it without increasing the
  score. -/)
  (proof := /-- Locate a factor $a_i$ that contains the surplus prime $p$, then
  replace $a_i$ with $a_i/p$.-/)
  (latexEnv := "sublemma")]
theorem Factorization.lower_score_1 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p, hp_mem, hp_pos⟩ := hf
  obtain ⟨m, hm, h_fac_pos⟩ : ∃ m ∈ f.a, 0 < m.factorization p := by
    contrapose! hp_pos
    simp_all [balance, sum]
  exact ⟨_, replace_div_total_imbalance f m p hm h_fac_pos (prime_of_mem_primesBelow hp_mem)
    hp_mem hp_pos, replace_div_score_le f m p hm h_fac_pos (prime_of_mem_primesBelow hp_mem)
      hp_mem hp_pos L⟩

@[blueprint
  "score-lower-2"
  (statement := /-- If there is a prime $p$ in deficit larger than $L$, one can remove it without
  increasing the score.-/)
  (proof := /-- Add an additional factor of $p$ to the factorization.-/)
  (latexEnv := "sublemma")]
theorem Factorization.lower_score_2 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p, hp_mem, hp_gt_L, hp_balance⟩ := hf
  have hp := prime_of_mem_primesBelow hp_mem
  set f' : Factorization n := ⟨f.a + {p}, fun m hm => by
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact f.ha m hm
    · exact le_of_lt_succ (lt_of_mem_primesBelow hp_mem),
    fun m hm ↦ by
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact f.hpos m hm
    · exact hp.pos⟩
  have h_balance_p : f'.balance p = f.balance p + 1 := by
    unfold balance sum
    simp only [show f'.a = f.a + {p} from rfl, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, Prime.factorization_self hp]
    omega
  have h_balance_q : ∀ q, q ≠ p → f'.balance q = f.balance q := fun q hq ↦ by
    have hq_fac : p.factorization q = 0 := by rw [Prime.factorization hp]; simp [hq.symm]
    unfold balance sum
    simp only [show f'.a = f.a + {p} from rfl, Multiset.map_add, Multiset.sum_add,
      Multiset.map_singleton, Multiset.sum_singleton, hq_fac, add_zero]
  have h_total_imbalance : f'.total_imbalance < f.total_imbalance := by
    refine Finset.sum_lt_sum (fun q _ ↦ ?_) ⟨p, hp_mem, by rw [h_balance_p]; omega⟩
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
    have h_rest := Finset.sum_congr rfl fun x hx ↦
      h_sum_q x (Finset.mem_sdiff.mp hx).1
        (fun h ↦ (Finset.mem_sdiff.mp hx).2 (Finset.mem_singleton.mpr h))
    linarith
  have h_penalty : (if f'.total_imbalance > 0 then Real.log n else 0) ≤
      (if f.total_imbalance > 0 then Real.log n else 0) := by
    split_ifs <;> first | linarith | positivity
  have h_score : f'.score L ≤ f.score L := by
    unfold score
    linarith
  exact ⟨f', h_total_imbalance, h_score⟩

/-- Case 2a of `lower_score_3`: If `L > n` and there is a deficit prime, we can add it to reduce
the score. -/
lemma Factorization.lower_score_3_case2a {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) (hL_gt_n : L > n) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p, hp_mem, hp_le_L, hp_def⟩ := hf
  have hp_le_n : p ≤ n := Nat.lt_succ_iff.mp (mem_primesBelow.mp hp_mem).1
  have hp_pos : 0 < p := (prime_of_mem_primesBelow hp_mem).pos
  have hn_pos : 0 < n := hp_pos.trans_le hp_le_n
  have hp_prime : p.Prime := prime_of_mem_primesBelow hp_mem
  have h_imb : (addFactor f p hp_le_n hp_pos).total_imbalance = f.total_imbalance - 1 := by
    have hM : {p} ≤ deficitMultiset f L := Multiset.singleton_le.mpr <|
      Multiset.mem_bind.mpr ⟨p, Finset.mem_filter.mpr ⟨hp_mem, hp_le_L, hp_def⟩,
        Multiset.mem_replicate.mpr ⟨(Int.natAbs_pos.mpr hp_def.ne).ne', rfl⟩⟩
    simpa using addFactor_submultiset_total_imbalance f L h_surplus {p} hM p
      hp_le_n hp_pos (Multiset.prod_singleton (a := p)).symm
  have h_bal : (addFactor f p hp_le_n hp_pos).balance p = f.balance p + 1 := by
    rw [addFactor_balance, hp_prime.factorization, Finsupp.single_eq_same]; ring
  have h_bal_eq : ∀ q ∈ (n + 1).primesBelow, q ≠ p →
      (addFactor f p hp_le_n hp_pos).balance q = f.balance q := fun q hq hq_ne_p ↦ by
    rw [addFactor_balance, factorization_eq_zero_of_not_dvd, Int.ofNat_zero, add_zero]
    exact fun hdvd ↦
      hq_ne_p ((prime_dvd_prime_iff_eq (prime_of_mem_primesBelow hq) hp_prime).mp hdvd)
  have h_score_sum := score_sum_change f (addFactor f p hp_le_n hp_pos) L p hp_mem hp_le_L hp_def
    h_bal h_bal_eq
  have h_waste := addFactor_waste f p hp_le_n hp_pos
  have h_total_imb_pos : f.total_imbalance > 0 :=
    (Int.natAbs_pos.mpr hp_def.ne).trans_le
      (Finset.single_le_sum (fun q _ ↦ (Int.natAbs (f.balance q)).zero_le) hp_mem)
  have h_imbalance_penalty :
      (addFactor f p hp_le_n hp_pos).score L ≤ f.score L + Real.log (n / p) - Real.log L := by
    unfold score at *
    have h_log_n : log (n : ℝ) ≥ 0 := log_nonneg (by exact_mod_cast hn_pos)
    split_ifs at * <;> linarith [h_score_sum, h_waste, h_total_imb_pos]
  refine ⟨addFactor f p hp_le_n hp_pos, ?_, h_imbalance_penalty.trans ?_⟩
  · exact h_imb ▸ sub_lt h_total_imb_pos one_pos
  · rw [add_sub_assoc]
    refine add_le_of_nonpos_right (sub_nonpos_of_le (log_le_log (by positivity) ?_))
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < p)]
    have h1 : (n : ℝ) * 1 ≤ n * p := by
      exact_mod_cast mul_le_mul_left n <| one_le_iff_ne_zero.mpr hp_pos.ne'
    have h2 : (n : ℝ) * p < L * p := by exact_mod_cast mul_lt_mul_of_pos_right hL_gt_n hp_pos
    linarith

/-- Case 2b of `lower_score_3`: If `L ≤ n` and the product of deficit primes is `> n`,
we can find a submultiset to add that reduces the score. -/
lemma Factorization.lower_score_3_case2b {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0)
    (h_prod : n < (deficitMultiset f L).prod) (hL_le_n : L ≤ n) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  obtain ⟨p₀, hp₀_mem, hp₀_le, hp₀_bal⟩ := hf
  have hp₀ := prime_of_mem_primesBelow hp₀_mem
  obtain ⟨M, hM_sub, hM_lb, hM_ub⟩ := exists_submultiset_prod_between (deficitMultiset f L)
    (hp₀.pos.trans_le hp₀_le) ((hp₀.pos.trans_le hp₀_le).trans_le hL_le_n)
      (fun p hp ↦ (mem_deficitMultiset f L p hp).2) h_prod
  refine ⟨addFactor f M.prod hM_ub (pos_of_ne_zero fun h ↦ by grind), ?_, ?_⟩
  · have h_imb := addFactor_submultiset_total_imbalance f L h_surplus M hM_sub
      M.prod hM_ub (pos_of_ne_zero fun h ↦ by grind) rfl
    refine h_imb ▸ sub_lt ?_ <| card_pos.mpr (by grind)
    exact pos_of_ne_zero fun h ↦
      hp₀_bal.ne <| by have := sum_eq_zero_iff.mp h _ hp₀_mem; grind
  · exact score_le_of_add_submultiset f L M hM_sub M.prod hM_ub (by grind) rfl hM_lb
      (card_pos.mpr (by grind)) <| hp₀.two_le.trans hp₀_le

/-- The clean case of `lower_score_3`, combining the three subcases. -/
lemma Factorization.lower_score_3_clean {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  by_cases h_prod : (deficitMultiset f L).prod ≤ n
  · exact lower_score_3_case1 f L h_surplus h_deficit_large hf h_prod
  by_cases hL_gt_n : n < L
  · exact lower_score_3_case2a f L h_surplus hf hL_gt_n
  · exact lower_score_3_case2b f L h_surplus h_deficit_large hf
      (not_le.mp h_prod) (not_lt.mp hL_gt_n)

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
  any further; add this product to the factorization, increasing the waste by at most $\log L$.-/)
  (latexEnv := "sublemma")]
theorem Factorization.lower_score_3 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  by_cases h1 : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0
  · exact lower_score_1 f L h1
  by_cases h2 : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0
  · exact lower_score_2 f L h2
  push_neg at h1 h2
  refine lower_score_3_clean f L (fun p ↦ ?_) (fun p hp ↦ ?_) hf
  · by_cases hp : p.Prime
    · by_cases hp' : p ≤ n
      · exact h1 p <| mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hp', hp⟩
      · have := fun m hm ↦ factorization_eq_zero_of_not_dvd fun h ↦ hp' <| (f.ha m hm).trans'
          (le_of_dvd (f.hpos m hm) h); simp [balance, sum, map_congr rfl this]
    · simp [balance, sum, factorization_eq_zero_of_not_prime _ hp]
  · have hp_prime : p.Prime := of_not_not fun hnp ↦ hp.ne <| by simp [balance, sum,
      factorization_eq_zero_of_not_prime _ hnp]
    exact not_lt.mp fun hpL ↦ hp.not_ge <| h2 p (mem_primesBelow.mpr ⟨Nat.lt_succ_of_le
      (deficit_implies_le_n f p hp), hp_prime⟩) hpL

@[blueprint
  "score-lowest"
  (statement := /-- One can bring any factorization into balance without increasing the score. -/)
  (proof := /-- Apply strong induction on the total imbalance of the factorization and use the
  previous three sublemmas.-/)
  (latexEnv := "lemma")]
theorem Factorization.lowest_score {n : ℕ} (f : Factorization n) (L : ℕ) :
    ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ f.score L := by
  induction h : f.total_imbalance using Nat.strong_induction_on generalizing f with
  | _ k ih =>
    obtain rfl | hk := k.eq_zero_or_pos
    · exact ⟨f, h, le_refl _⟩
    · have step : ∀ g : Factorization n, g.total_imbalance < k →
          ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ g.score L :=
        fun g hg ↦ ih g.total_imbalance (h ▸ hg) g rfl
      have reduce (f₁ : Factorization n) (hlt : f₁.total_imbalance < f.total_imbalance)
          (hle : f₁.score L ≤ f.score L) :
          ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ f.score L :=
        let ⟨f', hbal, hle'⟩ := step f₁ (h ▸ hlt); ⟨f', hbal, hle'.trans hle⟩
      by_cases h1 : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0
      · exact let ⟨f₁, hlt, hle⟩ := lower_score_1 f L h1; reduce f₁ hlt hle
      · by_cases h2 : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0
        · exact let ⟨f₁, hlt, hle⟩ := lower_score_2 f L h2; reduce f₁ hlt hle
        · have h3 : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0 := by
            push_neg at h1 h2; by_contra hc; push_neg at hc
            exact hk.ne' <| h ▸ sum_eq_zero fun p hp ↦ by
              have := h1 p hp; have := if hpL : p ≤ L then hc p hp hpL
                else h2 p hp (lt_of_not_ge hpL); omega
          exact let ⟨f₁, hlt, hle⟩ := lower_score_3 f L h3; reduce f₁ hlt hle

@[blueprint
  "card-bound"
  (statement := /--
  Starting from any factorization $f$, one can find a factorization $f'$ in balance whose
  cardinality is at most $\log n!$ plus the score of $f$, divided by $\log n$.-/)
  (proof := /-- Combine Lemma \ref{score-lowest}, Lemma \ref{score-eq}, and
  Lemma \ref{waste-eq}.-/)
  (latexEnv := "proposition")]
theorem Factorization.card_bound {n : ℕ} (f : Factorization n) (L : ℕ) : ∃ f' :
    Factorization n, f'.total_imbalance = 0 ∧ (f'.a.card : ℝ) * (Real.log n)
      ≤ Real.log n.factorial + (f.score L) := by
  obtain ⟨f', hf'_bal, hf'_score⟩ := lowest_score f L
  exact ⟨f', hf'_bal, by rw [waste_eq f' hf'_bal]; linarith [score_eq hf'_bal L]⟩

@[blueprint
  "params-set"
  (statement := /-- Now let $M,L$ be additional parameters with $n > L^2$; we also need the minor
  variant $\lfloor n/L \rfloor > \sqrt{n}$. -/)]
structure Params where
  n : ℕ
  M : ℕ
  L : ℕ
  hM : M > 1
  hL_pos : L > 0
  hL : n > L * L
  hL' : (n/L:ℕ) > Real.sqrt n  -- almost implied by hL, but not quite

@[blueprint
  "initial-factorization-def"
  (statement := /-- We perform an initial factorization by taking the natural numbers between
  $n-n/M$ (inclusive) and $n$ (exclusive) repeated $M$ times, deleting those elements that are
  not $n/L$-smooth (i.e., have a prime factor greater than or equal to $n/L$). -/)]
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
  (statement := /-- The number of elements in this initial factorization is at most $n$. -/)
  (latexEnv := "sublemma")]
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

/-- Elements of the initial factorization lie in the interval `[n - n/M, n)`. -/
lemma Params.initial.mem_range (P : Params) (m : ℕ) (hm : m ∈ P.initial.a) :
    P.n - P.n / P.M ≤ m ∧ m < P.n := by
  simp only [initial, Multiset.mem_filter, mem_join, mem_replicate] at hm
  obtain ⟨⟨_, ⟨_, rfl⟩, hs⟩, _⟩ := hm
  exact Multiset.mem_Ico.mp hs

/-- For elements `m` in the initial factorization, `n/m ≤ (1 - 1/M)⁻¹`. -/
lemma Params.initial.div_le (P : Params) (m : ℕ) (hm : m ∈ P.initial.a) :
    (P.n : ℝ) / m ≤ (1 - 1 / (P.M : ℝ))⁻¹ := by
  have ⟨hlo, hhi⟩ := mem_range P m hm
  have hM_pos : (0 : ℝ) < P.M := Nat.cast_pos.mpr (Nat.zero_lt_of_lt P.hM)
  have h_denom_pos : 0 < 1 - 1 / (P.M : ℝ) := by
    rw [sub_pos, div_lt_one hM_pos]; exact Nat.one_lt_cast.mpr P.hM
  have hn_pos : (0 : ℝ) < P.n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (P.initial.hpos m hm) hhi.le)
  have hlo' : (P.n : ℝ) - P.n / P.M ≤ m := by
    calc (P.n : ℝ) - P.n / P.M ≤ P.n - (P.n / P.M : ℕ) := by gcongr; exact Nat.cast_div_le
      _ = ((P.n - P.n / P.M : ℕ) : ℝ) := by rw [Nat.cast_sub (Nat.div_le_self ..)]
      _ ≤ m := by exact_mod_cast hlo
  calc (P.n : ℝ) / m ≤ P.n / (P.n - P.n / P.M) := by
        gcongr; rw [sub_pos]; exact div_lt_self hn_pos <| one_lt_cast.mpr P.hM
    _ = P.n / (P.n * (1 - 1 / (P.M : ℝ))) := by rw [mul_sub, mul_one, mul_one_div]
    _ = (1 - 1 / (P.M : ℝ))⁻¹ := by rw [div_mul_eq_div_div, div_self hn_pos.ne', one_div]

@[blueprint
  "initial-factorization-waste"
  (statement := /-- The total waste in this initial factorization is at most
  $n \log \frac{1}{1-1/M}$. -/)
  (latexEnv := "lemma")]
theorem Params.initial.waste (P : Params) :
    P.initial.waste ≤ P.n * log (1 - 1/(P.M : ℝ))⁻¹ := by
  unfold Factorization.waste Factorization.sum
  have hM_pos : (0 : ℝ) < P.M := cast_pos.mpr (Nat.zero_lt_of_lt P.hM)
  have h_denom_pos : 0 < 1 - 1 / (P.M : ℝ) := by
    rw [sub_pos, div_lt_one hM_pos]; exact one_lt_cast.mpr P.hM
  have h_inv_ge_one : 1 ≤ (1 - 1 / (P.M : ℝ))⁻¹ := by
    rw [one_le_inv₀ h_denom_pos]; linarith [one_div_pos.mpr hM_pos]
  have h_each : ∀ m ∈ P.initial.a, log ((P.n : ℝ) / m) ≤ log (1 - 1 / (P.M : ℝ))⁻¹ :=
    fun m hm ↦ log_le_log (div_pos (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (P.initial.hpos m hm)
      (mem_range P m hm).2.le)) (Nat.cast_pos.mpr (P.initial.hpos m hm))) (div_le P m hm)
  calc (P.initial.a.map fun (m : ℕ) ↦ log ((P.n : ℝ) / m)).sum
      ≤ P.initial.a.card * log (1 - 1 / (P.M : ℝ))⁻¹ := by
        rw [← nsmul_eq_mul, ← Multiset.card_map (fun (m : ℕ) ↦ log ((P.n : ℝ) / m)) P.initial.a]
        refine Multiset.sum_le_card_nsmul _ _ fun x hx ↦ ?_
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hx
        exact h_each m hm
    _ ≤ P.n * log (1 - 1 / (P.M : ℝ))⁻¹ := by
        gcongr
        · exact Real.log_nonneg h_inv_ge_one
        · exact_mod_cast card P

@[blueprint
  "initial-factorization-large-prime-le"
  (statement := /-- A large prime $p \geq n/L$ cannot be in surplus. -/)
  (proof := /-- No such prime can be present in the factorization.-/)
  (latexEnv := "sublemma")]
theorem Params.initial.balance_large_prime_le (P : Params) {p : ℕ} (hp : p ≥ P.n / P.L) :
    P.initial.balance p ≤ 0 := by
  simp only [Factorization.balance, Factorization.sum, initial, sub_nonpos]
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
lemma Params.initial.factorial_factorization_eq_div {n p : ℕ} (hp : p.Prime)
    (h_sqrt : p > Real.sqrt n) :
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
  (statement := /-- A large prime $p \geq n/L$ can be in deficit by at most $n/p$. -/)
  (proof := /-- This is the number of times $p$ can divide $n!$. -/)
  (latexEnv := "sublemma")]
theorem Params.initial.balance_large_prime_ge (P : Params) {p : ℕ}
    (hp : p ≥ P.n / P.L) : P.initial.balance p ≥ -(P.n / p) := by
  have hsum : (P.initial.a.map (·.factorization p)).sum = 0 := sum_eq_zero fun x hx ↦ by
    simp only [Multiset.mem_map, initial, Multiset.mem_filter] at hx
    obtain ⟨m, ⟨_, hsmooth⟩, rfl⟩ := hx
    rw [factorization_eq_zero_iff, mem_smoothNumbers'] at *
    by_cases hprime : p.Prime
    · by_cases hdvd : p ∣ m
      · exact ((hsmooth p hprime hdvd).not_ge hp).elim
      · exact .inr (.inl hdvd)
    · exact .inl hprime
  have hfact : (P.n.factorial.factorization p : ℤ) ≤ P.n / p := by
    rcases eq_or_ne p 0 with rfl | -; · simp
    by_cases hprime : p.Prime
    · have hn_pos : (0 : ℝ) < P.n := by
        have := Nat.lt_of_lt_of_le (Nat.mul_pos P.hL_pos P.hL_pos) P.hL.le; exact_mod_cast this
      have hL_lt_sqrt : (P.L : ℝ) < Real.sqrt P.n := by
        rw [Real.lt_sqrt (Nat.cast_nonneg _)]; exact_mod_cast by nlinarith [P.hL]
      have hp_gt_sqrt : (p : ℝ) > Real.sqrt P.n := calc
        (p : ℝ) ≥ (P.n / P.L : ℕ) := by exact_mod_cast hp
        _ > Real.sqrt P.n := P.hL'
      rw [factorial_factorization_eq_div hprime hp_gt_sqrt,
        Int.le_ediv_iff_mul_le (by exact_mod_cast hprime.pos)]
      exact_mod_cast Nat.div_mul_le_self P.n p
    · simp only [Nat.factorization_eq_zero_of_not_prime _ hprime, Nat.cast_zero]; positivity
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
    exact ⟨k, ⟨le_of_lt_succ <| Nat.div_lt_of_lt_mul <|
      by rw [tsub_lt_iff_left] <;> grind,
      lt_of_succ_le <| le_div_iff_mul_le hp |>.2 <|
        by rw [Nat.le_sub_iff_add_le] <;> grind⟩, hk.symm⟩
  refine (card_le_card hsub).trans ?_
  norm_num [card_image_of_injective _ fun x y hxy ↦ mul_left_cancel₀ hp.ne' hxy, card_Ico]
  rcases le_total B A with h | h <;> simp_all only [div_le_iff_le_mul_add_pred, tsub_le_iff_right]
  · rcases p with _ | _ | p <;> simp_all +arith [Nat.div_eq_of_lt]
    linarith [Nat.div_add_mod (A + p + 1) (p + 2), Nat.mod_lt (A + p + 1) (by grind : p + 2 > 0)]
  · linarith [div_add_mod (B - A + p - 1) p, mod_lt (B - A + p - 1) hp,
      div_add_mod (A + p - 1) p, mod_lt (A + p - 1) hp, Nat.sub_add_cancel h,
      Nat.sub_add_cancel (by grind : 1 ≤ p), Nat.sub_add_cancel (by grind : 1 ≤ B - A + p),
      Nat.sub_add_cancel (by grind : 1 ≤ A + p)]

/-- An auxiliary bound `M · ⌈(n/M)/p⌉ ≤ ⌊n/p⌋ + M`, where the ceiling is computed as
`(n/M + p - 1) / p`. -/
lemma Params.initial.count_bound_aux (n M p : ℕ) (hp : p > 0) :
    M * ((n / M + p - 1) / p) ≤ n / p + M := by
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
  have hle : P.initial.a ≤ S := by unfold initial; aesop
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
  (proof := /-- Routine computation using Legendre's formula.-/)
  (latexEnv := "sublemma")]
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

/-- If `√n < p < n/L` and `p ∣ m` with `0 < m < n`, then `m` is `(n/L)`-smooth. -/
lemma Params.initial.smooth_of_multiple (P : Params) {p m : ℕ} (hp : p > Real.sqrt P.n)
    (hps : p < P.n / P.L) (hm : m < P.n) (hm0 : m ≠ 0) (hpm : p ∣ m) :
    m ∈ smoothNumbers (P.n / P.L) := by
  contrapose! hps
  refine le_of_not_gt fun h ↦ hps ?_
  obtain ⟨q, hq, hqm, hqn⟩ : ∃ q, Prime q ∧ q ∣ m ∧ q ≥ P.n / P.L := by
    simp_all [smoothNumbers]
  have : p * q > P.n := by
    rw [gt_iff_lt, Real.sqrt_lt] at hp <;> norm_cast at * <;> nlinarith
  exact absurd (le_of_dvd (pos_of_ne_zero hm0) (Coprime.mul_dvd_of_dvd_of_dvd
    (coprime_comm.mp <| hq.coprime_iff_not_dvd.mpr <| not_dvd_of_pos_of_lt
      (pos_of_ne_zero <| by grind) <| by nlinarith [div_mul_le_self P.n P.L])
        hpm hqm)) (by omega)

/-- For `√n < p` prime and `p ∣ m` with `0 < m < n`, we have `ν_p(m) = 1` since `p² > n ≥ m`. -/
lemma Params.initial.valuation_eq_one (P : Params) {p m : ℕ} (hp : p.Prime)
    (hp' : p > Real.sqrt P.n) (hm : m < P.n) (hm0 : m ≠ 0) (hpm : p ∣ m) :
    m.factorization p = 1 := by
  have : p ^ 2 ∣ m → False := fun h ↦ by
    have := le_of_dvd (pos_of_ne_zero hm0) h
    rw [gt_iff_lt, Real.sqrt_lt] at hp' <;> norm_cast at * <;> grind
  exact le_antisymm (Nat.le_of_not_lt fun h ↦
    this <| dvd_trans (pow_dvd_pow _ h) <| ordProj_dvd _ _)
      (Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp <| by aesop)

/-- The interval `[n - n/M, n)` contains at least `⌊n/M⌋/p` multiples of `p`. -/
lemma Params.initial.count_multiples_lower_bound (n M p : ℕ) (hM : M > 0) (hp : p > 0) :
    M * (Finset.filter (p ∣ ·) (Finset.Ico (n - n / M) n)).card + M ≥ n / p := by
  have h1 : (Finset.filter (p ∣ ·) (Finset.Ico (n - n / M) n)).card ≥ (n / M) / p := by
    have hsup : Finset.filter (p ∣ ·) (Finset.Ico (n - n / M) n) ⊇
        Finset.image (p * ·) (Finset.Ico ((n - n / M + p - 1) / p) ((n + p - 1) / p)) := fun _ hx ↦ by
      simp +zetaDelta only [gt_iff_lt, mem_image, Finset.mem_Ico, Finset.mem_filter,
        tsub_le_iff_right] at *
      obtain ⟨a, ⟨ha₁, ha₂⟩, rfl⟩ := hx
      refine ⟨⟨?_, ?_⟩, by norm_num⟩
      · nlinarith [div_add_mod (n - n / M + p - 1) p, mod_lt (n - n / M + p - 1) hp,
          Nat.sub_add_cancel (div_le_self n M), Nat.sub_add_cancel (succ_le_of_lt (by omega :
            0 < n - n / M + p))]
      · nlinarith [div_mul_le_self (n + p - 1) p, Nat.sub_add_cancel (by omega : 1 ≤ n + p)]
    refine le_trans ?_ (Finset.card_mono hsup)
    rw [Finset.card_image_of_injective _ fun _ _ h ↦ mul_left_cancel₀ hp.ne' h]
    simp +arith only [card_Ico, div_le_iff_le_mul_add_pred hp]; zify
    repeat rw [Nat.cast_sub] <;> push_cast <;> try omega
    · nlinarith [Int.mul_ediv_add_emod (n + p - 1) p,
        Int.emod_nonneg (n + p - 1) (by omega : (p : ℤ) ≠ 0),
        Int.emod_lt_of_pos (n + p - 1) (by omega : (p : ℤ) > 0),
        Int.mul_ediv_add_emod (p + (n - n / M) - 1) p,
        Int.emod_nonneg (p + (n - n / M) - 1) (by omega : (p : ℤ) ≠ 0),
        Int.emod_lt_of_pos (p + (n - n / M) - 1) (by omega : (p : ℤ) > 0),
        div_mul_le_self n M]
    · exact div_le_self _ _
    · rw [div_le_iff_le_mul_add_pred hp]
      rcases p with _ | _ | p <;> simp_all [succ_mul]
      nlinarith [div_add_mod (n + (p + 1)) (p + 1 + 1), mod_lt (n + (p + 1)) (by omega :
        p + 1 + 1 > 0), sub_le n (n / M), div_mul_le_self n M]
  have h2 : n / p ≤ M * ((n / M) / p) + M := le_of_lt_succ (Nat.div_lt_of_lt_mul <| by
    nlinarith [div_add_mod n M, mod_lt n hM, div_add_mod (n / M) p, mod_lt (n / M) hp])
  exact h2.trans (by gcongr)

/-- For `√n < p < n/L` and `0 < m < n`: smooth `m` has `ν_p(m) = 1` iff `p ∣ m`. -/
lemma Params.initial.valuation_eq_indicator (P : Params) {p m : ℕ} (hp : p.Prime)
    (hp' : p > Real.sqrt P.n) (hps : p < P.n / P.L) (hm : m < P.n) (hm0 : m ≠ 0) :
    (if m ∈ smoothNumbers (P.n / P.L) then m.factorization p else 0) =
      if p ∣ m then 1 else 0 := by
  split_ifs with hs hd hd' <;> simp_all only [gt_iff_lt, factorization_eq_zero_iff,
    not_false_eq_true, or_false, or_true]
  · exact valuation_eq_one P hp hp' hm hm0 hd
  · exact hs <| smooth_of_multiple P hp' hps hm hm0 hd'

/-- For `√n < p < n/L`, `∑_{a ∈ initial.a} ν_p(a) = M · #{m ∈ [n-n/M, n) : p ∣ m}`. -/
lemma Params.initial.sum_valuation_eq (P : Params) {p : ℕ} (hp : p.Prime)
    (hp' : p > Real.sqrt P.n) (hps : p < P.n / P.L) : (P.initial.a.map (·.factorization p)).sum =
    P.M * (Finset.filter (p ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card := by
  have h1 : ∀ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, (if m ∈ smoothNumbers (P.n / P.L)
      then m.factorization p else 0) = if p ∣ m then 1 else 0 := fun m hm ↦ by
    by_cases m = 0
    · simp_all only [Finset.mem_Ico, nonpos_iff_eq_zero]
      exact absurd hm.1 (Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.div_lt_self hm.2 (by linarith [P.hM]))))
    · simp_all [valuation_eq_indicator]
  have h2 : (P.initial.a.map (·.factorization p)).sum =
      P.M * ∑ m ∈ Finset.Ico (P.n - P.n / P.M) P.n,
        if m ∈ smoothNumbers (P.n / P.L) then m.factorization p else 0 := by
    have : (P.initial.a.map (·.factorization p)).sum =
        (map (fun m ↦ if m ∈ smoothNumbers (P.n / P.L) then m.factorization p else 0)
          (join (replicate P.M (Finset.Ico (P.n - P.n / P.M) P.n).val))).sum := by
      conv_lhs => rw [show P.initial.a = filter (· ∈ smoothNumbers (P.n / P.L))
          (join (replicate P.M (Finset.Ico (P.n - P.n / P.M) P.n).val)) from rfl]
      induction (replicate P.M (Finset.Ico (P.n - P.n / P.M) P.n).val).join
        using Multiset.induction <;> aesop
    simp_all
  simp_all [sum_congr rfl h1]

@[blueprint
  "initial-factorization-medium-prime-ge"
  (statement := /-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in deficit by at most $M$.-/)
  (proof := /-- The number of times $p$ divides $a_1 \dots a_t$ is at least $M \lfloor n/Mp
  \rfloor ≥ n/p - M$ (note that the removal of the non-smooth numbers does not remove any multiples
  of $p$).  Meanwhile, the number of times $p$ divides $n!$ is at most $n/p$.-/)
  (latexEnv := "sublemma")]
theorem Params.initial.balance_medium_prime_ge (P : Params) {p : ℕ} (hp : p < P.n / P.L)
    (hp' : p > Real.sqrt P.n) : P.initial.balance p ≥ -P.M := by
  by_cases hp_prime : p.Prime
  · have : (P.initial.a.map (·.factorization p)).sum ≥ P.n / p - P.M :=
      (initial.sum_valuation_eq P hp_prime hp' hp).symm ▸ sub_le_of_le_add
        (initial.count_multiples_lower_bound P.n P.M p (by linarith [P.hM]) hp_prime.pos)
    simp only [Factorization.balance, Factorization.sum, factorial_factorization_eq_div hp_prime hp']
    omega
  · simp_all [Factorization.balance, Factorization.sum]

/-- The sum of `p`-adic valuations of numbers in an interval equals the sum over `k` of the count of
multiples of `p^k` in that interval. -/
lemma sum_factorization_eq_sum_multiples {A B p : ℕ} (hp : p.Prime) (hA : 0 < A) :
    ∑ m ∈ .Ico A B, m.factorization p =
      ∑ k ∈ .Ico 1 B, ((Finset.Ico A B).filter (p ^ k ∣ ·)).card := by
  have h_factorization : ∀ m ∈ Finset.Ico A B, m.factorization p = ∑ k ∈ .Ico 1 B,
      if p^k ∣ m then 1 else 0 := fun m hm ↦ by
    have hm' : m ≠ 0 := (hA.trans_le (Finset.mem_Ico.mp hm).1).ne'
    have : (Finset.Ico 1 B).filter (p^· ∣ m) = Finset.Ico 1 (m.factorization p + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨fun ⟨⟨h1, _⟩, h2⟩ ↦ ⟨h1, Nat.lt_succ_iff.mpr <| le_of_not_gt fun h ↦
        pow_succ_factorization_not_dvd hm' hp <| (pow_dvd_pow p h).trans h2⟩,
        fun ⟨h1, h2⟩ ↦ ⟨⟨h1, (le_of_lt_succ h2).trans_lt (factorization_lt p hm') |>.trans_le
          (Finset.mem_Ico.mp hm).2.le⟩,
            (pow_dvd_pow p (le_of_lt_succ h2)).trans (ordProj_dvd m p)⟩⟩
    simp [sum_boole, this]
  rw [sum_congr rfl h_factorization, sum_comm]
  simp [sum_boole]

/-- The contribution of the `k`-th power of `p` to the balance is bounded by `M`.
Specifically, `M * count(p^k) ≤ floor(n/p^k) + M`. -/
lemma Params.initial.term_bound (P : Params) {p k : ℕ} (hp : p.Prime) :
    P.M * ((Finset.Ico (P.n - P.n / P.M) P.n).filter (p ^ k ∣ ·)).card ≤
      P.n / p ^ k + P.M := by
  calc
    _ ≤ P.M * ((P.n / P.M + p ^ k - 1) / p ^ k) := Nat.mul_le_mul_left _ (by
        convert Params.initial.count_multiples_le (P.n - P.n / P.M) P.n (p ^ k) <|
          pow_pos hp.pos k using 1
        rw [Nat.sub_sub_self (div_le_self _ _)])
    _ ≤ P.M * (P.n / P.M / p ^ k + 1) := mul_le_mul_left _
      (by rw [← add_div_right _ <| pow_pos hp.pos k]; exact Nat.div_le_div_right <| sub_le ..)
    _ ≤ P.n / p ^ k + P.M := by
        rw [mul_add, mul_one]
        exact Nat.add_le_add_right (le_trans (mul_div_le_mul_div_assoc ..)
          (Nat.div_le_div_right <| by rw [mul_comm]; exact div_mul_le_self ..)) ..

/-- The sum of valuations in the initial factorization is bounded by `M` times the sum of
valuations in the interval. This is because the initial factorization is a subset of `M` copies
of the interval. -/
lemma Params.initial.sum_valuation_le (P : Params) (p : ℕ) :
    (initial P).sum (fun m ↦ m.factorization p) ≤
      P.M * ∑ m ∈ .Ico (P.n - P.n / P.M) P.n, m.factorization p := by
  have h_subset : P.initial.a ≤ Multiset.bind (replicate P.M (Finset.Ico (P.n - P.n / P.M) P.n))
      (fun s ↦ s.val) := by
    simp only [initial, le_iff_count]
    intro a
    by_cases a ∈ (P.n / P.L).smoothNumbers
    · simp_all only [join, count_filter_of_pos]
      simp only [sum_replicate, count_nsmul, count_bind, map_replicate]
      rfl
    · simp_all [join]
  have h_sum_le : ∀ {s t : Multiset ℕ}, s ≤ t →
      (s.map (fun m ↦ m.factorization p)).sum ≤ (t.map (fun m ↦ m.factorization p)).sum := by
    intro s t hst
    obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp hst
    simp
  convert h_sum_le h_subset using 1
  simp [Multiset.bind]

@[blueprint
  "initial-factorization-small-prime-le"
  (statement := /-- A small prime $p \leq \sqrt{n}$ can be in surplus by at most $M\log n$.-/)
  (proof := /-- Routine computation using Legendre's formula, noting that at most
  $\log n / \log 2$ powers of $p$ divide any given number up to $n$.-/)
  (latexEnv := "sublemma")
  (discussion := 513)]
theorem Params.initial.balance_small_prime_le (P : Params) {p : ℕ} :
    P.initial.balance p ≤ P.M * (Real.log P.n) / (Real.log 2):= by
  have h_sum_valuation_le_M_sum_multiples :
      (initial P).sum (fun m ↦ m.factorization p) ≤
        P.M * (∑ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, m.factorization p) := by
    exact sum_valuation_le P p
  by_cases hp_prime : Nat.Prime p
  · have h_sum_multiples : ∑ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, m.factorization p =
        ∑ k ∈ .Ico 1 (Nat.log p P.n + 1),
          ((Finset.Ico (P.n - P.n / P.M) P.n).filter (p ^ k ∣ ·)).card := by
      have h_sum_multiples_aux : ∀ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, m.factorization p =
          ∑ k ∈ .Ico 1 (Nat.log p P.n + 1), (if p ^ k ∣ m then 1 else 0) := by
        intro m hm
        have h_factorization_eq : m.factorization p = ∑ k ∈ .Ico 1 (m.factorization p + 1), 1 := by simp
        rw [h_factorization_eq, ← Finset.sum_filter]
        refine sum_bij (fun k hk ↦ k) ?_ ?_ ?_ ?_ <;> norm_num
        · refine fun a ha₁ ha₂ ↦
            ⟨⟨ha₁, lt_succ_of_le (Nat.le_log_of_pow_le hp_prime.one_lt ?_)⟩, ?_⟩
          · refine le_trans (Nat.pow_le_pow_right hp_prime.pos (le_of_lt_succ ha₂)) ?_
            refine le_trans (le_of_dvd (pos_of_ne_zero (by aesop)) (ordProj_dvd ..)) ?_
            linarith [Finset.mem_Ico.mp hm]
          · exact dvd_trans (pow_dvd_pow _ <| le_of_lt_succ ha₂) <| ordProj_dvd ..
        · refine fun b hb₁ hb₂ hb₃ ↦ ⟨hb₁, lt_succ_of_le (le_of_not_gt fun hb₄ ↦
            absurd (dvd_trans (pow_dvd_pow _ hb₄) hb₃) <|
              pow_succ_factorization_not_dvd ?_ hp_prime)⟩
          linarith [Finset.mem_Ico.mp hm, Nat.sub_pos_of_lt (show P.n / P.M < P.n from
            div_lt_self (pos_of_ne_zero (by grind)) (by linarith [P.hM]))]
      rw [sum_congr rfl h_sum_multiples_aux, sum_comm]; simp_all
    have h_factorial_factorization : (P.n.factorial.factorization p : ℤ) =
        ∑ k ∈ Ico 1 (log p P.n + 1), (P.n / p ^ k : ℤ) := by
      rw [factorization_def]
      · have := Fact.mk hp_prime
        rw [padicValNat_factorial] <;> aesop
      · assumption
    have h_balance_bound : (P.initial.balance p : ℤ) ≤ ∑ k ∈ .Ico 1 (Nat.log p P.n + 1),
        (P.M * ((Finset.Ico (P.n - P.n / P.M) P.n).filter (p ^ k ∣ ·)).card -
          (P.n / p ^ k : ℤ)) := by
      simp_all only [Factorization.balance, sum_sub_distrib, ← mul_sum ..,
        tsub_le_iff_right, sub_add_cancel]
      exact_mod_cast h_sum_valuation_le_M_sum_multiples
    have h_term_bound : ∀ k ∈ Finset.Ico 1 (Nat.log p P.n + 1),
        (P.M * ((Finset.Ico (P.n - P.n / P.M) P.n).filter (p ^ k ∣ ·)).card -
          (P.n / p ^ k : ℤ)) ≤ P.M :=
      fun k hk ↦ sub_le_iff_le_add'.mpr (mod_cast initial.term_bound P hp_prime (k := k))
    have h_num_terms_bound : (Nat.log p P.n : ℤ) ≤ Real.log P.n / Real.log p := by
      rw [le_div_iff₀ (log_pos <| Nat.one_lt_cast.mpr hp_prime.one_lt)]
      simpa using log_le_log (by norm_cast; exact Nat.Prime.pos hp_prime |> fun h ↦ pow_pos h _)
        (show (p ^ Nat.log p P.n : ℝ) ≤ P.n from mod_cast pow_log_le_self p <| by
          linarith [show P.n > 0 from pos_of_ne_zero <| by rintro h; have := P.hL; grind])
    have : Real.log p ≥ Real.log 2 := log_le_log (by norm_num) (mod_cast hp_prime.two_le)
    refine le_trans (Int.cast_le.mpr h_balance_bound) <|
      le_trans (Int.cast_le.mpr <| sum_le_sum h_term_bound) ?_
    norm_num [mul_div_assoc, mul_comm] at *
    gcongr
    exact h_num_terms_bound.trans (div_le_div_of_nonneg_left (log_nonneg <|
      mod_cast Nat.one_le_iff_ne_zero.mpr <| by rintro h; have := P.hL; grind)
        (log_pos <| by norm_num) this)
  · field_simp
    rw [show P.initial.balance p = 0 from ?_] <;> norm_num
    · exact mul_nonneg (cast_nonneg _) <| log_natCast_nonneg _
    · simp_all [Factorization.balance]

/-- If `p` is a small prime (`L < p ≤ √n`) and `m` is in the initial interval and divisible by `p`,
then `m` is `(n/L)`-smooth. -/
lemma Params.initial.smooth_of_dvd_small_prime (P : Params) {p m : ℕ} (hp : p ≤ Real.sqrt P.n)
    (hpL : p > P.L) (hm : m ∈ Finset.Ico (P.n - P.n / P.M) P.n) (hpm : p ∣ m) :
    m ∈ (P.n / P.L).smoothNumbers := by
  by_contra h_not_smooth
  have hm_ne_zero : m ≠ 0 := by
    intro h
    rw [Finset.mem_Ico, h, nonpos_iff_eq_zero, Nat.sub_eq_zero_iff_le] at hm
    nlinarith [div_mul_le_self P.n P.M, P.hM, P.hL_pos, P.hL, P.hL']
  obtain ⟨q, hq_prime, hq_div, hq_ge⟩ : ∃ q, q.Prime ∧ q ∣ m ∧ q ≥ P.n / P.L := by
    simp only [smoothNumbers] at h_not_smooth; simp_all
  have hp_div_mq : p ∣ m / q := by
    refine dvd_div_of_mul_dvd <| Coprime.mul_dvd_of_dvd_of_dvd
      (hq_prime.coprime_iff_not_dvd.mpr fun h ↦ ?_) hq_div hpm
    rw [le_sqrt (cast_nonneg _) (cast_nonneg _)] at hp
    norm_cast at hp
    nlinarith [le_of_dvd (lt_trans P.hL_pos hpL) h, div_add_mod P.n P.L, mod_lt P.n P.hL_pos]
  have hm_gt_n : P.n < m := by
    rw [(Nat.mul_div_cancel' hq_div).symm]
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul hq_ge <| lt_of_lt_of_le hpL <| le_of_dvd (div_pos
      (le_of_dvd (pos_of_ne_zero hm_ne_zero) hq_div) hq_prime.pos) hp_div_mq)
    nlinarith only [div_add_mod P.n P.L, mod_lt P.n (pos_of_ne_zero
      (by linarith [P.hL_pos] : P.L ≠ 0)), P.hL_pos, P.hL]
  linarith [Finset.mem_Ico.mp hm]

/-- For a small prime `p`, the sum of `p`-adic valuations in the initial factorization equals `M`
times the sum over `k` of the count of multiples of `p^k` in the interval. -/
lemma Params.initial.sum_valuation_eq_small (P : Params) {p : ℕ} (hp : p.Prime)
    (hp_le : p ≤ Real.sqrt P.n) (hp_gt : p > P.L) :
    (P.initial.a.map (·.factorization p)).sum =
    P.M * ∑ k ∈ Finset.Ico 1 (Nat.log p P.n + 1),
      (Finset.filter (p^k ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card := by
  have h_sum_factorizations : (P.initial.a.map (·.factorization p)).sum =
      P.M * (∑ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, m.factorization p) := by
    have h_sum_smooth : (P.initial.a.map (·.factorization p)).sum =
        P.M * (∑ m ∈ filter (fun m ↦ m ∈ smoothNumbers (P.n / P.L))
          (Ico (P.n - P.n / P.M) P.n), m.factorization p) := by
      simp only [initial, join, sum_replicate, sum_filter, filter_nsmul]
      simp only [Finset.sum_ite, sum_const_zero, add_zero]
      induction P.M with
      | zero => simp_all
      | succ n ih =>
        simp_all only [gt_iff_lt, add_smul, one_smul, Multiset.map_add, sum_add, succ_mul]
        congr! 1
        rw [Multiset.map_nsmul]
        induction n with
        | zero => simp_all
        | succ n' ih' =>
          simp_all only [Multiset.sum_nsmul, smul_eq_mul, succ_mul]
          congr! 1
    rw [h_sum_smooth, sum_filter_of_ne]
    intro m hm hmp
    specialize hmp
    contrapose! hmp
    simp_all +decide only [Finset.mem_Ico, factorization_eq_zero_iff, false_or]
    refine Or.inl fun h ↦ hmp <| initial.smooth_of_dvd_small_prime P hp_le (by grind)
      (Finset.mem_Ico.mpr ⟨by grind, by grind⟩) h
  have h_sum_factorizations_eq : ∀ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, m.factorization p =
      ∑ k ∈ Ico 1 (Nat.log p P.n + 1), (if p ^ k ∣ m then 1 else 0) := by
    intro m hm
    have h_factorization_eq_sum : m.factorization p = ∑ k ∈ Finset.Ico 1 (Nat.factorization m p + 1),
        (if p ^ k ∣ m then 1 else 0) := by
      simp_all only [sum_congr rfl fun x hx ↦ if_pos <| dvd_trans (pow_dvd_pow _ <|
        Finset.mem_Ico.mp hx |>.2 |> Nat.lt_succ_iff.mp) <| ordProj_dvd .., succ_eq_add_one,
          sum_const, card_Ico, add_tsub_cancel_right, smul_eq_mul, mul_one]
    refine h_factorization_eq_sum.trans <| sum_subset ?_ ?_
    · simp +contextual only [Finset.subset_iff, Finset.mem_Ico, true_and, and_imp]
      refine fun k hk₁ hk₂ ↦ lt_succ_of_le (le_log_of_pow_le hp.one_lt ?_)
      linarith [Finset.mem_Ico.mp hm, le_of_dvd (pos_of_ne_zero (by aesop_cat)) (ordProj_dvd m p),
        Nat.pow_le_pow_right hp.one_lt.le (show k ≤ factorization m p from by grind)]
    · simp +contextual only [Finset.mem_Ico, true_and, not_lt, ite_eq_right_iff, one_ne_zero,
      imp_false, and_imp]
      intro x hx₁ hx₂ hx₃
      contrapose! hx₃
      rw [← factorization_le_iff_dvd] at hx₃ <;> norm_num at *
      · exact lt_succ_of_le (by simpa [hp] using hx₃ p)
      · exact fun h ↦ absurd h hp.ne_zero
      · rintro rfl
        norm_num at *
        exact hm.1.not_gt (div_lt_self hm.2 (by linarith [P.hM]))
  rw [h_sum_factorizations, Finset.sum_congr rfl h_sum_factorizations_eq, Finset.sum_comm,
    Finset.sum_congr rfl]
  aesop

/-- The balance of a small prime `p` is at least `-M * floor(log_p n)`. -/
lemma Params.initial.balance_ge_neg_M_mul_log (P : Params) {p : ℕ} (hp : p.Prime)
    (hp_le : p ≤ Real.sqrt P.n) (hp_gt : p > P.L) :
    P.initial.balance p ≥ - (P.M * (Nat.log p P.n) : ℤ) := by
  have := Fact.mk hp
  rw [Factorization.balance, Factorization.sum, initial.sum_valuation_eq_small P hp hp_le hp_gt,
    factorization_def _ hp, padicValNat_factorial]
  · simp only [cast_mul, cast_sum, Int.natCast_ediv, cast_pow, ge_iff_le, neg_le_sub_iff_le_add]
    calc
      _ ≤ ∑ k ∈ Ico 1 (Nat.log p P.n + 1), ((P.M : ℤ) *
          (Finset.filter (p^k ∣ ·) (Ico (P.n - P.n / P.M) P.n)).card + P.M) :=
        sum_le_sum fun k _ ↦ mod_cast initial.count_multiples_lower_bound P.n P.M (p^k)
          (by linarith [P.hM]) (pow_pos hp.pos _)
      _ = _ := by simp [sum_add_distrib, mul_sum, mul_comm]
  · exact lt_succ_self _

@[blueprint
  "initial-factorization-small-prime-ge"
  (statement := /-- A small prime $L < p \leq \sqrt{n}$ can be in deficit by at most
  $M\log n$.-/)
  (proof := /-- Routine computation using Legendre's formula, noting that at most
  $\log n / \log 2$ powers of $p$ divide any given number up to $n$.-/)
  (latexEnv := "sublemma")
  (discussion := 514)]
theorem Params.initial.balance_small_prime_ge (P : Params) {p : ℕ} (hp : p ≤ Real.sqrt P.n)
    (hp' : p > P.L) : P.initial.balance p ≥ - P.M * (Real.log P.n) / (Real.log 2) := by
  have h_bound_ℝ : (P.initial.balance p : ℝ) ≥ -(P.M * (Real.log P.n / Real.log p)) := by
    refine le_trans (b := - (P.M * (Nat.log p P.n : ℝ))) ?_ ?_
    · gcongr
      have h_p_gt_1 : 1 < p := lt_of_le_of_lt (succ_le_of_lt P.hL_pos) hp'
      have hn_pos : 0 < P.n := by
        refine pos_iff_ne_zero.mpr fun h ↦ ?_
        simp only [h, CharP.cast_eq_zero, Real.sqrt_zero, cast_nonpos] at hp
        linarith [hp, hp', P.hL_pos]
      rw [le_div_iff₀ (log_pos (by exact_mod_cast lt_of_le_of_lt (succ_le_of_lt P.hL_pos) hp'))]
      nth_rw 1 [← Real.log_pow]
      exact log_le_log (by positivity) <| by norm_cast; exact pow_log_le_self p (Nat.ne_of_gt hn_pos)
    norm_cast
    by_cases hp_prime : p.Prime
    · simpa using initial.balance_ge_neg_M_mul_log P hp_prime hp hp'
    · simp only [cast_mul, Factorization.balance, hp_prime, not_false_eq_true,
        factorization_eq_zero_of_not_prime, CharP.cast_eq_zero, sub_zero]
      rw [neg_le_iff_add_nonneg']
      positivity
  exact le_trans (by rw [mul_div]; ring_nf; gcongr; norm_cast; linarith [P.hL_pos]) h_bound_ℝ

@[blueprint
  "initial-factorization-tiny-prime-ge"
  (statement := /-- A tiny prime $p \leq L$ can be in deficit by at most $M\log n + ML\pi(n)$.-/)
  (proof := /-- In addition to the Legendre calculations, one potentially removes factors of the
  form $plq$ with $l \leq L$ and $q \leq n$ a prime up to $M$ times each, with at most $L$ copies
  of $p$ removed at each factor.-/)
  (latexEnv := "sublemma")
  (discussion := 515)]
theorem Params.initial.balance_tiny_prime_ge (P : Params) {p : ℕ} (hp : p ≤ P.L) :
    P.initial.balance p ≥ - P.M * (Real.log P.n) - P.M * P.L^2 * (primeCounting P.n) := by
  sorry

@[blueprint
  "initial-score-bound"
  (statement := /-- The initial score is bounded by
  $$ n \log(1-1/M)^{-1} + \sum_{p \leq n/L} M \log n + \sum_{p \leq \sqrt{n}} M \log^2 n / \log 2
  + \sum_{n/L < p \leq n} \frac{n}{p} \log \frac{n}{p}
  + \sum_{p \leq L} (M \log n + M L \pi(n)) \log L.$$ -/)
  (latexEnv := "proposition")
  (proof := /-- Combine Lemma \ref{initial-factorization-waste},
  Sublemma \ref{initial-factorization-large-prime-le},
  Sublemma \ref{initial-factorization-large-prime-ge},
  Sublemma \ref{initial-factorization-medium-prime-le},
  Sublemma \ref{initial-factorization-medium-prime-ge},
  Sublemma \ref{initial-factorization-small-prime-le},
  Sublemma \ref{initial-factorization-small-prime-ge}, and
  Sublemma \ref{initial-factorization-tiny-prime-ge}, and combine $\log p$ and $\log (n/p)$ to $\log n$.-/)]
theorem Params.initial.score_bound (P : Params) :
    P.initial.score P.L ≤ P.n * log (1 - 1 / (P.M : ℝ))⁻¹ +
      ∑ p ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)), P.M * Real.log P.n +
      ∑ p ∈ Finset.filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
        P.M * Real.log P.n * Real.log P.n / Real.log 2 +
      ∑ p ∈ Finset.filter (·.Prime) (Finset.Icc (P.n / P.L + 1) P.n),
        (P.n / p) * Real.log (P.n / p) +
      ∑ p ∈ Finset.filter (·.Prime) (Finset.Iic P.L),
        (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L := by sorry

@[blueprint
  "bound-score-1"
  (statement := /-- If $M$ is sufficiently large depending on $\varepsilon$, then
$n \log(1-1/M)^{-1} \leq \varepsilon n$. -/)
  (proof := /-- Use the fact that $\log(1-1/M)^{-1}$ goes to zero as $M \to \infty$.-/)
  (latexEnv := "sublemma")]
theorem Params.initial.bound_score_1 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ M in .atTop, ∀ P : Params,
      P.M = M → P.n * log (1 - 1 / (P.M : ℝ))⁻¹ ≤ ε * P.n := by
  have h_tendsto : Filter.Tendsto (fun M : ℕ ↦ log (1 - 1 / (M : ℝ))⁻¹) .atTop (nhds 0) := by
    have : Filter.Tendsto (fun M : ℕ ↦ (1 : ℝ) / M) .atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have : Filter.Tendsto (fun M : ℕ ↦ 1 - 1 / (M : ℝ)) .atTop (nhds 1) := by
      simpa only [one_div, sub_zero] using tendsto_const_nhds.sub this
    have : Filter.Tendsto (fun M : ℕ ↦ (1 - 1 / (M : ℝ))⁻¹) .atTop (nhds 1) := by
      simpa using this.inv₀ one_ne_zero
    have h : Filter.Tendsto (fun x : ℝ ↦ log x) (nhds 1) (nhds 0) := by
      simpa [ContinuousAt, log_one] using continuousAt_log (x := (1 : ℝ)) one_ne_zero
    exact h.comp this
  rw [Metric.tendsto_atTop] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with M hM P hPM
  rcases eq_or_ne P.n 0 with hn | hn
  · simp [hn]
  have hM_pos : (0 : ℝ) < M := cast_pos.mpr (zero_lt_of_lt <| hPM ▸ P.hM)
  have h_one_sub_pos : 0 < 1 - 1 / (M : ℝ) := by
    rw [sub_pos, div_lt_one hM_pos]; exact one_lt_cast.mpr <| hPM ▸ P.hM
  have h_inv_ge_one : 1 ≤ (1 - 1 / (M : ℝ))⁻¹ := by
    rw [one_le_inv_iff₀]; exact ⟨h_one_sub_pos, by linarith [div_nonneg one_pos.le hM_pos.le]⟩
  have h_log_lt : log (1 - 1 / (M : ℝ))⁻¹ < ε := by
    have := hN M hM; rw [Real.dist_eq, log_inv, sub_zero, abs_neg] at this; rw [log_inv]
    rwa [abs_of_neg (log_neg h_one_sub_pos (by linarith [div_pos one_pos hM_pos]))] at this
  calc P.n * log (1 - 1 / (P.M : ℝ))⁻¹ = P.n * log (1 - 1 / (M : ℝ))⁻¹ := by rw [hPM]
    _ ≤ P.n * ε := by gcongr
    _ = ε * P.n := mul_comm ..

@[blueprint
  "bound-score-2"
  (statement := /-- If $L$ is sufficiently large depending on $M, \varepsilon$, and $n$
  sufficiently large depending on $L$, then $\sum_{p \leq n/L} M \log n  \leq \varepsilon n$. -/)
  (proof := /-- Use the prime number theorem (or the Chebyshev bound). -/)
  (latexEnv := "sublemma")]
theorem Params.initial.bound_score_2 (ε : ℝ) (hε : ε > 0) (M : ℕ) :
    ∀ᶠ L in .atTop, ∀ᶠ n in .atTop, ∀ P : Params,
      P.L = L → P.n = n → P.M = M → ∑ _p ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)),
        P.M * Real.log P.n ≤ ε * P.n := by
  have pi_equiv := pi_alt'
  rw [IsEquivalent, isLittleO_iff] at pi_equiv
  specialize pi_equiv (by norm_num : (1 : ℝ) / 2 > 0)
  rw [Filter.eventually_atTop] at pi_equiv
  obtain ⟨N₀, hN₀⟩ := pi_equiv
  filter_upwards [Filter.eventually_ge_atTop (max 2 (max (⌈N₀⌉₊ + 1) (⌈4 * M / ε⌉₊ + 1)))] with L hL
  have hL2 : L ≥ 2 := le_of_max_le_left hL
  have hLN₀ : (L : ℝ) > N₀ :=
    (le_ceil N₀).trans_lt (by exact_mod_cast (le_max_left _ _).trans (le_of_max_le_right hL))
  have hL4Mε : (L : ℝ) > 4 * M / ε :=
    (le_ceil _).trans_lt (by exact_mod_cast (le_max_right _ _).trans (le_of_max_le_right hL))
  have hLpos : (L : ℝ) > 0 := by positivity
  filter_upwards [Filter.eventually_ge_atTop (4 * L ^ 2)] with n hn P hPL hPn hPM
  simp only [hPM, hPL, hPn]
  have hnL2 : n ≥ L ^ 2 := (Nat.le_mul_of_pos_left _ (by omega : 0 < 4)).trans hn
  have hnLge : n / L ≥ L := le_div_iff_mul_le (by omega) |>.mpr (by rw [sq] at hnL2; exact hnL2)
  have hnLN₀ : ((n / L : ℕ) : ℝ) > N₀ := hLN₀.trans_le (by exact_mod_cast hnLge)
  conv_lhs => rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (filter Prime (Finset.Iic (n / L))).card = primeCounting (n / L) := by
    simp only [primeCounting, primeCounting', card_filter, count_eq_card_filter_range]
    congr 1; ext p
    rw [Finset.mem_Iic, Finset.mem_range, Nat.lt_succ_iff]
  rw [hcard]
  rcases eq_or_ne M 0 with rfl | hMne
  · simp [mul_nonneg (hε.le) (cast_nonneg _)]
  have hnLgt1 : (1 : ℝ) < (n / L : ℕ) := by exact_mod_cast hL2.trans hnLge
  have hlogPos : Real.log (n / L : ℕ) > 0 := Real.log_pos hnLgt1
  have hdivPos : (0 : ℝ) < (n / L : ℕ) / Real.log (n / L : ℕ) := div_pos (by grind) hlogPos
  have hπ : (primeCounting (n / L) : ℝ) ≤ 3 / 2 * ((n / L : ℕ) / Real.log (n / L : ℕ)) := by
    have h := hN₀ ((n / L : ℕ) : ℝ) hnLN₀.le
    simp only [Pi.sub_apply, floor_natCast, norm_eq_abs, abs_of_pos hdivPos] at h
    linarith [abs_sub_le_iff.mp h]
  have hn4 : n ≥ 4 := (Nat.pow_le_pow_left hL2 2).trans hnL2
  have hnpos : (n : ℝ) > 0 := cast_pos.mpr (by positivity)
  have hn_gt_1 : (1 : ℝ) < n := by exact_mod_cast (by grind)
  have hlogN : Real.log (n / L : ℕ) ≥ Real.log n / 2 := by
    have hsqrt : ((n / L : ℕ) : ℝ) ≥ Real.sqrt n := by
      have h1 : Real.sqrt n ≤ n / (2 * L) := by
        rw [sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [div_pow, le_div_iff₀ (by positivity)]
        have hn4L2 : (4 : ℝ) * L ^ 2 ≤ n := by exact_mod_cast hn
        have h2L_sq : ((2 : ℝ) * L) ^ 2 = 4 * L ^ 2 := by ring
        nlinarith [h2L_sq, sq_nonneg ((n : ℝ) - 4 * L ^ 2)]
      have h2 : (n : ℝ) / L - Real.sqrt n ≥ 1 := by
        have hL_ne : (L : ℝ) ≠ 0 := by positivity
        calc (n : ℝ) / L - Real.sqrt n ≥ n / L - n / (2 * L) := by grind
          _ = n / (2 * L) := by grind
          _ ≥ 4 * L ^ 2 / (2 * L) := by gcongr; exact_mod_cast hn
          _ = 2 * L := by grind
          _ ≥ 4 := by have hL2' : (2 : ℝ) ≤ L := ofNat_le_cast.mpr hL2; grind
          _ ≥ 1 := by grind
      have h3 : ((n / L : ℕ) : ℝ) ≥ (n : ℝ) / L - 1 := by
        have hlt := sub_one_lt_floor (a := (n : ℝ) / L)
        rw [floor_div_eq_div] at hlt
        grind
      grind
    calc
      Real.log (n / L : ℕ) ≥ Real.log (Real.sqrt n) := log_le_log (sqrt_pos.mpr hnpos) hsqrt
      _ = Real.log n / 2 := log_sqrt hnpos.le
  calc
    (primeCounting (n / L) : ℝ) * (M * Real.log n)
      ≤ 3 / 2 * ((n / L : ℕ) / Real.log (n / L : ℕ)) * (M * Real.log n) := by gcongr
    _ ≤ 3 / 2 * ((n : ℝ) / L / Real.log (n / L : ℕ)) * (M * Real.log n) := by
        have : ((n / L : ℕ) : ℝ) ≤ (n : ℝ) / L := cast_div_le; gcongr
    _ ≤ 3 / 2 * ((n : ℝ) / L / (Real.log n / 2)) * (M * Real.log n) := by
        have : 0 < Real.log n / 2 := div_pos (log_pos hn_gt_1) (by grind); gcongr
    _ = 3 * M * n / L := by field_simp [log_ne_zero_of_pos_of_ne_one hnpos <| ne_of_gt hn_gt_1]
    _ ≤ ε * n := by
        rw [div_le_iff₀ hLpos]
        have : 4 * M < ε * L := by linarith [(div_lt_iff₀ hε).mp hL4Mε]
        calc 3 * M * n ≤ ε * L * n := by nlinarith
          _ = ε * n * L := by ring

@[blueprint "bound-score-3"
  (statement := /-- If $n$ sufficiently large depending on $M, \varepsilon$, then
  $\sum_{p \leq \sqrt{n}} M \log^2 n / \log 2 \leq \varepsilon n$. -/)
  (proof := /-- Crude estimation. -/)
  (discussion := 516)
  (latexEnv := "sublemma")]
theorem Params.initial.bound_score_3 (ε : ℝ) (hε : ε > 0) (M : ℕ) :
    ∀ᶠ n in .atTop, ∀ P : Params,
      P.M = M → P.n = n → ∑ _p ∈ filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
          P.M * Real.log P.n * Real.log P.n / Real.log 2 ≤ ε * P.n := by
  have h_littleO : (fun x : ℝ ↦ Real.sqrt x * Real.log x) =o[Filter.atTop] (fun x ↦ x) :=
    (isLittleO_mul_iff_isLittleO_div (hf := by
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx; exact sqrt_ne_zero'.mpr hx)).mpr
      (by simp_rw [div_sqrt, sqrt_eq_rpow]; exact isLittleO_log_rpow_atTop one_half_pos)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp
    (h_littleO.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
      (ε * Real.log 2 / (8 * (M + 1))) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp <| isLittleO_iff.mp pi_alt' one_half_pos
  filter_upwards [Filter.eventually_ge_atTop (max 16 (max N₀ ((⌈N₁⌉₊ + 1) ^ 2)))] with n hn P hPM hPn
  simp only [hPM, hPn]; have hn16 : n ≥ 16 := le_of_max_le_left hn
  have hnpos : (n : ℝ) > 0 := by positivity
  have hlogn_pos : Real.log n > 0 := log_pos (by exact_mod_cast lt_of_add_left_lt hn16)
  have hsqrt_pos : Real.sqrt n > 0 := sqrt_pos.mpr hnpos
  have hn16' : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hsqrt_ge_4 : Real.sqrt n ≥ 4 := by nlinarith [Real.sq_sqrt hnpos.le, sq_nonneg (Real.sqrt n - 4)]
  have hfloor_gt_1 : (1 : ℝ) < ⌊Real.sqrt n⌋₊ := by
    exact_mod_cast lt_of_add_left_lt (le_floor (by linarith : (3 : ℝ) ≤ Real.sqrt n))
  conv_lhs => rw [sum_const, nsmul_eq_mul]
  rw [show (filter Nat.Prime (Finset.Iic ⌊Real.sqrt n⌋₊)).card = primeCounting ⌊Real.sqrt n⌋₊ by
    simp only [primeCounting, primeCounting', card_filter, count_eq_card_filter_range]
    congr 1; ext p; simp only [Finset.mem_Iic, Finset.mem_range, Nat.lt_succ_iff]]
  rcases eq_or_ne M 0 with rfl | hMne; · simp [mul_nonneg hε.le (cast_nonneg _)]
  have hsqrt_N₁ : (⌊Real.sqrt n⌋₊ : ℝ) > N₁ := by
    have hnsq : n ≥ (⌈N₁⌉₊ + 1) ^ 2 := (le_max_right _ _).trans (le_of_max_le_right hn)
    have : Real.sqrt n ≥ ⌈N₁⌉₊ + 1 := by
      calc (⌈N₁⌉₊ : ℝ) + 1 = Real.sqrt (((⌈N₁⌉₊ + 1 : ℕ) : ℝ) ^ 2) := by
            rw [Real.sqrt_sq (cast_nonneg' (⌈N₁⌉₊ + 1))]; simp
        _ ≤ Real.sqrt n := sqrt_le_sqrt (by exact_mod_cast hnsq)
    linarith [le_ceil N₁, sub_one_lt_floor (Real.sqrt n)]
  have hlog_floor_pos : Real.log ⌊Real.sqrt n⌋₊ > 0 := log_pos hfloor_gt_1
  have hπ : (primeCounting ⌊Real.sqrt n⌋₊ : ℝ) ≤ 3 / 2 * (⌊Real.sqrt n⌋₊ / Real.log ⌊Real.sqrt n⌋₊) := by
    have := hN₁ ⌊Real.sqrt n⌋₊ hsqrt_N₁.le
    simp only [Pi.sub_apply, floor_natCast, norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < ⌊Real.sqrt n⌋₊ / Real.log ⌊Real.sqrt n⌋₊)] at this
    linarith [(abs_le.mp this).2]
  have hlog_floor_ge : Real.log ⌊Real.sqrt n⌋₊ ≥ Real.log n / 4 := by
    have hfloor_ge : (⌊Real.sqrt n⌋₊ : ℝ) ≥ Real.sqrt n / 2 := by linarith [sub_one_lt_floor (Real.sqrt n)]
    calc Real.log ⌊Real.sqrt n⌋₊ ≥ log (Real.sqrt n / 2) := log_le_log (by positivity) hfloor_ge
      _ = Real.log n / 2 - Real.log 2 := by rw [log_div hsqrt_pos.ne' two_ne_zero, log_sqrt hnpos.le]
      _ ≥ Real.log n / 4 := by
          have : Real.log n ≥ 4 * Real.log 2 := by
            calc Real.log n ≥ Real.log 16 := log_le_log ofNat_pos' <| ofNat_le_cast.mpr hn16
              _ = 4 * Real.log 2 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
          linarith
  have hbound := hN₀ n ((le_max_left ..).trans (le_of_max_le_right hn))
  simp only [Function.comp_apply, Real.dist_eq, sub_zero] at hbound
  have h_sqrt_log : Real.sqrt n * Real.log n < ε * Real.log 2 * n / (8 * (M + 1)) := by
    have : Real.sqrt n * Real.log n / n < ε * Real.log 2 / (8 * (M + 1)) := by
      linarith [(abs_lt.mp hbound).2, (by positivity : Real.sqrt n * Real.log n / n ≥ 0)]
    calc Real.sqrt n * Real.log n = Real.sqrt n * Real.log n / n * n := by field_simp
      _ < ε * Real.log 2 / (8 * (M + 1)) * n := by gcongr
      _ = _ := by ring
  calc (primeCounting ⌊Real.sqrt n⌋₊ : ℝ) * (M * Real.log n * Real.log n / Real.log 2)
      ≤ 3 / 2 * (⌊Real.sqrt n⌋₊ / Real.log ⌊Real.sqrt n⌋₊) *
          (M * Real.log n * Real.log n / Real.log 2) := by gcongr
    _ ≤ 3 / 2 * (Real.sqrt n / (Real.log n / 4)) *
          (M * Real.log n * Real.log n / Real.log 2) := by gcongr; exact floor_le hsqrt_pos.le
    _ = 6 * M * Real.sqrt n * Real.log n / Real.log 2 := by field_simp; ring
    _ ≤ 8 * (M + 1) * Real.sqrt n * Real.log n / Real.log 2 := by
        have h6le8 : (6 : ℝ) * M ≤ 8 * (M + 1) := by exact_mod_cast (by omega : 6 * M ≤ 8 * (M + 1))
        have := hlogn_pos; gcongr
    _ ≤ ε * n := by
        rw [div_le_iff₀ (log_pos one_lt_two)]
        calc 8 * (M + 1) * Real.sqrt n * Real.log n
          ≤ 8 * (M + 1) * (ε * Real.log 2 * n / (8 * (M + 1))) := le_of_lt (by nlinarith [h_sqrt_log])
        _ = ε * n * Real.log 2 := by field_simp

/-- The product `∏ p ≤ n, (1 - 1/p)` over primes tends to zero as `n → ∞`. -/
lemma prod_one_sub_one_div_prime_tendsto_zero :
    Filter.Tendsto (fun n ↦ ∏ p ∈ filter Prime (range n), (1 - 1 / (p : ℝ))) .atTop (nhds 0) := by
  have h_exp_neg_sum : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (-∑ p ∈ filter Prime (range n), (1 / p : ℝ))) .atTop (nhds 0) := by
    have h_not_summable : ¬Summable (fun p : ℕ ↦ if p.Prime then (1 / p : ℝ) else 0) := by
      have h_primes : ¬Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) := by
        convert Primes.not_summable_one_div
      contrapose! h_primes
      convert h_primes.comp_injective (fun a b h ↦ Subtype.ext h) using 1
      ext ⟨p, hp⟩
      simp [hp]
    have h_diverge : Filter.Tendsto
        (fun n : ℕ ↦ ∑ p ∈ range n, if p.Prime then (1 / p : ℝ) else 0) .atTop .atTop :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ ↦ by positivity)).mp h_not_summable
    simpa [sum_filter] using h_diverge
  refine squeeze_zero (fun n ↦ prod_nonneg fun _ hx ↦
    sub_nonneg.mpr <| div_le_self zero_le_one <| mod_cast (mem_filter.mp hx).2.pos) ?_ h_exp_neg_sum
  intro n
  rw [exp_neg, exp_sum, ← prod_inv_distrib]
  refine prod_le_prod (fun _ hx ↦ sub_nonneg.mpr <| div_le_self zero_le_one <|
    mod_cast (mem_filter.mp hx).2.pos) fun _ _ ↦ ?_
  rw [← Real.exp_neg]
  exact (Real.add_one_le_exp _).trans' (by norm_num)

/-- For any `ε > 0`, there exists `a ≠ 0` with `φ(a)/a < ε`. -/
lemma exists_phi_div_self_lt {ε : ℝ} (hε : 0 < ε) : ∃ a : ℕ, a ≠ 0 ∧ (a.totient : ℝ) / a < ε := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∏ p ∈ filter Prime (range n), (1 - 1 / (p : ℝ)) < ε :=
    (prod_one_sub_one_div_prime_tendsto_zero.eventually (gt_mem_nhds hε)).exists
  use ∏ p ∈ filter Prime (range n), p
  rw [totient_eq_div_primeFactors_mul, primeFactors_prod]
  · rw [Nat.div_self] <;> norm_num
    · rw [← Finset.prod_div_distrib]
      refine ⟨prod_ne_zero_iff.mpr fun p hp ↦ (mem_filter.mp hp).2.ne_zero, ?_⟩
      convert hn using 1
      exact prod_congr rfl fun x hx ↦ by
        rw [cast_sub <| succ_le_of_lt (mem_filter.mp hx).2.pos]
        simp [sub_div, (mem_filter.mp hx).2.ne_zero]
    · exact fun _ _ hi' ↦ hi'.pos
  · aesop

/-- The prime counting function satisfies `π(n) = o(n)` as `n → ∞`. -/
lemma primeCounting_is_o_id :
    IsLittleO .atTop (fun n ↦ (primeCounting n : ℝ)) (fun n ↦ (n : ℝ)) := by
  refine isLittleO_iff.mpr fun ε hε ↦ ?_
  obtain ⟨a, ha_ne_zero, ha_bound⟩ : ∃ a : ℕ, a ≠ 0 ∧ (a.totient : ℝ) / a < ε / 2 :=
    exists_phi_div_self_lt (half_pos hε)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N,
      (primeCounting' n : ℝ) ≤ (a.totient : ℝ) / a * n + (a.totient : ℝ) + primeCounting' (a + 1) := by
    refine ⟨a + 1 + 1, fun n hn ↦ ?_⟩
    have := primeCounting'_add_le ha_ne_zero (lt_succ_self a) (n - (a + 1))
    simp only [ne_eq, ge_iff_le, primeCounting'] at *
    rw [div_mul_eq_mul_div, div_add', div_add', le_div_iff₀] <;> norm_cast <;> try positivity
    rw [show a + 1 + (n - (a + 1)) = n by rw [add_tsub_cancel_of_le (by linarith)]] at this
    nlinarith [Nat.zero_le (φ a), Nat.zero_le (count Nat.Prime (a + 1)),
      Nat.zero_le ((n - (a + 1)) / a), Nat.div_mul_le_self (n - (a + 1)) a,
      Nat.sub_add_cancel (by linarith : a + 1 ≤ n)]
  have hN_primeCounting : ∀ᶠ n in .atTop, (primeCounting n : ℝ) ≤
      (totient a : ℝ) / a * (n : ℝ) + (totient a : ℝ) + primeCounting' (a + 1) + 1 := by
    simp only [ne_eq, ge_iff_le, primeCounting', primeCounting, Filter.eventually_atTop] at *
    refine ⟨N + 1, fun b hb ↦ ?_⟩
    specialize hN (b + 1) (by linarith)
    simp_all only [count_succ, cast_add, cast_ite, cast_one, CharP.cast_eq_zero]
    have h_phi_le : (φ a : ℝ) / a ≤ 1 := by
      rw [div_le_iff₀ (cast_pos.mpr <| pos_of_ne_zero ha_ne_zero)]
      simp [one_mul, totient_le a]
    nlinarith
  norm_num at *
  obtain ⟨M, hM⟩ := hN_primeCounting
  let C := (φ a : ℝ) + primeCounting' (a + 1) + 1
  refine ⟨M + ⌈C / (ε / 2)⌉₊ + 1, fun n hn ↦ ?_⟩
  have h_ceil := le_ceil (C / (ε / 2))
  have h_cancel := mul_div_cancel₀ C (by positivity : ε / 2 ≠ 0)
  have h_n_ge : (n : ℝ) ≥ M + ⌈C / (ε / 2)⌉₊ + 1 := by exact_mod_cast hn
  nlinarith [hM n (by linarith)]

@[blueprint
  "bound-score-4"
  (statement := /-- If $n$ sufficiently large depending on $L, \varepsilon$, then
$\sum_{n/L < p \leq n} \frac{n}{p} \log \frac{n}{p} \leq \varepsilon n$. -/)
  (proof := /-- Bound $\frac{n}{p}$ by $L$ and use the prime number theorem (or the Chebyshev bound). -/)
  (discussion := 517)
  (latexEnv := "sublemma")]
theorem Params.initial.bound_score_4 (ε : ℝ) (hε : ε > 0) (L : ℕ) :
    ∀ᶠ n in .atTop, ∀ P : Params, P.L = L → P.n = n → ∑ p ∈ filter (·.Prime) (Icc (P.n / P.L + 1) P.n),
      (P.n / p) * Real.log (P.n / p) ≤ ε * P.n := by
  have h_term_bound : ∀ (n L : ℕ), 0 < n → 0 < L → ∀ p ∈ Finset.filter (·.Prime) (Icc (n / L + 1) n),
      ((n : ℝ) / p) * Real.log (n / p) ≤ L * Real.log L := by
    intro n L hn hL p hp
    have hp_Icc := Finset.mem_Icc.mp (mem_filter.mp hp).1
    have hp_prime : p.Prime := (mem_filter.mp hp).2
    have h_div_bound : (n / p : ℝ) ≤ L := by
      rw [div_le_iff₀ (cast_pos.mpr hp_prime.pos)]
      norm_cast
      nlinarith [Nat.div_add_mod n L, Nat.mod_lt n hL, hp_Icc.1, hp_Icc.2]
    gcongr
    · exact log_nonneg <| by rw [le_div_iff₀ (cast_pos.mpr hp_prime.pos)]; norm_cast; grind
    · exact div_pos (cast_pos.mpr hn) (cast_pos.mpr hp_prime.pos)
  have h_num_terms : ∀ (n L : ℕ), 0 < n → 0 < L →
      (Finset.filter (·.Prime) (Icc (n / L + 1) n)).card ≤ primeCounting n := by
    intro n L _ _
    rw [primeCounting, primeCounting', count_eq_card_filter_range]
    exact card_mono fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      linarith [Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1]), (mem_filter.mp hx).2⟩
  have h_bound : ∀ᶠ n in .atTop, ∀ P : Params, P.L = L → P.n = n → (∑ p ∈ filter (·.Prime) (Icc (P.n / P.L + 1) P.n),
        ((P.n : ℝ) / p) * Real.log (P.n / p)) ≤ (primeCounting P.n) * L * Real.log L := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn P hP₁ hP₂
    refine le_trans (Finset.sum_le_sum fun x hx ↦ h_term_bound _ _ (by linarith) P.hL_pos _ hx) ?_
    · simp_all only [gt_iff_lt, Finset.mem_filter, Finset.mem_Icc, and_imp, sum_const, nsmul_eq_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (mod_cast h_num_terms n L hn (by linarith [P.hL_pos]))
        (mul_nonneg (cast_nonneg _) (log_natCast_nonneg _))
  have h_tendsto : Filter.Tendsto (fun n ↦ (primeCounting n : ℝ) * L * Real.log L / n) .atTop (nhds 0) := by
    have := primeCounting_is_o_id
    rw [isLittleO_iff_tendsto] at this
    · convert this.const_mul (L * Real.log L) using 2 <;> ring
    · aesop
  have h_pi_bound : ∀ᶠ n in .atTop, (primeCounting n : ℝ) * L * Real.log L ≤ ε * n := by
    filter_upwards [h_tendsto.eventually (gt_mem_nhds (show 0 < ε by positivity)),
      Filter.eventually_gt_atTop 0] with n hn hn'
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n)] at hn
    linarith
  filter_upwards [h_bound, h_pi_bound] with n hn hn' P hP hP'
  exact le_trans (hn P hP hP') (by simpa [hP'] using hn')

@[blueprint
  "primeCounting-le-bound"
  (statement := /-- For all $n \geq 2$, one has $$\pi(n) \leq \sqrt{n} + \frac{2n \log 4}{\log n}.$$ -/)
  (proof := /-- By Chebyshev's bound, $\prod_{p \leq n} p \leq 4^n$, so
$\sum_{p \leq n} \log p \leq n \log 4$. The number of primes $p \leq \sqrt{n}$ is trivially
at most $\sqrt{n}$. For primes $p > \sqrt{n}$, we have $\log p > \frac{1}{2} \log n$, hence
$$\bigl(\pi(n) - \pi(\sqrt{n})\bigr) \cdot \tfrac{1}{2} \log n
  < \sum_{\sqrt{n} < p \leq n} \log p \leq n \log 4,$$
giving $\pi(n) - \pi(\sqrt{n}) < \frac{2n \log 4}{\log n}$. Adding $\pi(\sqrt{n}) \leq \sqrt{n}$
yields the result. -/)
  (latexEnv := "sublemma")]
lemma primeCounting_le_bound (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ Real.sqrt n + (2 * n * Real.log 4) / Real.log n := by
  have h_sum_log_bound :
      (∑ p ∈ filter Prime (Icc 1 n), Real.log p) ≤ n * Real.log 4 := by
    have h_prod_le : (∏ p ∈ filter Prime (Icc 1 n), p : ℕ) ≤ 4 ^ n := by
      convert primorial_le_4_pow n using 1; congr 1 with (_ | p) <;> aesop
    have h_prod_le_real : (∏ p ∈ filter Prime (Icc 1 n), (p : ℝ)) ≤ 4 ^ n := by
      rw [← cast_prod]; exact_mod_cast h_prod_le
    rw [← log_prod fun x hx ↦ cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop]
    have h_prod_pos : 0 < ∏ p ∈ filter Prime (Icc 1 n), (p : ℝ) :=
      prod_pos fun p hp ↦ cast_pos.mpr <| Prime.pos <| by aesop
    simpa using log_le_log h_prod_pos h_prod_le_real
  have h_large_primes :
      (∑ p ∈ filter Prime (Icc (⌊Real.sqrt n⌋₊ + 1) n), Real.log p) ≥
      (primeCounting n - primeCounting ⌊Real.sqrt n⌋₊) * Real.log (Real.sqrt n) := by
    have h_log_lower : ∀ p ∈ Finset.filter Prime (Icc (⌊Real.sqrt n⌋₊ + 1) n),
        Real.log p ≥ Real.log (Real.sqrt n) := fun p hp ↦ log_le_log (by positivity)
        (le_trans (lt_floor_add_one _ |> le_of_lt) (mod_cast (Finset.mem_Icc.mp (mem_filter.mp hp).1).1))
    refine le_trans ?_ (sum_le_sum h_log_lower)
    norm_num [primeCounting, primeCounting', count_eq_card_filter_range]
    rw [show Finset.filter Prime (Icc (n.sqrt + 1) n) =
      Finset.filter Prime (range (n + 1)) \ filter Nat.Prime (range (n.sqrt + 1)) from ?_, card_sdiff]
    · rw [cast_sub]
      · rw [inter_eq_left.mpr (filter_subset_filter _ <| range_mono <| succ_le_succ <| sqrt_le_self _)]
      · exact card_mono inter_subset_right
    · ext; simp [Finset.mem_Icc, Finset.mem_range, mem_sdiff]; grind
  have h_combined :
      (Nat.primeCounting n - Nat.primeCounting ⌊Real.sqrt n⌋₊) * Real.log (Real.sqrt n) ≤
      n * Real.log 4 := by
    refine le_trans h_large_primes <| h_sum_log_bound.trans' <| sum_le_sum_of_subset_of_nonneg ?_
        (fun _ _ _ ↦ log_nonneg <| one_le_cast.mpr <| Prime.pos <| by aesop)
    exact filter_subset_filter _ <| Icc_subset_Icc (succ_pos _) le_rfl
  have h_trivial : primeCounting ⌊Real.sqrt n⌋₊ ≤ Real.sqrt n := by
    have : primeCounting ⌊Real.sqrt n⌋₊ ≤ ⌊Real.sqrt n⌋₊ := by
      rw [primeCounting, primeCounting', count_eq_card_filter_range]
      calc (Finset.filter Prime (range (⌊Real.sqrt n⌋₊ + 1))).card
          ≤ (Finset.Ico 2 (⌊Real.sqrt n⌋₊ + 1)).card := card_le_card fun x hx ↦ Finset.mem_Ico.mpr
            ⟨Prime.two_le (mem_filter.mp hx).2, Finset.mem_range.mp (mem_filter.mp hx).1⟩
        _ ≤ ⌊Real.sqrt n⌋₊ := by simp
    exact le_trans (cast_le.mpr this) (floor_le (sqrt_nonneg _))
  rw [log_sqrt (cast_nonneg _)] at h_combined
  rw [add_div', le_div_iff₀] <;> nlinarith [log_pos <| show (n : ℝ) > 1 by norm_cast,
    log_le_sub_one_of_pos <| show (n : ℝ) > 0 by positivity]

/-- The ratio `π(n) / n → 0` as `n → ∞`. -/
lemma tendsto_primeCounting_div_id_zero :
    Filter.Tendsto (fun n ↦ (Nat.primeCounting n : ℝ) / n) .atTop (nhds 0) := by
  have h_upper_bound : ∀ n : ℕ, 2 ≤ n → (primeCounting n : ℝ) / n ≤ Real.sqrt n / n + (2 * Real.log 4) / Real.log n := by
    intro n hn
    rw [div_le_iff₀ (by positivity)]
    convert primeCounting_le_bound n hn using 1
    · ring_nf; norm_num [show n ≠ 0 by positivity]
  have h_tendsto : Filter.Tendsto (fun n : ℕ ↦ .sqrt n / n + (2 * Real.log 4) / Real.log n) .atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt n / n) .atTop (nhds 0) := by
      simpa [sqrt_div_self] using tendsto_inv_atTop_nhds_zero_nat.sqrt
    have h2 : Filter.Tendsto (fun n : ℕ ↦ (2 * Real.log 4) / Real.log n) .atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using h1.add h2
  exact squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ by
    rw [norm_of_nonneg (by positivity)]; exact h_upper_bound n hn⟩) h_tendsto

@[blueprint
  "bound-score-5"
  (statement := /-- If $n$ sufficiently large depending on $M, L, \varepsilon$, then
$\sum_{p \leq L} (M \log n + M L \pi(n)) \log L \leq \varepsilon n$. -/)
  (proof := /-- Use the prime number theorem (or the Chebyshev bound). -/)
  (discussion := 518)
  (latexEnv := "sublemma")]
theorem Params.initial.bound_score_5 (ε : ℝ) (hε : ε > 0) (M L : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ P : Params,
      P.M = M → P.L = L → P.n = n → ∑ _p ∈ Finset.filter (·.Prime) (Finset.Iic P.L),
          (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L ≤ ε * P.n := by
  have tendsto_log_div_atTop : Filter.Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ)) .atTop (nhds 0) := by
    suffices h : Filter.Tendsto (fun y : ℝ ↦ y * Real.log (1 / y)) (.map (1 / ·) .atTop) (nhds 0) by
      exact (h.comp (Filter.map_mono tendsto_natCast_atTop_atTop)).congr fun _ ↦ by grind
    norm_num at *
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using Real.continuous_mul_log.neg.tendsto 0)
  have h_pi_div_n_zero : Filter.Tendsto (fun n : ℕ ↦ (Nat.primeCounting n : ℝ) / n)
      .atTop (nhds 0) := tendsto_primeCounting_div_id_zero
  have h_sum_bound : Filter.Tendsto (fun n : ℕ ↦
      ((Nat.primeCounting L : ℝ) * (M * Real.log n + M * L ^ 2 * (Nat.primeCounting n : ℝ)) *
        Real.log L) / n) .atTop (nhds 0) := by
    convert Filter.Tendsto.const_mul ((primeCounting L : ℝ) * M * Real.log L)
      ((tendsto_log_div_atTop.const_mul 1).add (h_pi_div_n_zero.const_mul (L ^ 2 : ℝ))) using 2 <;>
      ring
  filter_upwards [h_sum_bound.eventually (gt_mem_nhds hε), Filter.eventually_gt_atTop 0] with n hn hn' P hM hL hn''
  rw [div_lt_iff₀ (by positivity)] at hn
  simp_all only [gt_iff_lt, mul_comm, mul_left_comm, mul_add, mul_assoc, sum_const]
  convert hn.le using 1
  · norm_num [primeCounting]
    ring_nf
    rw [primeCounting', count_eq_card_filter_range]
    norm_num [add_comm, sum_range_succ]
    ring_nf
    rw [show count Nat.Prime (1 + L) = (Finset.filter Prime (Iic L)).card from ?_]
    · ring_nf
    · rw [count_eq_card_filter_range, add_comm, range_eq_Ico]; rfl

@[blueprint
  "initial-score"
  (statement := /-- The score of the initial factorization can be taken to be $o(n)$.-/)
  (proof := /-- Pick $M$ large depending on $\varepsilon$, then $L$ sufficiently large depending
  on $M, \varepsilon$, then $n$ sufficiently large depending on $M,L,\varepsilon$, so that the
  bounds in Sublemma \ref{bound-score-1}, Sublemma \ref{bound-score-2},
  Sublemma \ref{bound-score-3}, Sublemma \ref{bound-score-4}, and Sublemma \ref{bound-score-5}
  each contribute at most $(\varepsilon/5) n$.  Then use Proposition \ref{initial-score-bound}.
  -/)
  (discussion := 519)
  (latexEnv := "proposition")]
theorem Params.initial.score (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in .atTop, ∃ P : Params, P.n = n ∧ P.initial.score P.L ≤ ε * n := by
  have h_bound_score_1 : ∀ᶠ M in .atTop, ∀ P : Params,
      P.M = M → P.n * log (1 - 1 / (P.M : ℝ))⁻¹ ≤ ε * P.n / 5 :=
    (initial.bound_score_1 (ε := ε / 5) (by positivity)).mono fun M hM P hP ↦ by linarith [hM P hP]
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp h_bound_score_1
  let M := max M₀ 2
  have hM : M > 1 ∧ ∀ P : Params, P.M = M → P.n * log (1 - 1 / (P.M : ℝ))⁻¹ ≤ ε * P.n / 5 :=
    ⟨by omega, fun P hP ↦ hM₀ _ (le_max_left _ _) _ hP⟩
  have h_bound_score_2 : ∀ᶠ L in .atTop, ∀ᶠ n in .atTop, ∀ P : Params,
      P.L = L → P.n = n → P.M = M → ∑ _p ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)),
        P.M * Real.log P.n ≤ ε * P.n / 5 :=
    (initial.bound_score_2 (ε / 5) (by positivity) M).mono fun L hL ↦
      hL.mono fun n hn P hPL hPn hPM ↦ by linarith [hn P hPL hPn hPM]
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp h_bound_score_2
  let L := max L₀ 1
  have h_bound_score_3 : ∀ᶠ n in .atTop, ∀ P : Params,
      P.M = M → P.n = n → ∑ _p ∈ Finset.filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
        P.M * Real.log P.n * Real.log P.n / Real.log 2 ≤ ε * P.n / 5 :=
    (initial.bound_score_3 (ε / 5) (by positivity) M).mono fun n hn P hPM hPn ↦ by grind
  have h_bound_score_4 : ∀ᶠ n in .atTop, ∀ P : Params,
      P.L = L → P.n = n → ∑ p ∈ Finset.filter (·.Prime) (Finset.Icc (P.n / P.L + 1) P.n),
        (P.n / p) * Real.log (P.n / p) ≤ ε * P.n / 5 :=
    (initial.bound_score_4 (ε / 5) (by linarith) L).mono fun n hn P hPL hPn ↦ by grind
  have h_bound_score_5 : ∀ᶠ n in .atTop, ∀ P : Params,
      P.M = M → P.L = L → P.n = n → ∑ _p ∈ filter (·.Prime) (Finset.Iic P.L),
        (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L ≤ ε * P.n / 5 :=
    (initial.bound_score_5 (ε / 5) (by positivity) M L).mono fun n hn P hPM hPL hPn ↦ by grind
  have h_exists_n₀ : ∃ n₀ : ℕ, ∀ n ≥ n₀, n > L * L ∧ (n / L : ℕ) > Real.sqrt n := by
    refine ⟨L^2 + L^2 + 1, fun n hn ↦ ⟨by grind, ?_⟩⟩
    have hmod : n % L < L := mod_lt n (by positivity)
    rw [gt_iff_lt, sqrt_lt' (Nat.cast_pos.mpr <| by nlinarith [div_add_mod n L, hmod])]
    have : n < (n / L)^2 := by
      have : n ≤ L * (n / L) + (L - 1) := by
        calc n = L * (n / L) + n % L := (div_add_mod n L).symm
          _ ≤ L * (n / L) + (L - 1) := by omega
      have : (n / L)^2 ≥ (L + 1)^2 := Nat.pow_le_pow_left (by nlinarith [div_add_mod n L, hmod]) 2
      nlinarith [div_add_mod n L, hmod]
    exact_mod_cast this
  filter_upwards [Filter.eventually_ge_atTop h_exists_n₀.choose, hL₀ L (le_max_left _ _),
    h_bound_score_3, h_bound_score_4, h_bound_score_5] with n hn hn2 hn3 hn4 hn5
  obtain ⟨hn_LL, hn_sqrt⟩ := h_exists_n₀.choose_spec n hn
  let P : Params := ⟨n, M, L, hM.1, by positivity, hn_LL, hn_sqrt⟩
  refine ⟨P, rfl, ?_⟩
  calc P.initial.score P.L ≤ _ := initial.score_bound P
    _ ≤ ε * P.n / 5 + ε * P.n / 5 + ε * P.n / 5 + ε * P.n / 5 + ε * P.n / 5 := by
        gcongr <;> first | exact hM.2 P rfl | exact hn2 P rfl rfl rfl |
          exact hn3 P rfl rfl | exact hn4 P rfl rfl | exact hn5 P rfl rfl rfl
    _ = ε * n := by ring

@[blueprint
  "erdos-sol-1"
  (statement := /-- One can find a balanced factorization of $n!$ with cardinality at least
  $n - n / \log n - o(n / \log n)$.--/)
  (proof := /-- Combine Proposition \ref{initial-score} with Proposition \ref{card-bound} and
  the Stirling approximation.-/)
  (latexEnv := "theorem")]
theorem Solution_1 (ε : ℝ) (_hε : ε > 0) : ∀ᶠ n in .atTop, ∃ f : Factorization n,
    f.total_imbalance = 0 ∧ f.a.card ≥ n - n / Real.log n - ε * n / Real.log n := by
  refine .of_forall fun n ↦
    ⟨⟨Multiset.Ico 1 (n + 1), fun _ hm ↦ ?_, fun _ hm ↦ ?_⟩, ?_, ?_⟩
  · exact le_of_lt_succ (Multiset.mem_Ico.mp hm).2
  · exact (Multiset.mem_Ico.mp hm).1
  · rw [Factorization.total_imbalance]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    simp only [Factorization.balance, Factorization.sum, Int.natAbs_eq_zero, sub_eq_zero]
    norm_cast
    simp only [Multiset.Ico, ← sum_eq_multiset_sum]
    have : ∀ {m : ℕ}, m > 0 →
        m.factorial.factorization p = ∑ k ∈ Ico 1 (m + 1), k.factorization p := by
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
    have : (0 : ℝ) ≤ n / Real.log n ∧ (0 : ℝ) ≤ ε * n / Real.log n :=
      ⟨by positivity, by positivity⟩
    linarith

@[blueprint
  "erdos-sol-2"
  (statement := /-- One can find a factor $n!$ into at least $n/2 - n / 2\log n - o(n / \log n)$
  numbers of size at most $n^2$.--/)
  (proof := /-- Group the factorization arising in Theorem \ref{erdos-sol-1} into pairs, using
  Lemma \ref{balance-zero}.-/)
  (latexEnv := "theorem")]
theorem Solution_2 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in .atTop, ∃ (t : ℕ) (a : Fin t → ℕ), ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n ^ 2 ∧
        t ≥ (n / 2) - n / (2 * Real.log n) - ε * n / Real.log n := by
  norm_num
  refine ⟨2, fun b _hb ↦ ⟨b, (· + 1), ?_, ?_⟩⟩ <;> norm_num
  · exact prod_range_add_one_eq_factorial b ▸ (prod_range (· + 1)).symm
  · exact fun i ↦ ⟨by nlinarith [i.is_lt],
      le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (by linarith) (by positivity)) (by positivity)⟩

end Erdos392
