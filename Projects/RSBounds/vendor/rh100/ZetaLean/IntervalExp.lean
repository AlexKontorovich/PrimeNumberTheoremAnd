module

public import Mathlib
public import ZetaLean.Rigor

@[expose] public section

/-!
# Certified interval `exp` and `log`

The first stone of rung 3's numeric half.  `ZetaLean/DHZeroCriterion.lean`
reduced the Davenport-Heilbronn theorem to two interval inequalities about
`DH`; discharging them inside the kernel requires evaluating terms
`n^{-s} = exp(-s·log n)` with certified enclosures.  This file supplies the
real elementary functions that evaluation is made of, on the `Interval`
layer of `ZetaLean/Rigor.lean`:

* `Interval.exp1`, certified `exp` on intervals inside `[-1, 1]`: Taylor
  partial sums at the rational endpoints, inflated by the Lagrange remainder
  of Mathlib's `Real.exp_bound`, tightened by monotonicity (endpoints
  suffice; no interval Taylor needed).
* `Interval.expI`: `exp` on intervals inside `[-2^k, 2^k]`, by `k`
  halvings and certified squarings (`exp t = exp(t/2)²`).
* `Interval.log1`: certified `log` on intervals inside `(0, 2)`, from the
  alternating series bound `Real.abs_log_sub_add_sum_range_le`, again
  tightened by monotonicity.
* `Interval.log2I`: an enclosure of `log 2 = -log(1/2)`, the anchor for
  extending `log1` to all positive rationals by binary reduction
  (`log q = k·log 2 + log(q/2^k)`, future work).

Every operation returns an interval together with a containment theorem; the
smoke tests at the bottom (`exp_one_gt`, …) kernel-check concrete digits of
`e` and `log 2` end-to-end, which is the point: the same pipeline, pointed
at `DH`, is what will eventually discharge the two hypotheses of
`davenport_heilbronn_of_certified_disk`.
-/

namespace ZetaLean.Interval

open Finset

/-! ### Certified `exp` on `[-1, 1]` -/

/-- Rational Taylor partial sum of `exp`. -/
def expSum (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, q ^ i / i.factorial

/-- Rational Lagrange remainder bound, matching `Real.exp_bound`. -/
def expRem (n : ℕ) (q : ℚ) : ℚ :=
  |q| ^ n * ((n + 1) / (n.factorial * n))

private lemma expSum_cast (n : ℕ) (q : ℚ) :
    ((expSum n q : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ i / i.factorial := by
  unfold expSum
  push_cast
  rfl

private lemma expRem_cast (n : ℕ) (q : ℚ) :
    ((expRem n q : ℚ) : ℝ) = |(q : ℝ)| ^ n * ((n + 1) / (n.factorial * n)) := by
  unfold expRem
  push_cast
  rfl

/-- Taylor lower bound for `exp` at a rational point. -/
theorem exp_lower {n : ℕ} (hn : 0 < n) {q : ℚ} (hq : |q| ≤ 1) :
    ((expSum n q - expRem n q : ℚ) : ℝ) ≤ Real.exp q := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  have h1 := (abs_sub_le_iff.mp h).1
  have h2 := (abs_sub_le_iff.mp h).2
  push_cast
  rw [expSum_cast, expRem_cast]
  have hsucc : (n.succ : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hsucc] at h1 h2
  linarith

/-- Taylor upper bound for `exp` at a rational point. -/
theorem exp_upper {n : ℕ} (hn : 0 < n) {q : ℚ} (hq : |q| ≤ 1) :
    Real.exp q ≤ ((expSum n q + expRem n q : ℚ) : ℝ) := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  have h1 := (abs_sub_le_iff.mp h).1
  have h2 := (abs_sub_le_iff.mp h).2
  push_cast
  rw [expSum_cast, expRem_cast]
  have hsucc : (n.succ : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hsucc] at h1 h2
  linarith

/-- Certified `exp` on an interval inside `[-1, 1]`: Taylor at the two
endpoints plus monotonicity.  The `max` in `hi` only discharges the
`lo ≤ hi` obligation; soundness never routes through it. -/
def exp1 (n : ℕ) (x : Interval) : Interval :=
  { lo := expSum n x.lo - expRem n x.lo,
    hi := max (expSum n x.hi + expRem n x.hi) (expSum n x.lo - expRem n x.lo),
    le := le_max_right _ _ }

theorem contains_exp1 {n : ℕ} (hn : 0 < n) {x : Interval} {t : ℝ}
    (hx : x.contains t) (hlo : -1 ≤ x.lo) (hhi : x.hi ≤ 1) :
    (exp1 n x).contains (Real.exp t) := by
  have hqlo : |x.lo| ≤ 1 := abs_le.mpr ⟨hlo, x.le.trans hhi⟩
  have hqhi : |x.hi| ≤ 1 := abs_le.mpr ⟨hlo.trans x.le, hhi⟩
  refine ⟨?_, ?_⟩
  · exact (exp_lower hn hqlo).trans (Real.exp_le_exp.mpr hx.1)
  · have h2 : Real.exp t ≤ ((expSum n x.hi + expRem n x.hi : ℚ) : ℝ) :=
      (Real.exp_le_exp.mpr hx.2).trans (exp_upper hn hqhi)
    refine h2.trans ?_
    change ((expSum n x.hi + expRem n x.hi : ℚ) : ℝ) ≤ ((exp1 n x).hi : ℝ)
    rw [exp1, Rat.cast_max]
    exact le_max_left _ _

/-! ### Range extension by halving and squaring -/

/-- Exact halving (tighter than routing through `mul`). -/
def halve (x : Interval) : Interval :=
  { lo := x.lo / 2, hi := x.hi / 2,
    le := by have := x.le; linarith }

theorem contains_halve {x : Interval} {t : ℝ} (hx : x.contains t) :
    x.halve.contains (t / 2) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩ <;> simp only [halve] <;> push_cast <;> linarith

/-- Certified `exp` on an interval inside `[-2^k, 2^k]`: halve `k` times
into `[-1, 1]`, take `exp1`, square back up (`exp t = exp(t/2)²`). -/
def expI (n : ℕ) : ℕ → Interval → Interval
  | 0, x => exp1 n x
  | k + 1, x =>
    let y := expI n k x.halve
    y.mul y

theorem contains_expI (n : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : Interval) (t : ℝ), x.contains t →
      -(2 ^ k : ℚ) ≤ x.lo → x.hi ≤ (2 ^ k : ℚ) →
      (expI n k x).contains (Real.exp t)
  | 0, x, t, hx, hlo, hhi => by
    refine contains_exp1 hn hx ?_ ?_
    · simpa using hlo
    · simpa using hhi
  | k + 1, x, t, hx, hlo, hhi => by
    rw [pow_succ] at hlo hhi
    have hy : (expI n k x.halve).contains (Real.exp (t / 2)) := by
      refine contains_expI n hn k x.halve (t / 2) (contains_halve hx) ?_ ?_
      · simp only [halve]; linarith
      · simp only [halve]; linarith
    have hmul := Interval.contains_mul hy hy
    rw [show Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t by
      rw [← Real.exp_add]; ring_nf] at hmul
    exact hmul

/-! ### Certified `log` on `(0, 2)` -/

/-- Rational partial sum of the series for `-log(1-q)`. -/
def logSum (n : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, q ^ (i + 1) / (i + 1)

/-- Rational tail bound, matching `Real.abs_log_sub_add_sum_range_le`. -/
def logRem (n : ℕ) (q : ℚ) : ℚ :=
  |q| ^ (n + 1) / (1 - |q|)

private lemma logSum_cast (n : ℕ) (q : ℚ) :
    ((logSum n q : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ (i + 1) / (i + 1) := by
  unfold logSum
  push_cast
  rfl

private lemma logRem_cast (n : ℕ) (q : ℚ) :
    ((logRem n q : ℚ) : ℝ) = |(q : ℝ)| ^ (n + 1) / (1 - |(q : ℝ)|) := by
  unfold logRem
  push_cast
  rfl

/-- Series lower bound for `log (1 - q)` at a rational point. -/
theorem log_one_sub_lower {n : ℕ} {q : ℚ} (hq : |q| < 1) :
    ((-logSum n q - logRem n q : ℚ) : ℝ) ≤ Real.log (1 - q) := by
  have hq' : |(q : ℝ)| < 1 := by exact_mod_cast hq
  have h := Real.abs_log_sub_add_sum_range_le hq' n
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  push_cast
  rw [logSum_cast, logRem_cast]
  linarith

/-- Series upper bound for `log (1 - q)` at a rational point. -/
theorem log_one_sub_upper {n : ℕ} {q : ℚ} (hq : |q| < 1) :
    Real.log (1 - q) ≤ ((-logSum n q + logRem n q : ℚ) : ℝ) := by
  have hq' : |(q : ℝ)| < 1 := by exact_mod_cast hq
  have h := Real.abs_log_sub_add_sum_range_le hq' n
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  push_cast
  rw [logSum_cast, logRem_cast]
  linarith

/-- Certified `log` on an interval inside `(0, 2)`: the series for
`log(1-x)` at the endpoints `x = 1 - lo`, `x = 1 - hi`, plus monotonicity. -/
def log1 (n : ℕ) (x : Interval) : Interval :=
  { lo := -logSum n (1 - x.lo) - logRem n (1 - x.lo),
    hi := max (-logSum n (1 - x.hi) + logRem n (1 - x.hi))
      (-logSum n (1 - x.lo) - logRem n (1 - x.lo)),
    le := le_max_right _ _ }

theorem contains_log1 {n : ℕ} {x : Interval} {t : ℝ}
    (hx : x.contains t) (hlo : 0 < x.lo) (hhi : x.hi < 2) :
    (log1 n x).contains (Real.log t) := by
  have hlo2 : x.lo < 2 := lt_of_le_of_lt x.le hhi
  have hhi0 : 0 < x.hi := lt_of_lt_of_le hlo x.le
  have hq1 : |(1 - x.lo : ℚ)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hq2 : |(1 - x.hi : ℚ)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by exact_mod_cast hlo) hx.1
  have hxlo : (0 : ℝ) < (x.lo : ℝ) := by exact_mod_cast hlo
  have hxhi : (0 : ℝ) < (x.hi : ℝ) := by exact_mod_cast hhi0
  have hcast_lo : (1 : ℝ) - ((1 - x.lo : ℚ) : ℝ) = (x.lo : ℝ) := by push_cast; ring
  have hcast_hi : (1 : ℝ) - ((1 - x.hi : ℚ) : ℝ) = (x.hi : ℝ) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h1 := log_one_sub_lower (n := n) hq1
    rw [hcast_lo] at h1
    exact h1.trans ((Real.log_le_log_iff hxlo ht0).mpr hx.1)
  · have h2 := log_one_sub_upper (n := n) hq2
    rw [hcast_hi] at h2
    have h3 : Real.log t ≤ ((-logSum n (1 - x.hi) + logRem n (1 - x.hi) : ℚ) : ℝ) :=
      ((Real.log_le_log_iff ht0 hxhi).mpr hx.2).trans h2
    refine h3.trans ?_
    change _ ≤ (((log1 n x).hi : ℚ) : ℝ)
    rw [log1, Rat.cast_max]
    exact le_max_left _ _

/-- An enclosure of `log 2 = -log(1/2)`. -/
def log2I (n : ℕ) : Interval :=
  (log1 n (Interval.exact (1 / 2))).neg

theorem contains_log2I (n : ℕ) : (log2I n).contains (Real.log 2) := by
  have h := contains_log1 (n := n) (Interval.contains_exact (1 / 2))
    (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  have h2 := Interval.contains_neg h
  rw [show -Real.log ((1 / 2 : ℚ) : ℝ) = Real.log 2 by
    rw [← Real.log_inv]; norm_num] at h2
  exact h2

/-! ### `log` of any positive rational -/

/-- Certified `log q` for a positive rational, by the binary reduction the
module docstring promised: `log q = k·log 2 + log (q / 2^k)`, with the second
summand landed in the domain of `log1`.  The caller picks `k`;
`contains_logQ` demands exactly the side conditions that make the choice
correct, and both are `norm_num`-decidable at any concrete call site. -/
def logQ (n k : ℕ) (q : ℚ) : Interval :=
  ((Interval.exact (k : ℚ)).mul (log2I n)).add (log1 n (Interval.exact (q / 2 ^ k)))

theorem contains_logQ {n k : ℕ} {q : ℚ} (h0 : 0 < q / 2 ^ k) (h2 : q / 2 ^ k < 2) :
    (logQ n k q).contains (Real.log q) := by
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  have hq0 : (0 : ℚ) < q := by
    have := mul_pos h0 h2k
    rwa [div_mul_cancel₀ _ h2k.ne'] at this
  have hid : Real.log q = (k : ℝ) * Real.log 2 + Real.log ((q : ℝ) / 2 ^ k) := by
    rw [Real.log_div (by exact_mod_cast hq0.ne') (by positivity), Real.log_pow]
    ring
  have hA := Interval.contains_mul (Interval.contains_exact (k : ℚ)) (contains_log2I n)
  have hB := contains_log1 (n := n) (Interval.contains_exact (q / 2 ^ k)) h0 h2
  have hC := Interval.contains_add hA hB
  have hcast : ((q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by push_cast; ring
  rw [hcast] at hC
  rw [hid, show ((k : ℝ)) = (((k : ℚ) : ℝ)) by push_cast; rfl]
  exact hC

/-! ### Smoke tests: kernel-checked digits of `e` and `log 2`

These are the end-to-end proof that the pipeline computes: the same
machinery, pointed at `DH`'s Dirichlet terms, is what will discharge the
hypotheses of `davenport_heilbronn_of_certified_disk`. -/

theorem exp_one_gt : (2.71828 : ℝ) < Real.exp 1 := by
  obtain ⟨h1, -⟩ := contains_exp1 (n := 10) (by norm_num) (x := Interval.exact 1)
    (Interval.contains_exact 1) (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  push_cast at h1
  refine lt_of_lt_of_le ?_ h1
  norm_num [exp1, Interval.exact, expSum, expRem, Finset.sum_range_succ, Nat.factorial]

theorem exp_one_lt : Real.exp 1 < (2.71829 : ℝ) := by
  obtain ⟨-, h2⟩ := contains_exp1 (n := 10) (by norm_num) (x := Interval.exact 1)
    (Interval.contains_exact 1) (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  push_cast at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [exp1, Interval.exact, expSum, expRem, Finset.sum_range_succ, Nat.factorial]

theorem exp_four_lt : Real.exp 4 < (54.6 : ℝ) := by
  have h := contains_expI 8 (by norm_num) 2 (Interval.exact 4) ((4 : ℚ) : ℝ)
    (Interval.contains_exact 4) (by norm_num [Interval.exact]) (by norm_num [Interval.exact])
  obtain ⟨-, h2⟩ := h
  push_cast at h2
  refine lt_of_le_of_lt h2 ?_
  norm_num [expI, exp1, halve, Interval.exact, Interval.mul, expSum, expRem,
    Finset.sum_range_succ, Nat.factorial]

theorem log_two_gt : (0.6931 : ℝ) < Real.log 2 := by
  obtain ⟨h1, -⟩ := contains_log2I 20
  refine lt_of_lt_of_le ?_ h1
  norm_num [log2I, log1, Interval.exact, Interval.neg, logSum, logRem,
    Finset.sum_range_succ]

theorem log_two_lt : Real.log 2 < (0.6932 : ℝ) := by
  obtain ⟨-, h2⟩ := contains_log2I 20
  refine lt_of_le_of_lt h2 ?_
  norm_num [log2I, log1, Interval.exact, Interval.neg, logSum, logRem,
    Finset.sum_range_succ]

theorem log_ten_gt : (2.30257 : ℝ) < Real.log 10 := by
  obtain ⟨h1, -⟩ := contains_logQ (n := 20) (k := 3) (q := 10)
    (by norm_num) (by norm_num)
  refine lt_of_lt_of_le ?_ h1
  norm_num [logQ, log2I, log1, Interval.exact, Interval.neg, Interval.mul,
    Interval.add, logSum, logRem, Finset.sum_range_succ]

theorem log_ten_lt : Real.log 10 < (2.30259 : ℝ) := by
  obtain ⟨-, h2⟩ := contains_logQ (n := 20) (k := 3) (q := 10)
    (by norm_num) (by norm_num)
  refine lt_of_le_of_lt h2 ?_
  norm_num [logQ, log2I, log1, Interval.exact, Interval.neg, Interval.mul,
    Interval.add, logSum, logRem, Finset.sum_range_succ]

end ZetaLean.Interval
