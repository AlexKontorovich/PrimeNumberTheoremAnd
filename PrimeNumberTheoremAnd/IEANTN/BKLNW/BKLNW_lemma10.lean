/-
PrimeNumberTheoremAnd/IEANTN/BKLNW/BKLNW_lemma10.lean

**BKLNW Lemma 10** (arXiv:2002.11068, `bklnw_paper.txt` lines 775-809, §3.5), formalized
*without* its Table 13 numerical input.

Paper statement (lines 775-784, equations (3.27)/(3.28)/(3.29)):

> Let `k = 1, …, 5`.  Let `0 < a < b` such that `a > e^{k+1}`.  Let `p_n` denote the `n`-th
> prime, with `p_{n0}` and `p_{n1}` being the smallest primes greater than `a` and `b`
> respectively.  Let
>     (3.27)   `D_k(a,b) = max_{n0 ≤ n ≤ n1} (log p_n)^k · (p_n − θ(p_{n−1})) / p_n`.
> If
>     (3.28)   `D_k(a,b) < (k+1)^{k+1}`
> then
>     (3.29)   `θ(x) ≥ x − D_k(a,b)·x/(log x)^k`  when `a ≤ x ≤ b`.

The paper's proof (lines 786-809) has exactly two ingredients, both formalized below with
no `sorry`:

* `θ` is constant between consecutive primes, so on `[p_{n−1}, p_n)` one has
  `θ(x) = θ(p_{n−1}) = p_n (1 − D_k(n)/(log p_n)^k)`  (lines 790-794);
* `φ(x) = x(1 − c/(log x)^k)` is increasing as long as `c < (k+1)^{k+1}`, because
  `φ'(x) = 1 + c(k − log x)/(log x)^{k+1}` has its minimum at `x = e^{k+1}`, where it
  equals `1 − c/(k+1)^{k+1} > 0`  (lines 790-796, our `phi_strictMonoOn`).

Everything expensive in BKLNW's use of Lemma 10 — the max over all primes below
`7·10^11` recorded in Table 13 — stays a *hypothesis* here (`hD`), so this file is
unconditional and depends only on Mathlib.  `ConditionalCells.lean` in this directory
discharges Table 15 cells against that hypothesis.

Faithfulness note on the shape of `hD`.  Rather than index primes by `Nat.nth Nat.Prime`,
we use the pointwise quantity `Dterm k x` (`(log p)^k (p − θ x)/p`, `p` = least prime
`> x`).  `Dterm_eq_of_consecutive` below proves this is *literally* the paper's `D_k(n)`
whenever `x ∈ [p_{n−1}, p_n)` (paper line 790), and `bklnw_lemma_10_paper_form` restates the whole lemma
with a hypothesis quantified over consecutive prime pairs `(p_{n−1}, p_n)`, exactly as
(3.27) is written.  So `∀ x ∈ [a,b], Dterm k x ≤ D` is precisely `D_k(a,b) ≤ D`.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Real Chebyshev

namespace BKLNW.Lemma10

/-! ## 1.  The next prime above a real number

`p_n` in (3.27) is "the smallest prime greater than `x`" once `x` runs through
`[p_{n−1}, p_n)`; this section builds that operation. -/

theorem exists_prime_gt (x : ℝ) : ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (⌊x⌋₊ + 1)
  refine ⟨p, hp, ?_⟩
  calc x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    _ = ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (p : ℝ) := by exact_mod_cast hpge

/-- The least prime strictly greater than `x` (the paper's `p_n` for `x ∈ [p_{n−1}, p_n)`). -/
noncomputable def nextPrime (x : ℝ) : ℕ := sInf {p : ℕ | p.Prime ∧ x < (p : ℝ)}

private theorem nextPrime_mem (x : ℝ) : nextPrime x ∈ {p : ℕ | p.Prime ∧ x < (p : ℝ)} := by
  obtain ⟨p, hp, hxp⟩ := exists_prime_gt x
  exact Nat.sInf_mem ⟨p, hp, hxp⟩

theorem nextPrime_prime (x : ℝ) : (nextPrime x).Prime := (nextPrime_mem x).1

theorem lt_nextPrime (x : ℝ) : x < ((nextPrime x : ℕ) : ℝ) := (nextPrime_mem x).2

theorem nextPrime_le {x : ℝ} {q : ℕ} (hq : q.Prime) (hxq : x < (q : ℝ)) :
    nextPrime x ≤ q := Nat.sInf_le ⟨hq, hxq⟩

theorem log_nextPrime_pos (x : ℝ) : 0 < Real.log ((nextPrime x : ℕ) : ℝ) := by
  have h2 : (2 : ℕ) ≤ nextPrime x := (nextPrime_prime x).two_le
  have : (2 : ℝ) ≤ ((nextPrime x : ℕ) : ℝ) := by exact_mod_cast h2
  exact Real.log_pos (by linarith)

/-- (3.27)'s quantity, evaluated pointwise: `D_k(n) = (log p_n)^k (p_n − θ(x))/p_n` for
`x ∈ [p_{n−1}, p_n)`, using `θ(x) = θ(p_{n−1})` (paper lines 790-794). -/
noncomputable def Dterm (k : ℕ) (x : ℝ) : ℝ :=
  (Real.log ((nextPrime x : ℕ) : ℝ)) ^ k * (((nextPrime x : ℕ) : ℝ) - θ x) /
    ((nextPrime x : ℕ) : ℝ)

/-! ## 2.  The paper's monotone auxiliary function `φ`

`φ(x) = x(1 − c/(log x)^k) = x − c·x/(log x)^k` (paper line 795). -/

/-- `φ_D,k(x) = x − D·x/(log x)^k`, the right-hand side of (3.29). -/
noncomputable def phi (D : ℝ) (k : ℕ) (x : ℝ) : ℝ := x - D * x / (Real.log x) ^ k

theorem phi_eq_mul (D : ℝ) (k : ℕ) {x : ℝ} (hx : 1 < x) :
    phi D k x = x * (1 - D / (Real.log x) ^ k) := by
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hne : (Real.log x) ^ k ≠ 0 := (pow_pos hlog k).ne'
  unfold phi
  field_simp

/-- `φ'(x) = 1 + D(k − log x)/(log x)^{k+1}` (paper line 797), written with `k = m+1`. -/
theorem hasDerivAt_phi (D : ℝ) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (phi D (m + 1))
      (1 - D * ((Real.log x - ((m : ℝ) + 1)) / (Real.log x) ^ (m + 2))) x := by
  have hx0 : x ≠ 0 := by positivity
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hlogne0 : Real.log x ≠ 0 := ne_of_gt hlog
  have hlogne : (Real.log x) ^ (m + 1) ≠ 0 := (pow_pos hlog (m + 1)).ne'
  have hL : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hpow : HasDerivAt (fun y => (Real.log y) ^ (m + 1))
      (((m : ℝ) + 1) * (Real.log x) ^ m * x⁻¹) x := by
    have h := hL.fun_pow (m + 1)
    simpa using h
  have hdiv : HasDerivAt (fun y => y / (Real.log y) ^ (m + 1))
      ((1 * (Real.log x) ^ (m + 1) - x * (((m : ℝ) + 1) * (Real.log x) ^ m * x⁻¹)) /
        ((Real.log x) ^ (m + 1)) ^ 2) x := (hasDerivAt_id x).div hpow hlogne
  have hfun : phi D (m + 1) = fun y => id y - D * (y / (Real.log y) ^ (m + 1)) := by
    funext y; simp [phi, mul_div_assoc]
  have h := (hasDerivAt_id x).sub (hdiv.const_mul D)
  have key : (1 : ℝ) - D * ((1 * (Real.log x) ^ (m + 1) -
        x * (((m : ℝ) + 1) * (Real.log x) ^ m * x⁻¹)) / ((Real.log x) ^ (m + 1)) ^ 2)
      = 1 - D * ((Real.log x - ((m : ℝ) + 1)) / (Real.log x) ^ (m + 2)) := by
    field_simp
    ring
  rw [hfun, ← key]
  exact h

/-- The tangent-line inequality behind (3.28)'s threshold `(k+1)^{k+1}`:
`t^{k+1} ≥ (k+1)^{k+1}(t − k)` for `t ≥ 0`, with equality at `t = k+1`.  This is exactly
why the paper's `φ'` has its minimum `1 − c/(k+1)^{k+1}` at `x = e^{k+1}` (lines 799-803).
Proved by the paper's own range `k = 1,…,5` (line 775). -/
theorem tangent_bound {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) {t : ℝ} (ht : 0 ≤ t) :
    ((k : ℝ) + 1) ^ (k + 1) * (t - (k : ℝ)) ≤ t ^ (k + 1) := by
  interval_cases k
  · push_cast; nlinarith [sq_nonneg (t - 2)]
  · push_cast
    nlinarith [mul_nonneg (sq_nonneg (t - 3)) (by linarith : (0:ℝ) ≤ t + 6)]
  · push_cast
    nlinarith [mul_nonneg (sq_nonneg (t - 4))
      (by nlinarith [sq_nonneg t] : (0:ℝ) ≤ t ^ 2 + 8 * t + 48)]
  · push_cast
    nlinarith [mul_nonneg (sq_nonneg (t - 5))
      (by nlinarith [pow_nonneg ht 3, sq_nonneg t] :
        (0:ℝ) ≤ t ^ 3 + 10 * t ^ 2 + 75 * t + 500)]
  · push_cast
    nlinarith [mul_nonneg (sq_nonneg (t - 6))
      (by nlinarith [pow_nonneg ht 4, pow_nonneg ht 3, sq_nonneg t] :
        (0:ℝ) ≤ t ^ 4 + 12 * t ^ 3 + 108 * t ^ 2 + 864 * t + 6480)]

/-- Paper lines 795-803: `φ(x) = x(1 − D/(log x)^k)` is (strictly) increasing on
`[e^{k+1}, ∞)` whenever `D < (k+1)^{k+1}` — condition (3.28). -/
theorem phi_strictMonoOn {D : ℝ} {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5)
    (hDsmall : D < ((k : ℝ) + 1) ^ (k + 1)) :
    StrictMonoOn (phi D k) (Set.Ici (Real.exp ((k : ℝ) + 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hk1R : (1 : ℝ) ≤ ((m : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- every point of the domain exceeds `e^{k+1} > e^2 > 1`
  have hgt : ∀ y ∈ Set.Ici (Real.exp (((m + 1 : ℕ) : ℝ) + 1)), (1 : ℝ) < y := by
    intro y hy
    have h1 : (1 : ℝ) < Real.exp (((m + 1 : ℕ) : ℝ) + 1) := by
      rw [Real.one_lt_exp_iff]; push_cast; linarith
    exact lt_of_lt_of_le h1 hy
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
  · intro y hy
    exact ((hasDerivAt_phi D m (hgt y hy)).differentiableAt.continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy' : Real.exp (((m + 1 : ℕ) : ℝ) + 1) < y := hy
    have hy1 : (1 : ℝ) < y := hgt y (le_of_lt hy')
    have hlog : ((m : ℝ) + 2) < Real.log y := by
      have := Real.log_lt_log (Real.exp_pos _) hy'
      rw [Real.log_exp] at this
      push_cast at this
      linarith
    rw [(hasDerivAt_phi D m hy1).deriv]
    have ht0 : (0 : ℝ) ≤ Real.log y := by linarith
    have htpow : (0 : ℝ) < (Real.log y) ^ (m + 2) := pow_pos (by linarith) _
    have hstep : D * (Real.log y - ((m : ℝ) + 1)) < (Real.log y) ^ (m + 2) := by
      have hpos : (0 : ℝ) < Real.log y - ((m : ℝ) + 1) := by linarith
      have hDcast : D < (((m : ℝ) + 1) + 1) ^ (m + 2) := by
        have he : ((((m + 1 : ℕ)) : ℝ) + 1) ^ (m + 1 + 1) = (((m : ℝ) + 1) + 1) ^ (m + 2) := by
          norm_num
        linarith [he ▸ hDsmall]
      have h2 := tangent_bound (k := m + 1) (by omega) hk5 ht0
      have hcast2 : ((((m + 1 : ℕ)) : ℝ) + 1) ^ (m + 1 + 1) * (Real.log y - ((m + 1 : ℕ) : ℝ))
          = (((m : ℝ) + 1) + 1) ^ (m + 2) * (Real.log y - ((m : ℝ) + 1)) := by
        push_cast; norm_num
      have h3 : (Real.log y) ^ (m + 1 + 1) = (Real.log y) ^ (m + 2) := by norm_num
      rw [hcast2, h3] at h2
      nlinarith [h2, hpos, hDcast]
    have hfin : D * ((Real.log y - ((m : ℝ) + 1)) / (Real.log y) ^ (m + 2)) < 1 := by
      rw [← mul_div_assoc, div_lt_one htpow]
      exact hstep
    linarith

/-! ## 3.  Lemma 10 -/

/-- **BKLNW Lemma 10** (`bklnw_paper.txt` lines 775-784, (3.27)-(3.29)).

`hD` is `D_k(a,b) ≤ D` written pointwise (see the module docstring and
`Dterm_eq_of_consecutive`); `hDsmall` is (3.28); the conclusion is (3.29).

`_hab` is the paper's `a < b`.  The proof does not use it -- the argument is pointwise on
`x ∈ [a,b]`, and that set is empty when `b < a` -- so the formal statement is very slightly
stronger than the printed one.  It is kept, unused, so the hypotheses match the paper
one-for-one. -/
theorem bklnw_lemma_10 {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) {a b D : ℝ}
    (ha : Real.exp ((k : ℝ) + 1) < a) (_hab : a < b)
    (hD : ∀ y ∈ Set.Icc a b, Dterm k y ≤ D)
    (hDsmall : D < ((k : ℝ) + 1) ^ (k + 1)) :
    ∀ x ∈ Set.Icc a b, x - D * x / (Real.log x) ^ k ≤ θ x := by
  intro x hx
  set p : ℕ := nextPrime x with hp
  have hpprime : p.Prime := nextPrime_prime x
  have hxp : x < (p : ℝ) := lt_nextPrime x
  have hlogp : (0 : ℝ) < Real.log (p : ℝ) := log_nextPrime_pos x
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℕ) ≤ p := hpprime.two_le
    exact_mod_cast lt_of_lt_of_le (by norm_num) this
  have hlogpk : (0 : ℝ) < (Real.log (p : ℝ)) ^ k := pow_pos hlogp k
  -- `c` is the paper's `D_k(n)` at this `x`
  set c : ℝ := Dterm k x with hc
  have hcD : c ≤ D := hD x hx
  have hpne : ((p : ℕ) : ℝ) ≠ 0 := ne_of_gt hppos
  have hlogpkne : (Real.log ((p : ℕ) : ℝ)) ^ k ≠ 0 := ne_of_gt hlogpk
  -- paper line 787-789: `θ(x) = φ_c(p_n)`
  have hthetaEq : phi c k ((p : ℕ) : ℝ) = θ x := by
    unfold phi
    rw [hc]
    unfold Dterm
    rw [← hp]
    field_simp
    ring
  -- widen `c` to `D`
  have hwiden : phi D k ((p : ℕ) : ℝ) ≤ phi c k ((p : ℕ) : ℝ) := by
    unfold phi
    have hq : (0 : ℝ) ≤ ((p : ℕ) : ℝ) / (Real.log ((p : ℕ) : ℝ)) ^ k :=
      le_of_lt (div_pos hppos hlogpk)
    have hle : c * ((p : ℕ) : ℝ) / (Real.log ((p : ℕ) : ℝ)) ^ k
        ≤ D * ((p : ℕ) : ℝ) / (Real.log ((p : ℕ) : ℝ)) ^ k := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hcD hq
    linarith
  -- paper (3.31): `φ_D` is increasing, and `x < p`
  have hmem_x : x ∈ Set.Ici (Real.exp ((k : ℝ) + 1)) := le_of_lt (lt_of_lt_of_le ha hx.1)
  have hmem_p : (p : ℝ) ∈ Set.Ici (Real.exp ((k : ℝ) + 1)) :=
    le_of_lt (lt_trans (lt_of_lt_of_le ha hx.1) hxp)
  have hmono : phi D k x ≤ phi D k (p : ℝ) :=
    ((phi_strictMonoOn hk1 hk5 hDsmall) hmem_x hmem_p hxp).le
  have : phi D k x ≤ θ x := by rw [← hthetaEq]; linarith
  simpa [phi] using this

/-- (3.29) in the paper's own multiplicative shape `θ(x) ≥ x(1 − D/(log x)^k)`. -/
theorem bklnw_lemma_10' {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) {a b D : ℝ}
    (ha : Real.exp ((k : ℝ) + 1) < a) (hab : a < b)
    (hD : ∀ y ∈ Set.Icc a b, Dterm k y ≤ D)
    (hDsmall : D < ((k : ℝ) + 1) ^ (k + 1)) :
    ∀ x ∈ Set.Icc a b, x * (1 - D / (Real.log x) ^ k) ≤ θ x := by
  intro x hx
  have h1 : (1 : ℝ) < x := by
    have h2 : (1 : ℝ) < Real.exp ((k : ℝ) + 1) := by
      rw [Real.one_lt_exp_iff]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    linarith [hx.1, ha]
  rw [← phi_eq_mul D k h1]
  unfold phi
  exact bklnw_lemma_10 hk1 hk5 ha hab hD hDsmall x hx


/-! ## 4.  Faithfulness bridge: `Dterm` really is (3.27)'s `D_k(n)`

Paper lines 790-793: "Let `x ∈ [p_{n−1}, p_n)` and observe that `θ(x) = θ(p_{n−1})`".
We prove that, then read (3.27) off it. -/

/-- `θ` is constant across a prime-free stretch: `θ x = θ y` whenever `x ≤ y` and every
prime above `x` is also above `y`. -/
theorem theta_eq_of_no_prime_between {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y)
    (h : ∀ p : ℕ, p.Prime → x < (p : ℝ) → y < (p : ℝ)) : θ x = θ y := by
  unfold Chebyshev.theta
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hq0, hqle⟩, hqp⟩
    exact ⟨⟨hq0, le_trans hqle (Nat.floor_le_floor hxy)⟩, hqp⟩
  · rintro ⟨⟨hq0, hqle⟩, hqp⟩
    refine ⟨⟨hq0, ?_⟩, hqp⟩
    by_contra hcon
    push Not at hcon
    have hxq : x < (q : ℝ) := by
      have hstep : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hcon
      linarith [Nat.lt_floor_add_one x]
    have hyq := h q hqp hxq
    have hqy : (q : ℝ) ≤ y :=
      le_trans (by exact_mod_cast hqle) (Nat.floor_le (le_trans hx0 hxy))
    linarith

/-- The primes `≤ x`, as a `Finset`. -/
noncomputable def primesUpto (x : ℝ) : Finset ℕ := (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

/-- The largest prime `≤ x` (the paper's `p_{n−1}` for `x ∈ [p_{n−1}, p_n)`). -/
noncomputable def prevPrime (x : ℝ) : ℕ := (primesUpto x).sup id

theorem primesUpto_nonempty {x : ℝ} (hx : 2 ≤ x) : (primesUpto x).Nonempty := by
  refine ⟨2, ?_⟩
  simp only [primesUpto, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, Nat.prime_two⟩
  have h2 : (2 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  omega

theorem prevPrime_mem {x : ℝ} (hx : 2 ≤ x) : prevPrime x ∈ primesUpto x := by
  obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup (primesUpto x) (primesUpto_nonempty hx) id
  have : prevPrime x = c := hce
  rw [this]; exact hc

theorem prevPrime_prime {x : ℝ} (hx : 2 ≤ x) : (prevPrime x).Prime := by
  have h := prevPrime_mem hx
  simp only [primesUpto, Finset.mem_filter] at h
  exact h.2

theorem prevPrime_le {x : ℝ} (hx : 2 ≤ x) : ((prevPrime x : ℕ) : ℝ) ≤ x := by
  have h := prevPrime_mem hx
  simp only [primesUpto, Finset.mem_filter, Finset.mem_range] at h
  have h1 : prevPrime x ≤ ⌊x⌋₊ := by omega
  calc ((prevPrime x : ℕ) : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ x := Nat.floor_le (by linarith)

theorem le_prevPrime {x : ℝ} {q : ℕ} (hq : q.Prime) (hqx : (q : ℝ) ≤ x) :
    q ≤ prevPrime x := by
  have hmem : q ∈ primesUpto x := by
    simp only [primesUpto, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have : q ≤ ⌊x⌋₊ := Nat.le_floor hqx; omega, hq⟩
  simpa [prevPrime] using Finset.le_sup (f := (id : ℕ → ℕ)) hmem

/-- `prevPrime x` and `nextPrime x` are **consecutive** primes: nothing prime lies
strictly between them.  Together with `prevPrime_le`/`lt_nextPrime` this says
`x ∈ [p_{n−1}, p_n)` with `p_{n−1} = prevPrime x`, `p_n = nextPrime x`. -/
theorem nextPrime_le_of_prevPrime_lt {x : ℝ} (_hx : 2 ≤ x) {r : ℕ} (hr : r.Prime)
    (hlt : prevPrime x < r) : nextPrime x ≤ r := by
  refine nextPrime_le hr ?_
  by_contra hcon
  push Not at hcon
  exact absurd (le_prevPrime hr hcon) (by omega)

theorem prevPrime_lt_nextPrime {x : ℝ} (hx : 2 ≤ x) : prevPrime x < nextPrime x := by
  have h1 : ((prevPrime x : ℕ) : ℝ) ≤ x := prevPrime_le hx
  have h2 : x < ((nextPrime x : ℕ) : ℝ) := lt_nextPrime x
  exact_mod_cast lt_of_le_of_lt h1 h2

/-- Paper lines 790-793: `θ(x) = θ(p_{n−1})`. -/
theorem theta_eq_theta_prevPrime {x : ℝ} (hx : 2 ≤ x) : θ ((prevPrime x : ℕ) : ℝ) = θ x := by
  refine theta_eq_of_no_prime_between (by positivity) (prevPrime_le hx) ?_
  intro r hr hlt
  have hlt' : prevPrime x < r := by exact_mod_cast hlt
  have := nextPrime_le_of_prevPrime_lt hx hr hlt'
  have hcast : ((nextPrime x : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
  linarith [lt_nextPrime x]

/-- **`Dterm` is literally (3.27)'s `D_k(n)`.**  For `x ∈ [p_{n−1}, p_n)`,
`Dterm k x = (log p_n)^k (p_n − θ(p_{n−1}))/p_n`. -/
theorem Dterm_eq_paper (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    Dterm k x = (Real.log ((nextPrime x : ℕ) : ℝ)) ^ k *
      (((nextPrime x : ℕ) : ℝ) - θ ((prevPrime x : ℕ) : ℝ)) / ((nextPrime x : ℕ) : ℝ) := by
  rw [Dterm, theta_eq_theta_prevPrime hx]

/-- **Lemma 10, with (3.27) written exactly as in the paper**: the hypothesis quantifies
over consecutive prime pairs `(p_{n−1}, p_n) = (q, p)` in the index range `n0 ≤ n ≤ n1`
(`a < p_n` excludes `n < n0`, `p_{n−1} ≤ b` excludes `n > n1`), and asks for
`(log p_n)^k (p_n − θ(p_{n−1}))/p_n ≤ D`, i.e. `D_k(a,b) ≤ D`. -/
theorem bklnw_lemma_10_paper_form {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) {a b D : ℝ}
    (ha : Real.exp ((k : ℝ) + 1) < a) (hab : a < b)
    (hD : ∀ q p : ℕ, q.Prime → p.Prime → q < p →
        (∀ r : ℕ, r.Prime → q < r → p ≤ r) →
        a < (p : ℝ) → (q : ℝ) ≤ b →
        (Real.log (p : ℝ)) ^ k * ((p : ℝ) - θ (q : ℝ)) / (p : ℝ) ≤ D)
    (hDsmall : D < ((k : ℝ) + 1) ^ (k + 1)) :
    ∀ x ∈ Set.Icc a b, x - D * x / (Real.log x) ^ k ≤ θ x := by
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hexp2 : (2 : ℝ) < Real.exp ((k : ℝ) + 1) := by
    have h3 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    have : Real.exp 2 ≤ Real.exp ((k : ℝ) + 1) := Real.exp_le_exp.mpr (by linarith)
    linarith
  refine bklnw_lemma_10 hk1 hk5 ha hab ?_ hDsmall
  intro y hy
  have hy2 : (2 : ℝ) ≤ y := le_of_lt (lt_of_lt_of_le hexp2 (le_trans ha.le hy.1))
  rw [Dterm_eq_paper k hy2]
  refine hD (prevPrime y) (nextPrime y) (prevPrime_prime hy2) (nextPrime_prime y)
    (prevPrime_lt_nextPrime hy2) (fun r hr hlt => nextPrime_le_of_prevPrime_lt hy2 hr hlt)
    ?_ ?_
  · exact lt_of_le_of_lt hy.1 (lt_nextPrime y)
  · exact le_trans (prevPrime_le hy2) hy.2

end BKLNW.Lemma10
