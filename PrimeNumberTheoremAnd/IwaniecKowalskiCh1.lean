import Architect
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

open scoped ArithmeticFunction.Moebius

open scoped LSeries.notation

namespace ArithmeticFunction

blueprint_comment /--
\section{Blueprint for Iwaniec-Kowalski Chapter 1}
-/

blueprint_comment /--
Here we collect facts from Chapter 1 that are not already in Mathlib.
We will try to upstream as much as possible.
-/

/-- `τ` (tau) is the divisor count function, equal to `σ 0`. -/
abbrev tau : ArithmeticFunction ℕ := σ 0

@[inherit_doc tau]
scoped notation "τ" => tau

variable {R : Type*}

/--
An arithmetic function `IsAdditive` if it satisfies the property that for any two coprime natural numbers `m` and `n`, the function evaluated at their product equals the sum of the function evaluated at each number individually.
-/
@[blueprint
  "IsAdditive"
  (title := "IsAdditive")
  (statement := /-- Additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for coprime $m$, $n$. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Coprime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (title := "IsCompletelyAdditive")
  (statement := /-- Completely additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for all $m, n \ne 0$. -/)]
def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive.isAdditive"
  (title := "IsCompletelyAdditive.isAdditive")
  (statement := /-- A completely additive function is additive. -/)]
lemma IsCompletelyAdditive.isAdditive [AddZeroClass R] {f : ArithmeticFunction R}
    (hf : IsCompletelyAdditive f) : IsAdditive f :=
  fun hm hn _ ↦ hf hm hn

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

@[blueprint
  "unique_divisor_decomposition"
  (title := "unique divisor decomposition")
  (statement := /-- If $a$ and $b$ are coprime, then any divisor $d$ of $ab$ can be uniquely expressed as a product of a divisor of $a$ and a divisor of $b$.
    \begin{verbatim}
  This has been upstreamed #36495.
  \end{verbatim}
-/)
  (proof := /--
  Let $a$ and $b$ be coprime natural numbers, and let $d$ be a divisor of $ab$. Since $a$ and $b$ are coprime, we can use the fact that the divisors of $ab$ correspond to pairs of divisors of $a$ and $b$. Specifically, we can express $d$ as $d = d_a \cdot d_b$, where $d_a$ divides $a$ and $d_b$ divides $b$. The uniqueness of this decomposition follows from the coprimality of $a$ and $b$, which ensures that the divisors of $a$ and $b$ do not share any common factors. Therefore, there is a one-to-one correspondence between the divisors of $ab$ and the pairs of divisors of $a$ and $b$, which guarantees the uniqueness of the decomposition.
  -/)]
lemma unique_divisor_decomposition {a b d : ℕ} (hab : Coprime a b) (hd : d ∣ a * b) :
    ∃! p : ℕ × ℕ, p.1 ∣ a ∧ p.2 ∣ b ∧ p.1 * p.2 = d := by
  sorry -- UPSTREAMED TO MATHLIB #36495

/-- If `f` is a multiplicative arithmetic function, then for coprime `a` and `b`, we have $\sum_{d | ab} f(d) = (\sum_{d | a} f(d)) \cdot (\sum_{d | b} f(d))$. -/
@[blueprint
  "sum_divisors_mul_of_coprime"
  (title := "sum divisors mul of coprime")
  (statement := /-- If $f$ is a multiplicative arithmetic function, then for coprime, nonzero $a$ and $b$, we have that
  $\sum_{d | ab} f(d) = (\sum_{d | a} f(d)) \cdot (\sum_{d | b} f(d))$.
  \begin{verbatim}
  This has been upstreamed #36495.
  \end{verbatim}
  -/)
  (proof := /--
  Since $f$ is multiplicative, we can express the sum over divisors of $ab$ in terms of the sums over divisors of $a$ and $b$. The key idea is to use the fact that the divisors of $ab$ can be expressed as products of divisors of $a$ and divisors of $b$, due to the coprimality condition. Specifically, each divisor $d$ of $ab$ can be uniquely written as $d = d_a * d_b$, where $d_a$ divides $a$ and $d_b$ divides $b$. Therefore, we can rewrite the sum as a double sum over the divisors of $a$ and $b$, which factorizes into the product of the two separate sums.
  -/)]
theorem sum_divisors_mul_of_coprime {R : Type*} [CommRing R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {a b : ℕ} (hab : Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ d ∈ (a * b).divisors, f d = (∑ d ∈ a.divisors, f d) * (∑ d ∈ b.divisors, f d) := by
  sorry -- UPSTREAMED TO MATHLIB #36495

/-- If `g` is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p | n} (1 - g(p))$. -/
@[blueprint
  "sum_moebius_pmul_eq_prod_one_sub"
  (title := "sum moebius pmul eq prod one sub")
  (statement := /-- If $g$ is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p | n} (1 - g(p))$.
      \begin{verbatim}
  Upstream issue has been created #1240.
  \end{verbatim}

    -/)
  (proof := /--
  Multiply out and collect terms.
  -/)]
theorem sum_moebius_pmul_eq_prod_one_sub {R : Type*} [CommRing R]
    {g : ArithmeticFunction R} (hg : g.IsMultiplicative) (n : ℕ) : n ≠ 0 →
    ∑ d ∈ n.divisors, (moebius d : R) * g d = ∏ p ∈ n.primeFactors, (1 - g p) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one => exact fun _ ↦ by simp [hg.map_one]
  | prime_pow p k hp hk =>
    refine fun _ ↦ ?_
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, sum_divisors_prime_pow hp,
      Finset.sum_range_succ']
    simp only [pow_zero, moebius_apply_one, Int.cast_one, hg.map_one, mul_one]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hk)]
    · simp only [zero_add, pow_one, moebius_apply_prime hp, Int.reduceNeg, Int.cast_neg,
        Int.cast_one, neg_mul, one_mul]; ring
    · intro i _ hi
      have hnsq : ¬Squarefree (p ^ (i + 1)) := by
        rw [Nat.squarefree_pow_iff hp.ne_one (by omega : i + 1 ≠ 0)]
        omega
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simp
  | coprime a b ha hb hab iha ihb =>
    intro hn
    rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors,
        ← iha (by omega), ← ihb (by omega)]
    let h : ArithmeticFunction R := ⟨fun n ↦ ↑(moebius n) * g n, by simp⟩
    have h_mul : h.IsMultiplicative := by
      refine ⟨?_, ?_⟩
      · simp [h, ArithmeticFunction.coe_mk, hg.left]
      · intro m n hmn
        simp only [h, ArithmeticFunction.coe_mk]
        rw [ArithmeticFunction.isMultiplicative_moebius.right hmn, hg.right hmn]
        push_cast
        ring
    exact sum_divisors_mul_of_coprime h_mul hab (by omega) (by omega)

/-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/
@[blueprint
  "zeta_mul_zeta"
  (title := "zeta mul zeta")
  (statement := /-- The Dirichlet convolution of $\zeta$ with itself is $\tau$ (the divisor count function). -/)
  (proof := /--
  By definition of $\zeta$, we have $\zeta(n) = 1$ for all $n \geq 1$. Thus, the Dirichlet convolution
  $(\zeta * \zeta)(n)$ counts the number of ways to write $n$ as a product of two positive integers,
  which is exactly the number of divisors of $n$, i.e., $\tau(n)$.
  -/)]
theorem zeta_mul_zeta : (ζ : ArithmeticFunction ℕ) * ζ = τ := by
  ext n; unfold zeta tau sigma
  simp only [mul_apply, coe_mk, mul_ite, mul_zero, mul_one, pow_zero, sum_const, smul_eq_mul]
  have key : ∀ x ∈ n.divisorsAntidiagonal, (if x.2 = 0 then 0 else if x.1 = 0 then 0 else 1) = 1 := by
    intro ⟨a, b⟩ hx
    have := Nat.mem_divisorsAntidiagonal.mp hx
    simp [mul_ne_zero_iff.mp (this.1 ▸ this.2)]
  simp_rw [Finset.sum_congr rfl key, Finset.card_eq_sum_ones, Finset.sum_const]
  simp only [smul_eq_mul, mul_one, ← Nat.map_div_right_divisors]
  exact card_map { toFun := fun d ↦ (d, n / d), inj' := fun x x_1 ↦ congr_arg Prod.fst }

/-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/
@[blueprint
  "LSeries_tau_eq_riemannZeta_sq"
  (title := "LSeries tau eq riemannZeta sq")
  (statement := /-- The L-series of $\tau$ equals the square of the Riemann zeta function for $\Re(s) > 1$. -/)
  (proof := /--
  From the previous theorem, we have that the Dirichlet convolution of $\zeta$ with itself is $\tau$.
  Taking L-series on both sides, we get $L(\tau, s) = L(\zeta, s) \cdot L(\zeta, s)$.
  Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, we conclude that
  $L(\tau, s) = \zeta(s)^2$ for $\Re(s) > 1$.
  -/)]
theorem LSeries_tau_eq_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗τ) s = riemannZeta s ^ 2 := by
  have h1 : LSeries (↗(ζ * ζ)) s = LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s := by
    congr 1; ext n; simp only [← natCoe_mul, natCoe_apply]
  have h2 : LSeries (↗((ζ : ArithmeticFunction ℂ) * ζ)) s = LSeries (↗ζ) s * LSeries (↗ζ) s :=
    LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs) (LSeriesSummable_zeta_iff.mpr hs)
  rw [← zeta_mul_zeta, h1, h2, LSeries_zeta_eq_riemannZeta hs, pow_two]

/-- `d k` is the k-fold divisor function: the number of ways to write n as an ordered
    product of k natural numbers. Equivalently, the Dirichlet convolution of ζ with
    itself k times. We have `d 0 = 1` (identity), `d 1 = ζ`, `d 2 = σ 0`. -/
@[blueprint
  "d"
  (title := "d")
  (statement := /-- $d_k$ is the $k$-fold divisor function: the number of ways to write $n$ as an ordered
    product of $k$ natural numbers. Equivalently, the Dirichlet convolution of $\zeta$ with
    itself $k$ times.-/)]
def d (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

/-- `d 0` is the multiplicative identity (indicator at 1). -/
@[blueprint
  "d_zero"
  (title := "d zero")
  (statement := /-- $d_0$ is the multiplicative identity (indicator at 1). -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 0$, this corresponds to the empty convolution, which is defined to be the multiplicative identity in the algebra of arithmetic functions. The multiplicative identity is the function that takes the value $1$ at $n=1$ and $0$ elsewhere, which can be expressed as $\zeta^0$.
  -/)]
theorem d_zero : d 0 = 1 := pow_zero zeta

/-- `d 1` is `ζ`. -/
@[blueprint
  "d_one"
  (title := "d one")
  (statement := /-- $d_1$ is $\zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 1$, this means we are taking the convolution of $\zeta$ with itself once, which simply gives us $\zeta$. Therefore, $d_1 = \zeta^1 = \zeta$.
  -/)]
theorem d_one : d 1 = zeta := pow_one zeta

/-- `d 2` is the classical divisor count function `τ`. -/
@[blueprint
  "d_two"
  (title := "d two")
  (statement := /-- $d_2$ is the classical divisor count function $\tau$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 2$, this means we are taking the convolution of $\zeta$ with itself twice, which gives us $\zeta * \zeta$. From the earlier theorem, we know that $\zeta * \zeta = \tau$, where $\tau$ is the divisor count function. Therefore, $d_2 = \zeta^2 = \tau$.
  -/)]
theorem d_two : d 2 = τ := by simp [d, sq, zeta_mul_zeta]

/-- Recurrence: `d_(k+1) = d_k * ζ`. -/
@[blueprint
  "d_succ"
  (title := "d succ")
  (statement := /-- Recurrence: $d_{k+1} = d_k * \zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. Therefore, $d_{k + 1}$ is the $(k + 1)$-fold convolution of $\zeta$, which can be expressed as the convolution of $d_k$ (the $k$-fold convolution) with $\zeta$. Thus, we have $d_{k + 1} = d_k * \zeta$.
  -/)]
theorem d_succ (k : ℕ) : d (k + 1) = d k * zeta := pow_succ zeta k

/-- The L-series for `d k` is summable -/
@[blueprint
  "LSeries_d_summable"
  (title := "LSeries d summable")
  (statement := /-- The L-series for $d_k$ is summable for $\Re(s) > 1$. -/)
  (proof := /--
  Since $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$, and we know that the L-series of $\zeta$ converges for $\Re(s) > 1$, it follows that the L-series of $d_k$ also converges for $\Re(s) > 1$. This is because the convolution of functions with convergent L-series will also have a convergent L-series in the same region. Therefore, we can conclude that $L(d_k, s)$ is summable for $\Re(s) > 1$.
  -/)]
theorem LSeries_d_summable (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
      LSeriesSummable (↗(d k : ArithmeticFunction ℂ)) s := by
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, one_eq_delta]
    exact (hasSum_single 1 fun n hn => by simp [LSeries.term_delta, hn]).summable
  | succ k ih =>
    rw [(LSeriesSummable_congr s (fun {n} _ => show (d (k + 1) : ArithmeticFunction ℂ) n =
      ((d k : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]))]
    exact LSeriesSummable_mul ih (LSeriesSummable_zeta_iff.mpr hs)

/-- The L-series of `d k` equals `ζ(s)^k` for `Re(s) > 1`. -/
@[blueprint
  "LSeries_d_eq_riemannZeta_pow"
  (title := "LSeries d eq riemannZeta pow")
  (statement := /-- The $L$-series of $d_k$ equals $\zeta(s)^k$ for $\Re(s) > 1$. -/)
  (proof := /--
  From the definition of $d_k$ as the $k$-fold Dirichlet convolution of $\zeta$, we can express $d_k$ as $\zeta^k$. The L-series of a Dirichlet convolution corresponds to the product of the L-series of the individual functions. Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, it follows that $L(d_k, s) = L(\zeta^k, s) = (L(\zeta, s))^k = \zeta(s)^k$ for $\Re(s) > 1$ where the series converges.
  -/)]
theorem LSeries_d_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(d k)) s = riemannZeta s ^ k := by
  change LSeries (↗(d k : ArithmeticFunction ℂ)) s = riemannZeta s ^ k
  induction k with
  | zero =>
    simp only [d_zero, natCoe_one, pow_zero, one_eq_delta]
    exact congr_fun LSeries_delta s
  | succ j ih =>
    have hζ : LSeriesSummable (↗(ζ : ArithmeticFunction ℂ)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    rw [pow_succ, LSeries_congr (fun {n} _ => show (d (j + 1) : ArithmeticFunction ℂ) n =
        ((d j : ArithmeticFunction ℂ) * ζ) n by rw [d_succ, natCoe_mul]) s,
        LSeries_mul' (LSeries_d_summable j hs) hζ, ih]
    congr 1
    exact LSeries_zeta_eq_riemannZeta hs


/-- `d k` is multiplicative for all `k`. -/
@[blueprint
  "d_isMultiplicative"
  (title := "d isMultiplicative")
  (statement := /-- $d_k$ is multiplicative for all $k$. -/)
  (proof := /--
  The function $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$. Since $\zeta$ is a multiplicative function, and the Dirichlet convolution of multiplicative functions is also multiplicative, it follows that $d_k$ is multiplicative for all $k$. This can be shown by induction on $k$, using the fact that the convolution of a multiplicative function with another multiplicative function remains multiplicative.
  -/)]
theorem d_isMultiplicative (k : ℕ) : (d k).IsMultiplicative := by
  induction k with
  | zero => rw [d_zero]; exact isMultiplicative_one
  | succ k ih =>
      rw [d_succ]
      exact ih.mul isMultiplicative_zeta

/- MOVE HELPER LEMMA ESLEWHERE?? Not used in this file, but seems potentially useful? -/
theorem Nat.sum_divisorsAntidiagonal_prime_pow {α : Type u_1} [AddCommMonoid α] [HMul α α α] {k p : ℕ} {f : ℕ × ℕ → α} (h : Nat.Prime p) :
∑ x ∈ (p ^ k).divisorsAntidiagonal, f x = ∑ n ∈ Finset.range (k + 1), f (p ^ n, p ^ (k - n)) := by
  sorry

/-- Explicit formula: `d k (p^a) = (a + k - 1).choose (k - 1) for prime p` for `k ≥ 1`. -/
@[blueprint
  "d_apply_prime_pow"
  (title := "d apply prime pow")
  (statement := /-- Explicit formula: $d_k (p^a) = (a + k - 1).choose (k - 1)$ for prime $p$ and $k \geq 1$. -/)
  (proof := /--
  The function $d_k$ counts the number of ways to write a natural number as an ordered product of $k$ natural numbers. For a prime power $p^a$, the number of ways to factor it into $k$ factors corresponds to the number of non-negative integer solutions to the equation $x_1 + x_2 + ... + x_k = a$, where each $x_i$ represents the exponent of $p$ in the factorization of the corresponding factor. This is a classic combinatorial problem, and the number of solutions is given by the formula $(a + k - 1).choose (k - 1)$, which counts the ways to distribute $a$ indistinguishable items (the prime factors) into $k$ distinguishable boxes (the factors).
  -/)]
theorem d_apply_prime_pow {k : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    d k (p ^ a) = (a + k - 1).choose (k - 1) := by
  obtain ⟨k', rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction k' generalizing a with
  | zero => simp [d_one, hp.ne_zero]
  | succ k' ih =>
      rw [d_succ, mul_zeta_apply, sum_divisors_prime_pow hp]
      simp_rw [fun i ↦ ih i (succ_pos _)]
      simpa [add_assoc, add_left_comm, add_comm] using sum_range_add_choose a k'

/-- (1.25) in Iwaniec-Kowalski: a formula for `d_k` for all `n`. -/
@[blueprint
  "d_apply"
  (title := "d apply")
  (statement := /-- (1.25) in Iwaniec-Kowalski: a formula for $d_k$ for all $n$. -/)
  (proof := /--
  The function $d_k$ is multiplicative, so to compute $d_k(n)$ for a general natural number $n$, we can factor $n$ into its prime power decomposition: $n = p_1^{a_1} p_2^{a_2} ... p_m^{a_m}$. Since $d_k$ is multiplicative, we have:

  \[
  d_k(n) = d_k(p_1^{a_1}) \cdot d_k(p_2^{a_2}) \cdot ... \cdot d_k(p_m^{a_m})
  \]

  Using the explicit formula for prime powers from the previous theorem, we can substitute to get:

  \[
  d_k(n) = \prod_{i=1}^{m} (a_i + k - 1).choose (k - 1)
  \]

  This gives us a complete formula for $d_k(n)$ in terms of the prime factorization of $n$.
  -/)]
lemma d_apply {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    d k n = ∏ p ∈ n.primeFactors, (n.factorization p + k - 1).choose (k - 1) := by
  have hmult : (d k).IsMultiplicative := d_isMultiplicative k
  rw [hmult.multiplicative_factorization (d k) hn, prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl (fun p hp => ?_)
  simpa using d_apply_prime_pow hk (prime_of_mem_primeFactors hp) _

/-- Divisor power sum with exponents in an arbitrary semiring `R`. -/
@[blueprint
  "sigmaR"
  (title := "sigmaR")
  (statement := /-- Divisor power sum with complex exponent. -/)]
noncomputable def sigmaR {R : Type*} [Semiring R] [HPow R R R] (s : R) : ArithmeticFunction R where
  toFun := fun n ↦ ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

@[inherit_doc]
scoped[ArithmeticFunction] notation "σᴿ" => ArithmeticFunction.sigmaR

/-- For natural exponents, sigmaR agrees with sigma. -/
@[blueprint
  "sigmaR_natCast"
  (title := "sigmaR-natCast")
  (statement := /-- For natural exponents, $\sigma^R$ agrees with $\sigma$. -/)
  (proof := /--
  The function $\sigma^R$ is defined as the sum of the $s$-th powers of the divisors of $n$. When
  $s$ is a natural number $k$, this definition coincides with the classical divisor power sum
  function $\sigma_k(n)$, which also sums the $k$-th powers of the divisors of $n$. Therefore, for
  natural exponents, we have $\sigma^R_k(n) = \sigma_k(n)$ when we view $\sigma_k(n)$ as a complex
  number. This can be shown by directly comparing the definitions and noting that both functions sum
  over the same set of divisors with the same exponentiation.
  -/)]
lemma sigmaR_natCast (k n : ℕ) :
    σᴿ k n = σ k n := by
  unfold sigmaR sigma
  simp only [cast_id, coe_mk]

@[blueprint
  "sigmaR_apply"
  (title := "sigmaR-apply")
  (statement := /--
    We have that $\sigma^R_s(n)=\sum_{d\mid n}d^s.$
  -/)
  (proof := /--
    This follows immediately from the definition.
  -/)]
lemma sigmaR_apply {n : ℕ} {s : ℂ} : σᴿ s n = ∑ d ∈ divisors n, (d : ℂ) ^ s := by
  rfl

@[blueprint
  "sigmaR_natCast'"
  (title := "sigmaR-natCast'")
  (statement := /--
    A casting lemma for $\sigma^R$.
  -/)]
lemma sigmaR_natCast' (k n : ℕ) :
    σᴿ (k : ℂ) n = σᴿ k n := by
  simp only [sigmaR_apply, Complex.cpow_natCast, sigmaR_natCast, sigma_apply, cast_sum, cast_pow]

@[blueprint
  "sigmaR_apply_prime_pow"
  (title := "sigmaR-apply-prime-pow")
  (statement := /--
    For a prime power, we have that $\sigma^R_s(p^i)=\sum_{j=0}^ip^{js}$.
  -/)
  (proof := /--
    Note that $d\mid p^i$ implies that $d=p^j$ with $0\leq j\leq i$. Thus,
    $$\sigma^R_s(p^i)=\sum_{d\mid p^i}d^s=\sum_{j=0}^i(p^j)^s=\sum_{j=0}^ip^{js}.$$
  -/)]
lemma sigmaR_apply_prime_pow {p i : ℕ} {s : ℂ} (hp : p.Prime) :
    σᴿ s (p ^ i) = ∑ j ∈ .range (i + 1), (p : ℂ) ^ (j * s) := by
  simp only [sigmaR_apply, divisors_prime_pow hp, sum_map, Function.Embedding.coeFn_mk, cast_pow]
  congr 1
  funext x
  exact Eq.symm (Complex.natCast_cpow_natCast_mul p x s)

@[blueprint
  "sigmaR_one_apply"
  (title := "sigmaR-one-apply")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_one_apply (n : ℕ) : σᴿ (1 : ℂ) n = ∑ d ∈ divisors n, d := by
  simp only [sigmaR_apply, Complex.cpow_one, cast_sum]

@[blueprint
  "sigmaR_one_apply_prime_pow"
  (title := "sigmaR-one-apply-prime-pow")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (1 : ℂ) (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp only [sigmaR_apply_prime_pow hp, mul_one, Complex.cpow_natCast, cast_sum, cast_pow]

@[blueprint
  "sigmaR_eq_sum_div"
  (title := "sigmaR-eq-sum-div")
  (statement := /--
    We have that $\sigma^R_s(n)=\sum_{d\mid n}(n/d)^s$.
  -/)
  (proof := /--
    Note that $d \mapsto n/d$ forms a one-to-one mapping between the divisors of $n$. Using this in
    combination with the definiton we have that
    $$\sigma^R_s(n)=\sum_{d\mid n}d^s=\sum_{d\mid n}(n/d)^s.$$
  -/)]
lemma sigmaR_eq_sum_div {n : ℕ} {s : ℂ} :
    σᴿ s n = ∑ d ∈ divisors n, ((n / d) : ℂ) ^ s := by
  rw[sigmaR_apply, ← sum_div_divisors]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw[Nat.cast_div (dvd_of_mem_divisors hd) (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]

@[blueprint
  "sigmaR_zero_apply"
  (title := "sigmaR-zero-apply")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_zero_apply (n : ℕ) :
    σᴿ (0 : ℂ) n = #n.divisors := by
  simp only [sigmaR_apply, Complex.cpow_zero, sum_const, nsmul_eq_mul, mul_one]

@[blueprint
  "sigmaR_zero_apply_prime_pow"
  (title := "sigmaR-zero-apply-prime-pow")
  (statement := /--
    Same as the previous lemma, but with a different casting structure.
  -/)]
lemma sigmaR_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σᴿ (0 : ℂ) (p ^ i) = i + 1 := by
  simp only [sigmaR_apply_prime_pow hp, mul_zero, Complex.cpow_zero, sum_const, card_range,
    nsmul_eq_mul, cast_add, cast_one, mul_one]

@[blueprint
  "sigmaR_one"
  (title := "sigmaR-one")
  (statement := /--
    We have that $\sigma^R_s(1)=1$.
  -/)
  (proof := /--
    By definition we have that
    $$\sigma^R_s(1)=\sum_{d \mid 1}d^s=1^s=1.$$
  -/)]
lemma sigmaR_one (s : ℂ) :
    σᴿ s 1 = 1 := by
  simp only [sigmaR_apply, divisors_one, sum_singleton, cast_one, Complex.one_cpow]

@[blueprint
  "powR"
  (title := "powR")
  (statement := /-- Arithmetic function with complex parameter $\nu$. Evaluates as $n\mapsto n^{\nu}$ for $n\neq 0$ and $0$ at $n=0$. -/)]
noncomputable def powR (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by grind⟩

@[blueprint
  "isMultiplicative_powR"
  (title := "isMultiplicative-powR")
  (statement := /--
    For fixed $\nu$ the function $n\mapsto n^\nu$ is multiplicative.
  -/)
  (proof := /--
    This immediately follows from the fact that exponentiation with a fixed power is a homomorphism.
  -/)]
theorem isMultiplicative_powR {ν : ℂ} : IsMultiplicative (powR ν) := by
  refine ⟨by simp [powR], fun {m n : ℕ} mCn => ?_⟩
  simp only [powR, ArithmeticFunction.coe_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, ↓reduceIte, mul_ite, mul_zero, ite_self]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, ↓reduceIte]
  have hmn_pos : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
  simp only [hm.ne', hn.ne', hmn_pos, if_false]
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n ν

@[blueprint
  "sigmaR_eq_zeta_mul_powR"
  (title := "sigmaR-eq-zeta-mul-powR")
  (statement := /-- $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$, where $\zeta$ is the constant function $1$. -/)
  (proof := /--
  The function $\sigma^R(\nu)$ is defined as the sum of the $\nu$-th powers of the divisors of $n$. The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The Dirichlet convolution of $\zeta$ (the constant function $1$) and $\text{pow}^R(\nu)$ is exactly $\sigma^R(\nu)$, since for each divisor $d$ of $n$, we have $(\zeta * \text{pow}^R(\nu))(n) = \sum_{d|n} 1 \cdot d^\nu = \sigma^R(\nu)(n)$. Thus, we have $\sigma^R(\nu) = \zeta * \text{pow}^R(\nu)$.
  -/)]
lemma sigmaR_eq_zeta_mul_powR (ν : ℂ) : sigmaR ν = (zeta : ArithmeticFunction ℂ) * powR ν := by
  ext n;
  by_cases hn : n = 0 <;> simp only [ hn, ArithmeticFunction.sigmaR, ArithmeticFunction.powR,
  ArithmeticFunction.zeta, map_zero, coe_mk, mul_apply, natCoe_apply, cast_ite, CharP.cast_eq_zero,
  cast_one, mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if x = 0 then 0 else ( y : ℂ ) ^ ν, ← Nat.sum_div_divisors ];
  exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ), if_neg ( Nat.ne_of_gt ( Nat.pos_of_mem_divisors hx ) ) ] ;

@[blueprint
  "isMultiplicative_sigmaR"
  (title := "isMultiplicative-sigmaR")
  (statement := /--
    For fixed $s$ function $n\mapsto\sigma^R_s(n)$ is multiplicative.
  -/)
  (proof := /--
    Recall from Lemma \ref{sigmaR-eq-zeta-mul-powR} that $\sigma^R$ is $\zeta$ convolved with
    Definition \ref{powR}. Since both of these are multiplicative functions, their convolution is
    also multiplicative.
  -/)]
lemma isMultiplicative_sigmaR {s : ℂ} :
    IsMultiplicative (σᴿ s) := by
  rw [sigmaR_eq_zeta_mul_powR]
  exact isMultiplicative_zeta.natCast.mul  isMultiplicative_powR

@[blueprint
  "sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul"
  (title := "sigmaR-eq-prod-primeFactors-sum-range-factorization-pow-mul")
  (statement := /--
    We have that
    $$\sigma^R_s(n)=\prod_{p\mid n}\sum_{j=0}^{v_p(n)}p^{js}.$$
  -/)
  (proof := /--
    Since $\sigma^R_s$ is multiplicative, it suffices to understand it at primes powers.
    $$\sigma^R_s(n)=\prod_{p\mid n}\sigma^R_s(p^{v_p(n)}).$$
    Applying Lemma \ref{sigmaR-apply-prime-pow}.
  -/)]
lemma sigmaR_eq_prod_primeFactors_sum_range_factorization_pow_mul {n : ℕ} {s : ℂ} (hn : n ≠ 0) :
    σᴿ s n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), (p : ℂ) ^ (i * s) := by
  rw [isMultiplicative_sigmaR.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigmaR_apply_prime_pow <| prime_of_mem_primeFactors h

@[blueprint
  "LSeries_powR_eq"
  (title := "LSeries powR eq")
  (statement := /-- $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ for $\Re(s - \nu) > 1$.
  \begin{verbatim}
  This is IK (1.27).
  \end{verbatim}
  -/)
  (proof := /--
  The function $\text{pow}^R(\nu)$ is defined as $n \mapsto n^\nu$ for $n \neq 0$ and $0$ for $n = 0$. The L-series of $\text{pow}^R(\nu)$ at $s$ is given by the sum $\sum_{n=1}^{\infty} n^{\nu - s}$. This series converges to the Riemann zeta function $\zeta(s - \nu)$ for $\Re(s - \nu) > 1$, since the zeta function is defined as $\zeta(s) = \sum_{n=1}^{\infty} n^{-s}$ for $\Re(s) > 1$. Therefore, we have $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ under the condition that $\Re(s - \nu) > 1$.
  -/)]
lemma LSeries_powR_eq (ν : ℂ) {s : ℂ} (hs : 1 < (s - ν).re) :
    LSeries (powR ν) s = riemannZeta (s - ν) := by
  convert ( LSeries_congr _ _ ) using 1;
  · rw [ zeta_eq_tsum_one_div_nat_cpow hs ];
    · refine tsum_congr fun n => ?_;
      by_cases hn : n = 0
      · simp only [LSeries.term, hn, one_div, CharP.cast_eq_zero, ↓reduceIte, inv_eq_zero, Complex.cpow_eq_zero_iff,
          ne_eq, true_and]
        exact sub_ne_zero_of_ne (by rintro rfl; norm_num at hs)
      · simp only [one_div];
        rw [← Complex.cpow_neg, neg_sub, Complex.cpow_sub];
        · exact Eq.symm (LSeries.term_of_ne_zero hn (fun n ↦ ↑n ^ ν) s)
        · exact cast_ne_zero.mpr hn
  · unfold ArithmeticFunction.powR; aesop;

@[blueprint
  "abscissa_powR_le"
  (title := "abscissa powR le")
  (statement := /-- The abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$. -/)
  (proof := /--
  We apply \ref{LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow} which states that if there exists a constant $C$ such that $\|f(n)\| \leq C \cdot n^r$ for all $n$ sufficiently large, then the abscissa of absolute convergence of $L(f, s)$ is at most $r + 1$. In our case, we can take $f(n) = n^\nu$ and observe that $\|n^\nu\| = n^{\Re(\nu)}$. Thus, we can choose $C = 1$ and $r = \Re(\nu)$, which gives us the desired result that the abscissa of absolute convergence of $L(\text{pow}^R(\nu), s)$ is at most $\Re(\nu) + 1$.
  -/)]
lemma abscissa_powR_le (ν : ℂ) : LSeries.abscissaOfAbsConv (powR ν) ≤ ν.re + 1 := by
  have h_abs_le : ∀ n : ℕ, n ≠ 0 → ‖(powR ν n : ℂ)‖ ≤ (n : ℝ) ^ ν.re := by
    intros n hn_nonzero
    simp only [ArithmeticFunction.powR, hn_nonzero, coe_mk, ↓reduceIte];
    rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn_nonzero ) ]
  apply_rules [ LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow ];
  exact ⟨ 1, fun n hn => by simpa using h_abs_le n hn ⟩

/-- `ζ(s)ζ(s - ν) = Σ σ_ν(n) n^(-s)` for `Re(s) > 1` and `Re(s - ν) > 1`. -/
@[blueprint
  "LSeries_sigma_eq_riemannZeta_mul"
  (title := "LSeries sigma eq riemannZeta mul")
  (statement := /-- $\zeta(s)\zeta(s - \nu) = \sum_{n=1}^{\infty} \sigma_\nu(n) n^{-s}$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$. -/)
  (proof := /--
  The divisor power sum function $\sigma_\nu$ is the Dirichlet convolution of the constant function $1$ (i.e., $\zeta$) and the power function $n \mapsto n^\nu$. The L-series of a Dirichlet convolution is the product of the L-series of the individual functions. Since $L(1, s) = \zeta(s)$ and $L(n \mapsto n^\nu, s) = \zeta(s - \nu)$, we have $L(\sigma_\nu, s) = \zeta(s) \cdot \zeta(s - \nu)$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$.
  -/)]
theorem LSeries_sigma_eq_riemannZeta_mul (ν : ℂ) {s : ℂ} (hs : 1 < s.re) (hsν : 1 < (s - ν).re) :
    LSeries (↗(σᴿ ν)) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← LSeries_powR_eq ν hsν, sigmaR_eq_zeta_mul_powR];
  apply ArithmeticFunction.LSeries_mul
  · apply (ArithmeticFunction.abscissaOfAbsConv_zeta.trans_lt _)
    exact_mod_cast hs
  · apply lt_of_le_of_lt (abscissa_powR_le ν)
    rw[Complex.sub_re] at hsν
    exact_mod_cast (by linarith)

@[blueprint
  "LSeriesSummable_two_pow_omega"
  (title := "LSeriesSummable-two-pow-omega")
  (statement := /--
    An L-series is convergent if the absolute value of each term is term wise less than a summable series.
  -/)
  (proof := /--
    Apply triangle inequality and comparison test.
  -/)]
lemma LSeriesSummable.of_norm_le_norm {f g : ℕ → ℂ} {s : ℂ}
  (hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ g n) s n‖ ≤ ‖LSeries.term (fun n ↦ f n) s n‖)
  (hf : Summable (fun n ↦ ‖LSeries.term (fun n ↦ f n) s n‖)) : LSeriesSummable (fun n ↦ g n) s := by
  rw [LSeriesSummable, ← summable_norm_iff]
  exact hf.of_nonneg_of_le (fun n => norm_nonneg _) hgf

@[blueprint
  "LSeries.term_isMultiplicative_if_fun_isMultiplicative"
  (title := "LSeries.term-isMultiplicative-if-fun-isMultiplicative")
  (statement := /--
    If $f$ is a multiplicative function, then so to is $n\mapsto f(n)/n^s$.
  -/)
  (proof := /--
    Note that $f(mn)/(mn)^s=f(m)f(n)/(m^sn^s)=(f(m)/n^s)(f(n)/n^s)$.
  -/)]
lemma LSeries.term_isMultiplicative_if_fun_isMultiplicative {f : ℕ → ℂ} (hf : (toArithmeticFunction f).IsMultiplicative) (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term f s (m * n) = LSeries.term f s m * LSeries.term f s n := by
  simp only [LSeries.term, _root_.mul_eq_zero, cast_mul, mul_ite, mul_zero, ite_mul, zero_mul]
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  rw[← mul_div_mul_comm, Complex.natCast_mul_natCast_cpow]
  simp only [or_self, ↓reduceIte]
  congr 1
  simpa [toArithmeticFunction, m_eq_zero, n_eq_zero] using hf.2 mCn

namespace Ramanujan

/-- `‖σᴿ α n‖ ≤ d(n) · n^(max (Re α) 0)`: the divisor sum is bounded by the number of divisors
times the largest possible term. -/
private theorem sigmaR_norm_bound (α : ℂ) (n : ℕ) (hn : n ≠ 0) :
    ‖σᴿ α n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (max α.re 0) := by
  rw [sigmaR_apply]
  calc ‖∑ d ∈ n.divisors, (d : ℂ) ^ α‖
      ≤ ∑ d ∈ n.divisors, ‖(d : ℂ) ^ α‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (max α.re 0) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hd_le : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
        rw [Complex.norm_natCast_cpow_of_pos hd_pos]
        calc (d : ℝ) ^ α.re ≤ (d : ℝ) ^ (max α.re 0) :=
              Real.rpow_le_rpow_of_exponent_le hd1 (le_max_left _ _)
          _ ≤ (n : ℝ) ^ (max α.re 0) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast hd_le) (le_max_right _ _)
    _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (max α.re 0) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Prime-power inequality `(a+1)^2 ≤ C(a+3, 3)`, i.e. `τ(p^a)^2 ≤ d_4(p^a)`. -/
private theorem ppow_ineq (a : ℕ) : (a + 1) ^ 2 ≤ (a + 3).choose 3 := by
  have hdesc : (a + 3).descFactorial 3 = (a + 3) * (a + 2) * (a + 1) := by
    simp [Nat.descFactorial]; ring
  have key : (3 : ℕ).factorial * ((a + 3).choose 3) = (a + 3) * (a + 2) * (a + 1) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, hdesc]
  rw [show (3 : ℕ).factorial = 6 from by decide] at key
  nlinarith [key, Nat.le_self_pow (n := 3) (by norm_num) a]

/-- The divisor count squared is bounded by the fourfold divisor function: `τ(n)^2 ≤ d_4(n)`. -/
private theorem card_sq_le_d4 {n : ℕ} (hn : n ≠ 0) : (n.divisors.card) ^ 2 ≤ (d 4) n := by
  rw [Nat.card_divisors hn, (d_isMultiplicative 4).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization, ← Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro p hp
  rw [d_apply_prime_pow (by norm_num) (Nat.prime_of_mem_primeFactors hp)]
  simpa using ppow_ineq (n.factorization p)

/-- The combined pointwise bound `‖σᴿ α n · σᴿ β n‖ ≤ d_4(n) · n^(max(Re α,0)+max(Re β,0))`. -/
private theorem combined_bound (α β : ℂ) (n : ℕ) (hn : n ≠ 0) :
    ‖σᴿ α n * σᴿ β n‖ ≤ ((d 4) n : ℝ) * (n : ℝ) ^ (max α.re 0 + max β.re 0) := by
  rw [norm_mul]
  have hα := sigmaR_norm_bound α n hn
  have hβ := sigmaR_norm_bound β n hn
  have hcard : (n.divisors.card : ℝ) ^ 2 ≤ ((d 4) n : ℝ) := by exact_mod_cast card_sq_le_d4 hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  calc ‖σᴿ α n‖ * ‖σᴿ β n‖
      ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ (max α.re 0)) *
          ((n.divisors.card : ℝ) * (n : ℝ) ^ (max β.re 0)) :=
        mul_le_mul hα hβ (norm_nonneg _) (by positivity)
    _ = (n.divisors.card : ℝ) ^ 2 * ((n : ℝ) ^ (max α.re 0) * (n : ℝ) ^ (max β.re 0)) := by ring
    _ = (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (max α.re 0 + max β.re 0) := by
        rw [← Real.rpow_add hnpos]
    _ ≤ ((d 4) n : ℝ) * (n : ℝ) ^ (max α.re 0 + max β.re 0) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- The norm of the dominating term value `d_4(n) · n^c` for a real exponent `c`. -/
private theorem majorant_norm (c : ℝ) (n : ℕ) (hn : n ≠ 0) :
    ‖((d 4) n : ℂ) * (n : ℂ) ^ (c : ℂ)‖ = ((d 4) n : ℝ) * (n : ℝ) ^ c := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.norm_natCast,
      Complex.ofReal_re]

/-- The dominating series `∑ d_4(n) n^c n^(-s)` is norm-summable when `Re s > 1 + c`,
by a shift to the convergent series for `d_4`. -/
private theorem majorant_summable (c : ℝ) (s : ℂ) (hc : 1 < s.re - c) :
    Summable (fun n => ‖LSeries.term (fun m => ((d 4) m : ℂ) * (m : ℂ) ^ (c : ℂ)) s n‖) := by
  rw [summable_norm_iff]
  have hsc : 1 < (s - (c : ℂ)).re := by simp; linarith
  apply (LSeries_d_summable 4 hsc).congr
  intro n
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        Complex.cpow_sub _ _ (by exact_mod_cast hn)]
    simp only [ArithmeticFunction.natCoe_apply]
    field_simp

/-- The exponent `max(Re α,0) + max(Re β,0)` lies strictly below `Re s − 1` under the four
absolute-convergence hypotheses. -/
private theorem exponent_lt (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    1 < s.re - (max α.re 0 + max β.re 0) := by
  simp only [Complex.sub_re] at h2 h3 h4
  rcases le_or_gt α.re 0 with ha | ha <;> rcases le_or_gt β.re 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; linarith
  · rw [max_eq_right ha, max_eq_left hb.le]; linarith
  · rw [max_eq_left ha.le, max_eq_right hb]; linarith
  · rw [max_eq_left ha.le, max_eq_left hb.le]; linarith

/-- Brick B1: norm-summability of the L-series term for `n ↦ σᴿ α n · σᴿ β n`, the summability
hypothesis required by the Euler product. -/
private theorem B1_summable (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    Summable (fun n : ℕ => ‖LSeries.term (fun n => σᴿ α n * σᴿ β n) s n‖) := by
  set c : ℝ := max α.re 0 + max β.re 0 with hc_def
  -- It suffices to prove `LSeriesSummable` (= `Summable` of the term) of the coefficient function.
  refine summable_norm_iff.mpr ?_
  -- Dominate by the convergent majorant `m ↦ d_4(m) · m^c`.
  refine LSeriesSummable.of_norm_le_norm (f := fun m => ((d 4) m : ℂ) * (m : ℂ) ^ (c : ℂ))
    (g := fun n => σᴿ α n * σᴿ β n) (s := s) ?_ ?_
  · -- pointwise: ‖term g s n‖ ≤ ‖term f s n‖
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
        majorant_norm c n hn]
      apply div_le_div_of_nonneg_right (combined_bound α β n hn)
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      positivity
  · -- majorant summability
    exact majorant_summable c s (exponent_lt α β s h1 h2 h3 h4)

private theorem B2_term_mult (α β s : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    LSeries.term (fun n => σᴿ α n * σᴿ β n) s (m * n)
      = LSeries.term (fun n => σᴿ α n * σᴿ β n) s m
        * LSeries.term (fun n => σᴿ α n * σᴿ β n) s n := by
  have hmult : (toArithmeticFunction (fun n => σᴿ α n * σᴿ β n)).IsMultiplicative := by
    have hbridge : toArithmeticFunction (fun n => σᴿ α n * σᴿ β n) = (σᴿ α).pmul (σᴿ β) := by
      ext k
      simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, ArithmeticFunction.pmul_apply]
      by_cases hk : k = 0 <;> simp [hk]
    rw [hbridge]
    exact (isMultiplicative_sigmaR).pmul (isMultiplicative_sigmaR)
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative hmult s hmn

/-- `∑' n, (n+1) x^n = (1-x)^{-2}`. -/
private theorem tsum_succ_geom (x : ℂ) (h : ‖x‖ < 1) :
    ∑' n : ℕ, ((n : ℂ) + 1) * x ^ n = (1 - x)⁻¹ ^ 2 := by
  have hx : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at h)
  have h1 : ∀ n : ℕ, ((n : ℂ) + 1) * x ^ n = (n : ℂ) * x ^ n + x ^ n := fun n => by ring
  simp_rw [h1]
  rw [Summable.tsum_add ((hasSum_coe_mul_geometric_of_norm_lt_one h).summable)
      (summable_geometric_of_norm_lt_one h)]
  rw [tsum_coe_mul_geometric_of_norm_lt_one h, tsum_geometric_of_norm_lt_one h]
  field_simp; ring

/-- Summability of `n ↦ (n+1) x^n` for `‖x‖ < 1`. -/
private theorem summable_succ_geom (x : ℂ) (h : ‖x‖ < 1) : Summable (fun n : ℕ => ((n : ℂ) + 1) * x ^ n) := by
  have h2 : ∀ n : ℕ, ((n : ℂ) + 1) * x ^ n = (n : ℂ) * x ^ n + x ^ n := fun n => by ring
  simp_rw [h2]
  exact ((hasSum_coe_mul_geometric_of_norm_lt_one h).summable).add (summable_geometric_of_norm_lt_one h)

/-- Summability of `n ↦ (n+1) c^{n+1} u^n` for `‖c u‖ < 1`. -/
private theorem summable_succ_shift (c u : ℂ) (h : ‖c * u‖ < 1) :
    Summable (fun n : ℕ => ((n : ℂ) + 1) * c ^ (n + 1) * u ^ n) := by
  have h1 : ∀ n : ℕ, ((n : ℂ) + 1) * c ^ (n + 1) * u ^ n = c * (((n : ℂ) + 1) * (c * u) ^ n) :=
    fun n => by rw [mul_pow]; ring
  simp_rw [h1]; exact (summable_succ_geom (c * u) h).mul_left c

/-- `∑' n, (n+1) c^{n+1} u^n = c (1 - c u)^{-2}`. -/
private theorem tsum_succ_shift (c u : ℂ) (h : ‖c * u‖ < 1) :
    ∑' n : ℕ, ((n : ℂ) + 1) * c ^ (n + 1) * u ^ n = c * (1 - c * u)⁻¹ ^ 2 := by
  have h1 : ∀ n : ℕ, ((n : ℂ) + 1) * c ^ (n + 1) * u ^ n = c * (((n : ℂ) + 1) * (c * u) ^ n) :=
    fun n => by rw [mul_pow]; ring
  simp_rw [h1]; rw [tsum_mul_left, tsum_succ_geom (c * u) h]

/-- `∑' n, (n+1)^2 u^n = (1+u)/(1-u)^3`. -/
private theorem tsum_succ_sq_geom (u : ℂ) (h : ‖u‖ < 1) :
    ∑' n : ℕ, ((n : ℂ) + 1) ^ 2 * u ^ n = (1 + u) / (1 - u) ^ 3 := by
  have hu : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at h)
  have hcast : ∀ n : ℕ,
      ((n : ℂ) + 1) ^ 2 * u ^ n = 2 * (((n + 2).choose 2 : ℕ) : ℂ) * u ^ n - ((n : ℂ) + 1) * u ^ n := by
    intro n; rw [Nat.cast_choose_two ℂ]; push_cast; ring
  simp_rw [hcast]
  have s1 : Summable (fun n : ℕ => 2 * (((n + 2).choose 2 : ℕ) : ℂ) * u ^ n) := by
    have e : ∀ n : ℕ, 2 * (((n + 2).choose 2 : ℕ) : ℂ) * u ^ n
        = 2 * ((((n + 2).choose 2 : ℕ) : ℂ) * u ^ n) := fun n => by ring
    simp_rw [e]; exact (hasSum_choose_mul_geometric_of_norm_lt_one 2 h).summable.mul_left 2
  have s2 : Summable (fun n : ℕ => ((n : ℂ) + 1) * u ^ n) := summable_succ_geom u h
  rw [Summable.tsum_sub s1 s2]
  have t1 : ∑' n : ℕ, 2 * (((n + 2).choose 2 : ℕ) : ℂ) * u ^ n = 2 * (1 / (1 - u) ^ 3) := by
    have e : ∀ n : ℕ, 2 * (((n + 2).choose 2 : ℕ) : ℂ) * u ^ n
        = 2 * ((((n + 2).choose 2 : ℕ) : ℂ) * u ^ n) := fun n => by ring
    simp_rw [e]; rw [tsum_mul_left]; congr 1
    convert tsum_choose_mul_geometric_of_norm_lt_one 2 h using 2
  have t2 : ∑' n : ℕ, ((n : ℂ) + 1) * u ^ n = (1 - u)⁻¹ ^ 2 := tsum_succ_geom u h
  rw [t1, t2]; field_simp; ring

/-- Generic case `q ≠ 1`, `r ≠ 1`. -/
private theorem generic_case (q r u : ℂ) (hu : ‖u‖ < 1) (hqu : ‖q * u‖ < 1) (hru : ‖r * u‖ < 1)
    (hqru : ‖q * r * u‖ < 1) (hq : q ≠ 1) (hr : r ≠ 1) :
    ∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), q ^ i) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e
      = (1 - q * r * u ^ 2) / ((1 - u) * (1 - q * u) * ((1 - r * u) * (1 - q * r * u))) := by
  have h1q : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have h1r : (1 : ℂ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have nu : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hu)
  have nqu : (1 : ℂ) - q * u ≠ 0 := sub_ne_zero.mpr (by rintro h; rw [← h] at hqu; simp at hqu)
  have nru : (1 : ℂ) - r * u ≠ 0 := sub_ne_zero.mpr (by rintro h; rw [← h] at hru; simp at hru)
  have nqru : (1 : ℂ) - q * r * u ≠ 0 := sub_ne_zero.mpr (by rintro h; rw [← h] at hqru; simp at hqru)
  have su : Summable (fun e : ℕ => u ^ e) := summable_geometric_of_norm_lt_one hu
  have sq : Summable (fun e : ℕ => q ^ (e + 1) * u ^ e) := by
    have h : ∀ e : ℕ, q ^ (e + 1) * u ^ e = q * (q * u) ^ e := fun e => by rw [mul_pow]; ring
    simp_rw [h]; exact (summable_geometric_of_norm_lt_one hqu).mul_left q
  have sr : Summable (fun e : ℕ => r ^ (e + 1) * u ^ e) := by
    have h : ∀ e : ℕ, r ^ (e + 1) * u ^ e = r * (r * u) ^ e := fun e => by rw [mul_pow]; ring
    simp_rw [h]; exact (summable_geometric_of_norm_lt_one hru).mul_left r
  have sqr : Summable (fun e : ℕ => (q * r) ^ (e + 1) * u ^ e) := by
    have h : ∀ e : ℕ, (q * r) ^ (e + 1) * u ^ e = (q * r) * (q * r * u) ^ e :=
      fun e => by rw [mul_pow]; ring_nf
    simp_rw [h]; exact (summable_geometric_of_norm_lt_one hqru).mul_left (q * r)
  have key : ∀ e : ℕ, ((1 - q) * (1 - r)) *
      (((∑ i ∈ Finset.range (e + 1), q ^ i) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e)
      = (u ^ e - q ^ (e + 1) * u ^ e - r ^ (e + 1) * u ^ e + (q * r) ^ (e + 1) * u ^ e) := by
    intro e
    have hgq := mul_neg_geom_sum q (e + 1)
    have hgr := mul_neg_geom_sum r (e + 1)
    calc ((1 - q) * (1 - r)) *
            (((∑ i ∈ Finset.range (e + 1), q ^ i) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e)
        = ((1 - q) * (∑ i ∈ Finset.range (e + 1), q ^ i)) *
            ((1 - r) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e := by ring
      _ = (1 - q ^ (e + 1)) * (1 - r ^ (e + 1)) * u ^ e := by rw [hgq, hgr]
      _ = (u ^ e - q ^ (e + 1) * u ^ e - r ^ (e + 1) * u ^ e + (q * r) ^ (e + 1) * u ^ e) := by
            rw [mul_pow]; ring
  have tq : ∑' e : ℕ, q ^ (e + 1) * u ^ e = q * (1 - q * u)⁻¹ := by
    have h : ∀ e : ℕ, q ^ (e + 1) * u ^ e = q * (q * u) ^ e := fun e => by rw [mul_pow]; ring
    simp_rw [h]; rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqu]
  have tr : ∑' e : ℕ, r ^ (e + 1) * u ^ e = r * (1 - r * u)⁻¹ := by
    have h : ∀ e : ℕ, r ^ (e + 1) * u ^ e = r * (r * u) ^ e := fun e => by rw [mul_pow]; ring
    simp_rw [h]; rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hru]
  have tqr : ∑' e : ℕ, (q * r) ^ (e + 1) * u ^ e = (q * r) * (1 - q * r * u)⁻¹ := by
    have h : ∀ e : ℕ, (q * r) ^ (e + 1) * u ^ e = (q * r) * (q * r * u) ^ e :=
      fun e => by rw [mul_pow]; ring_nf
    simp_rw [h]; rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hqru]
  set F : ℂ := (1 - u)⁻¹ - q * (1 - q * u)⁻¹ - r * (1 - r * u)⁻¹ + (q * r) * (1 - q * r * u)⁻¹ with hF
  have hSF : ((1 - q) * (1 - r)) *
      (∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), q ^ i) *
        (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e) = F := by
    rw [← tsum_mul_left]
    simp_rw [key]
    rw [((su.sub sq).sub sr).tsum_add sqr, (su.sub sq).tsum_sub sr, su.tsum_sub sq]
    rw [tsum_geometric_of_norm_lt_one hu, tq, tr, tqr, hF]
  have hFD : F * ((1 - u) * (1 - q * u) * (1 - r * u) * (1 - q * r * u))
      = (1 - q) * (1 - r) * (1 - q * r * u ^ 2) := by
    rw [hF]
    have e1 : (1 - u)⁻¹ * (1 - u) = 1 := inv_mul_cancel₀ nu
    have e2 : (1 - q * u)⁻¹ * (1 - q * u) = 1 := inv_mul_cancel₀ nqu
    have e3 : (1 - r * u)⁻¹ * (1 - r * u) = 1 := inv_mul_cancel₀ nru
    have e4 : (1 - q * r * u)⁻¹ * (1 - q * r * u) = 1 := inv_mul_cancel₀ nqru
    linear_combination
      ((1 - q * u) * (1 - r * u) * (1 - q * r * u)) * e1
      - q * ((1 - u) * (1 - r * u) * (1 - q * r * u)) * e2
      - r * ((1 - u) * (1 - q * u) * (1 - q * r * u)) * e3
      + (q * r) * ((1 - u) * (1 - q * u) * (1 - r * u)) * e4
  apply mul_left_cancel₀ (mul_ne_zero h1q h1r)
  rw [hSF]
  have hD : ((1 - u) * (1 - q * u) * ((1 - r * u) * (1 - q * r * u))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero nu nqu) (mul_ne_zero nru nqru)
  rw [mul_div_assoc']
  refine (eq_div_of_mul_eq hD ?_)
  linear_combination hFD

/-- Case `q = 1`, `r ≠ 1`. -/
private theorem case_q1 (r u : ℂ) (hu : ‖u‖ < 1) (hru : ‖r * u‖ < 1) (hr : r ≠ 1) :
    ∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) *
      (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e
      = (1 - 1 * r * u ^ 2) / ((1 - u) * (1 - 1 * u) * ((1 - r * u) * (1 - 1 * r * u))) := by
  have h1r : (1 : ℂ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have nu : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hu)
  have nru : (1 : ℂ) - r * u ≠ 0 := sub_ne_zero.mpr (by rintro h; rw [← h] at hru; simp at hru)
  have key : ∀ e : ℕ, ((1 - r)) *
      (((∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) *
        (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e)
      = (((e : ℂ) + 1) * u ^ e - ((e : ℂ) + 1) * r ^ (e + 1) * u ^ e) := by
    intro e
    have hg : (1 - r) * (∑ j ∈ Finset.range (e + 1), r ^ j) = 1 - r ^ (e + 1) :=
      mul_neg_geom_sum r (e + 1)
    have hone : (∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) = (e : ℂ) + 1 := by
      simp [one_pow, Finset.sum_const, Finset.card_range]
    rw [hone]
    calc (1 - r) * (((e : ℂ) + 1) * (∑ j ∈ Finset.range (e + 1), r ^ j) * u ^ e)
        = ((e : ℂ) + 1) * ((1 - r) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e := by ring
      _ = ((e : ℂ) + 1) * (1 - r ^ (e + 1)) * u ^ e := by rw [hg]
      _ = (((e : ℂ) + 1) * u ^ e - ((e : ℂ) + 1) * r ^ (e + 1) * u ^ e) := by ring
  set F : ℂ := (1 - u)⁻¹ ^ 2 - r * (1 - r * u)⁻¹ ^ 2 with hF
  have hSF : (1 - r) * (∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) *
      (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e) = F := by
    rw [← tsum_mul_left]
    simp_rw [key]
    rw [Summable.tsum_sub (summable_succ_geom u hu) (summable_succ_shift r u hru)]
    rw [tsum_succ_geom u hu, tsum_succ_shift r u hru, hF]
  apply mul_left_cancel₀ h1r
  rw [hSF]
  have hFD : F * ((1 - u) ^ 2 * (1 - r * u) ^ 2) = (1 - r) * (1 - r * u ^ 2) := by
    rw [hF]
    have e1 : (1 - u)⁻¹ ^ 2 * (1 - u) ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ nu, one_pow]
    have e2 : (1 - r * u)⁻¹ ^ 2 * (1 - r * u) ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ nru, one_pow]
    linear_combination ((1 - r * u) ^ 2) * e1 - r * ((1 - u) ^ 2) * e2
  have hD : ((1 - u) * (1 - 1 * u) * ((1 - r * u) * (1 - 1 * r * u))) ≠ 0 := by
    simp only [one_mul]; exact mul_ne_zero (mul_ne_zero nu nu) (mul_ne_zero nru nru)
  rw [mul_div_assoc']
  refine (eq_div_of_mul_eq hD ?_)
  have hassoc : ((1 - u) * (1 - 1 * u) * ((1 - r * u) * (1 - 1 * r * u))) = (1 - u) ^ 2 * (1 - r * u) ^ 2 := by
    ring
  rw [hassoc]; linear_combination hFD

/-- Case `q ≠ 1`, `r = 1`. -/
private theorem case_r1 (q u : ℂ) (hu : ‖u‖ < 1) (hqu : ‖q * u‖ < 1) (hq : q ≠ 1) :
    ∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), q ^ i) *
      (∑ j ∈ Finset.range (e + 1), (1 : ℂ) ^ j)) * u ^ e
      = (1 - q * 1 * u ^ 2) / ((1 - u) * (1 - q * u) * ((1 - 1 * u) * (1 - q * 1 * u))) := by
  have h1q : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have nu : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hu)
  have nqu : (1 : ℂ) - q * u ≠ 0 := sub_ne_zero.mpr (by rintro h; rw [← h] at hqu; simp at hqu)
  have key : ∀ e : ℕ, ((1 - q)) *
      (((∑ i ∈ Finset.range (e + 1), q ^ i) *
        (∑ j ∈ Finset.range (e + 1), (1 : ℂ) ^ j)) * u ^ e)
      = (((e : ℂ) + 1) * u ^ e - ((e : ℂ) + 1) * q ^ (e + 1) * u ^ e) := by
    intro e
    have hg : (1 - q) * (∑ i ∈ Finset.range (e + 1), q ^ i) = 1 - q ^ (e + 1) :=
      mul_neg_geom_sum q (e + 1)
    have hone : (∑ j ∈ Finset.range (e + 1), (1 : ℂ) ^ j) = (e : ℂ) + 1 := by
      simp [one_pow, Finset.sum_const, Finset.card_range]
    rw [hone]
    calc (1 - q) * (((∑ i ∈ Finset.range (e + 1), q ^ i) * ((e : ℂ) + 1)) * u ^ e)
        = ((e : ℂ) + 1) * ((1 - q) * (∑ i ∈ Finset.range (e + 1), q ^ i)) * u ^ e := by ring
      _ = ((e : ℂ) + 1) * (1 - q ^ (e + 1)) * u ^ e := by rw [hg]
      _ = (((e : ℂ) + 1) * u ^ e - ((e : ℂ) + 1) * q ^ (e + 1) * u ^ e) := by ring
  set F : ℂ := (1 - u)⁻¹ ^ 2 - q * (1 - q * u)⁻¹ ^ 2 with hF
  have hSF : (1 - q) * (∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), q ^ i) *
      (∑ j ∈ Finset.range (e + 1), (1 : ℂ) ^ j)) * u ^ e) = F := by
    rw [← tsum_mul_left]
    simp_rw [key]
    rw [Summable.tsum_sub (summable_succ_geom u hu) (summable_succ_shift q u hqu)]
    rw [tsum_succ_geom u hu, tsum_succ_shift q u hqu, hF]
  apply mul_left_cancel₀ h1q
  rw [hSF]
  have hFD : F * ((1 - u) ^ 2 * (1 - q * u) ^ 2) = (1 - q) * (1 - q * u ^ 2) := by
    rw [hF]
    have e1 : (1 - u)⁻¹ ^ 2 * (1 - u) ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ nu, one_pow]
    have e2 : (1 - q * u)⁻¹ ^ 2 * (1 - q * u) ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ nqu, one_pow]
    linear_combination ((1 - q * u) ^ 2) * e1 - q * ((1 - u) ^ 2) * e2
  have hD : ((1 - u) * (1 - q * u) * ((1 - 1 * u) * (1 - q * 1 * u))) ≠ 0 := by
    simp only [one_mul, mul_one]; exact mul_ne_zero (mul_ne_zero nu nqu) (mul_ne_zero nu nqu)
  rw [mul_div_assoc']
  refine (eq_div_of_mul_eq hD ?_)
  have hassoc : ((1 - u) * (1 - q * u) * ((1 - 1 * u) * (1 - q * 1 * u))) = (1 - u) ^ 2 * (1 - q * u) ^ 2 := by
    ring
  rw [hassoc]; linear_combination hFD

/-- Case `q = 1`, `r = 1`. -/
private theorem case_qr1 (u : ℂ) (hu : ‖u‖ < 1) :
    ∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) *
      (∑ j ∈ Finset.range (e + 1), (1 : ℂ) ^ j)) * u ^ e
      = (1 - 1 * 1 * u ^ 2) / ((1 - u) * (1 - 1 * u) * ((1 - 1 * u) * (1 - 1 * 1 * u))) := by
  have nu : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hu)
  have key : ∀ e : ℕ, ((∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) *
      (∑ j ∈ Finset.range (e + 1), (1 : ℂ) ^ j)) * u ^ e = ((e : ℂ) + 1) ^ 2 * u ^ e := by
    intro e
    have hone : (∑ i ∈ Finset.range (e + 1), (1 : ℂ) ^ i) = (e : ℂ) + 1 := by
      simp [one_pow, Finset.sum_const, Finset.card_range]
    rw [hone]; ring
  simp_rw [key]
  rw [tsum_succ_sq_geom u hu]
  rw [eq_div_iff (by simp only [one_mul]; exact mul_ne_zero (mul_ne_zero nu nu) (mul_ne_zero nu nu))]
  field_simp; ring

/-- The abstract local Euler factor, all cases combined. -/
private theorem abstract_all (q r u : ℂ) (hu : ‖u‖ < 1) (hqu : ‖q * u‖ < 1) (hru : ‖r * u‖ < 1)
    (hqru : ‖q * r * u‖ < 1) :
    ∑' e : ℕ, ((∑ i ∈ Finset.range (e + 1), q ^ i) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e
      = (1 - q * r * u ^ 2) / ((1 - u) * (1 - q * u) * ((1 - r * u) * (1 - q * r * u))) := by
  by_cases hq : q = 1
  · by_cases hr : r = 1
    · subst hq; subst hr; exact case_qr1 u hu
    · subst hq; exact case_q1 r u hu hru hr
  · by_cases hr : r = 1
    · subst hr; exact case_r1 q u hu hqu hq
    · exact generic_case q r u hu hqu hru hqru hq hr

/-- For a prime `p` and `Re w > 0`, `‖p^{-w}‖ < 1`. -/
private theorem norm_p_neg (p : Nat.Primes) (w : ℂ) (hw : 0 < w.re) : ‖((p : ℕ) : ℂ) ^ (-w)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
  simp only [Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)

private theorem B3_local (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) (p : Nat.Primes) :
    ∑' e : ℕ, LSeries.term (fun n => σᴿ α n * σᴿ β n) s ((p : ℕ) ^ e)
      = (1 - ((p : ℕ) : ℂ) ^ (-(2 * s - α - β))) /
        (((1 - ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α)))) *
         ((1 - ((p : ℕ) : ℂ) ^ (-(s - β))) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α - β))))) := by
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  set q : ℂ := ((p : ℕ) : ℂ) ^ α with hq
  set r : ℂ := ((p : ℕ) : ℂ) ^ β with hr
  set u : ℂ := ((p : ℕ) : ℂ) ^ (-s) with hu
  have hterm : ∀ e : ℕ, LSeries.term (fun n => σᴿ α n * σᴿ β n) s ((p : ℕ) ^ e)
      = ((∑ i ∈ Finset.range (e + 1), q ^ i) * (∑ j ∈ Finset.range (e + 1), r ^ j)) * u ^ e := by
    intro e
    rw [LSeries.term_of_ne_zero (by exact_mod_cast (pow_ne_zero e p.prop.ne_zero))]
    rw [show (((p : ℕ) ^ e : ℕ) : ℂ) = ((p : ℕ) : ℂ) ^ e by push_cast; ring]
    rw [div_eq_mul_inv]
    have hσα : σᴿ α ((p : ℕ) ^ e) = ∑ i ∈ Finset.range (e + 1), q ^ i := by
      rw [sigmaR_apply_prime_pow p.prop, hq]
      exact Finset.sum_congr rfl fun j _ => (Complex.cpow_nat_mul _ j α)
    have hσβ : σᴿ β ((p : ℕ) ^ e) = ∑ j ∈ Finset.range (e + 1), r ^ j := by
      rw [sigmaR_apply_prime_pow p.prop, hr]
      exact Finset.sum_congr rfl fun j _ => (Complex.cpow_nat_mul _ j β)
    rw [hσα, hσβ]
    congr 1
    rw [hu, show (((p : ℕ) : ℂ) ^ (-s)) ^ e = ((p : ℕ) : ℂ) ^ ((e : ℂ) * (-s)) from
        (Complex.cpow_nat_mul _ e (-s)).symm]
    rw [Complex.natCast_cpow_natCast_mul, Complex.cpow_neg]
  simp_rw [hterm]
  have bu : ‖u‖ < 1 := by rw [hu]; exact norm_p_neg p s (by linarith)
  have bqu : ‖q * u‖ < 1 := by
    rw [hq, hu, show ((p : ℕ) : ℂ) ^ α * ((p : ℕ) : ℂ) ^ (-s) = ((p : ℕ) : ℂ) ^ (-(s - α)) by
        rw [← Complex.cpow_add _ _ hpne]; ring_nf]
    exact norm_p_neg p (s - α) (by linarith)
  have bru : ‖r * u‖ < 1 := by
    rw [hr, hu, show ((p : ℕ) : ℂ) ^ β * ((p : ℕ) : ℂ) ^ (-s) = ((p : ℕ) : ℂ) ^ (-(s - β)) by
        rw [← Complex.cpow_add _ _ hpne]; ring_nf]
    exact norm_p_neg p (s - β) (by linarith)
  have bqru : ‖q * r * u‖ < 1 := by
    rw [hq, hr, hu, show ((p : ℕ) : ℂ) ^ α * ((p : ℕ) : ℂ) ^ β * ((p : ℕ) : ℂ) ^ (-s)
        = ((p : ℕ) : ℂ) ^ (-(s - α - β)) by
        rw [← Complex.cpow_add _ _ hpne, ← Complex.cpow_add _ _ hpne]; ring_nf]
    exact norm_p_neg p (s - α - β) (by linarith)
  rw [abstract_all q r u bu bqu bru bqru]
  have equ : q * u = ((p : ℕ) : ℂ) ^ (-(s - α)) := by
    rw [hq, hu, ← Complex.cpow_add _ _ hpne]; ring_nf
  have eru : r * u = ((p : ℕ) : ℂ) ^ (-(s - β)) := by
    rw [hr, hu, ← Complex.cpow_add _ _ hpne]; ring_nf
  have eqru : q * r * u = ((p : ℕ) : ℂ) ^ (-(s - α - β)) := by
    rw [hq, hr, hu, ← Complex.cpow_add _ _ hpne, ← Complex.cpow_add _ _ hpne]; ring_nf
  have eqru2 : q * r * u ^ 2 = ((p : ℕ) : ℂ) ^ (-(2 * s - α - β)) := by
    rw [hq, hr, hu, sq, ← Complex.cpow_add _ _ hpne, ← Complex.cpow_add _ _ hpne,
        ← Complex.cpow_add _ _ hpne]; ring_nf
  rw [eqru2, equ, eru, eqru, hu]


/-- B4 (HasProd form): Euler product for L(σ_α·σ_β). -/
theorem ram_eulerProduct_hasProd (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    HasProd (fun p : Nat.Primes =>
        (1 - ((p : ℕ) : ℂ) ^ (-(2 * s - α - β))) /
        (((1 - ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α)))) *
         ((1 - ((p : ℕ) : ℂ) ^ (-(s - β))) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α - β))))))
      (LSeries (fun n => σᴿ α n * σᴿ β n) s) := by
  have key := EulerProduct.eulerProduct_hasProd
      (f := LSeries.term (fun n => σᴿ α n * σᴿ β n) s)
      (by simp [LSeries.term, sigmaR_one])
      (fun {m n} h => B2_term_mult α β s h)
      (B1_summable α β s h1 h2 h3 h4)
      (LSeries.term_zero _ s)
  have hfac : (fun p : Nat.Primes =>
        (1 - ((p : ℕ) : ℂ) ^ (-(2 * s - α - β))) /
        (((1 - ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α)))) *
         ((1 - ((p : ℕ) : ℂ) ^ (-(s - β))) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α - β))))))
      = (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (fun n => σᴿ α n * σᴿ β n) s ((p : ℕ) ^ e)) :=
    funext (fun p => (B3_local α β s h1 h2 h3 h4 p).symm)
  rw [hfac]
  exact key

/-- B4 (tprod form). -/
theorem ram_eulerProduct_tprod (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    LSeries (fun n => σᴿ α n * σᴿ β n) s = ∏' p : Nat.Primes,
        (1 - ((p : ℕ) : ℂ) ^ (-(2 * s - α - β))) /
        (((1 - ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α)))) *
         ((1 - ((p : ℕ) : ℂ) ^ (-(s - β))) * (1 - ((p : ℕ) : ℂ) ^ (-(s - α - β))))) :=
  (ram_eulerProduct_hasProd α β s h1 h2 h3 h4).tprod_eq.symm

end Ramanujan

/--
Ramanujan formula:
`ζ(s)ζ(s-α)ζ(s-β)ζ(s-α-β)=ζ(2s-α-β) ∑ σ_α(n)σ_β(n)n^(-s)`. -/
@[blueprint
  "zeta_mul_zeta_mul_zeta_mul_zeta_eq"
  (title := "zeta mul zeta mul zeta mul zeta eq")
  (statement := /-- Ramanujan formula: $\zeta(s)\zeta(s-\alpha)\zeta(s-\beta)\zeta(s-\alpha-\beta)=\zeta(2s-\alpha-\beta) \sum_{n=1}^{\infty} \sigma_\alpha(n)\sigma_\beta(n)n^{-s}$.
  \begin{verbatim}
  This is IK (1.28).
  \end{verbatim}
   -/)
  (proof := /--
  This is a direct consequence of the multiplicative properties of the functions involved and the definition of the L-series. The left-hand side can be expressed as a product of L-series corresponding to the functions $\zeta$, $n \mapsto n^{-\alpha}$, and $n \mapsto n^{-\beta}$. The right-hand side involves the L-series of the convolution of $\sigma_\alpha$ and $\sigma_\beta$, which can be expressed in terms of the L-series of $\zeta$ and the power functions. By carefully applying the properties of Dirichlet convolutions and the definitions of the L-series, we can derive the stated formula.
  -/)]
theorem zeta_mul_zeta_mul_zeta_mul_zeta_eq (α β s : ℂ) (h1 : 1 < s.re) (h2 : 1 < (s - α).re)
    (h3 : 1 < (s - β).re) (h4 : 1 < (s - α - β).re) :
    riemannZeta s * riemannZeta (s - α) * riemannZeta (s - β) * riemannZeta (s - α - β) =
      riemannZeta (2 * s - α - β) *
      LSeries (fun n ↦ σᴿ α n * σᴿ β n) s := by
  have h5 : 1 < (2 * s - α - β).re := by
    have e : (2 * s - α - β).re = (s - α).re + (s - β).re := by
      simp only [Complex.sub_re, Complex.mul_re]; norm_num; ring
    rw [e]; linarith
  have m1 := (riemannZeta_eulerProduct_hasProd h1).multipliable
  have m2 := (riemannZeta_eulerProduct_hasProd h2).multipliable
  have m3 := (riemannZeta_eulerProduct_hasProd h3).multipliable
  have m4 := (riemannZeta_eulerProduct_hasProd h4).multipliable
  have m5 := (riemannZeta_eulerProduct_hasProd h5).multipliable
  have mL := (Ramanujan.ram_eulerProduct_hasProd α β s h1 h2 h3 h4).multipliable
  rw [← riemannZeta_eulerProduct_tprod h1, ← riemannZeta_eulerProduct_tprod h2,
      ← riemannZeta_eulerProduct_tprod h3, ← riemannZeta_eulerProduct_tprod h4,
      ← riemannZeta_eulerProduct_tprod h5, Ramanujan.ram_eulerProduct_tprod α β s h1 h2 h3 h4,
      ← Multipliable.tprod_mul m1 m2, ← Multipliable.tprod_mul (m1.mul m2) m3,
      ← Multipliable.tprod_mul ((m1.mul m2).mul m3) m4, ← Multipliable.tprod_mul m5 mL]
  refine tprod_congr (fun p => ?_)
  have nA := Complex.one_sub_prime_cpow_ne_zero p.2 h1
  have nB := Complex.one_sub_prime_cpow_ne_zero p.2 h2
  have nC := Complex.one_sub_prime_cpow_ne_zero p.2 h3
  have nD := Complex.one_sub_prime_cpow_ne_zero p.2 h4
  have nE := Complex.one_sub_prime_cpow_ne_zero p.2 h5
  set a := ((p : ℕ) : ℂ) ^ (-s)
  set b := ((p : ℕ) : ℂ) ^ (-(s - α))
  set c := ((p : ℕ) : ℂ) ^ (-(s - β))
  set d := ((p : ℕ) : ℂ) ^ (-(s - α - β))
  set e := ((p : ℕ) : ℂ) ^ (-(2 * s - α - β))
  field_simp

/-- Corollary:  `ζ(s)^4=ζ(2s) ∑ τ(n)^2 n^(-s)` -/
@[blueprint
  "zeta_pow_four_eq"
  (title := "zeta pow four eq")
  (statement := /-- Corollary: $\zeta(s)^4 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$.
  \begin{verbatim}
  This is IK (1.29).
  \end{verbatim}
  -/)
  (proof := /--
  This is a special case of the previous theorem where we set $\alpha = \beta = 0$.
  -/)]
theorem zeta_pow_four_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 4 = riemannZeta (2 * s) * LSeries (fun n ↦ (τ n) ^ 2) s := by
  convert (zeta_mul_zeta_mul_zeta_mul_zeta_eq 0 0 s hs (by simpa using hs) (by simpa using hs)
      (by simpa using hs)) using 1
  · ring_nf
  · congr
    · ring_nf
    · simp [tau, sigma, sigmaR, pow_two]

/--
Baby Rankin-Selberg:
`ζ(s)∑τ(n^2)n^-s = ∑τ(n)^2 n^-s`. -/
@[blueprint
  "zeta_mul_tau_square_eq"
  (title := "zeta mul tau square eq")
  (statement := /-- Baby Rankin-Selberg: $\zeta(s)\sum_{n=1}^{\infty}\tau(n^2)n^{-s} = \sum_{n=1}^{\infty}\tau(n)^2 n^{-s}$.
  \begin{verbatim}
  Precursor to IK (1.30).
  \end{verbatim}
  -/)
  (proof := /--
  This follows from the multiplicative properties of the divisor function $\tau$ and the definition of the L-series. The left-hand side can be expressed as a product of L-series corresponding to $\zeta$ and the function $n \mapsto \tau(n^2)$. The right-hand side is the L-series of the function $n \mapsto \tau(n)^2$. By analyzing the Euler products and using the fact that $\tau(n)$ counts divisors, we can derive the stated equality.
  -/)]
lemma zeta_mul_tau_square_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s * LSeries (fun n ↦ τ (n ^ 2)) s = LSeries (fun n ↦ (τ n) ^ 2) s := by
  sorry

/--
Zeta cubed:
`ζ(s)^3 = ζ(2s) ∑ τ(n^2) n^(-s)`. -/
@[blueprint
  "zeta_pow_three_eq"
  (title := "zeta pow three eq")
  (statement := /-- Zeta cubed: $\zeta(s)^3 = \zeta(2s) \sum_{n=1}^{\infty}\tau(n^2) n^{-s}$.
  \begin{verbatim}
  This is IK (1.30).
  \end{verbatim}
  -/)
  (proof := /--
  This follows from the previous two theorems. From the corollary of Ramanujan's formula, we have $\zeta(s)^4 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$. From the Baby Rankin-Selberg result, we have $\zeta(s) \sum_{n=1}^{\infty} \tau(n^2) n^{-s} = \sum_{n=1}^{\infty} \tau(n)^2 n^{-s}$. Combining these two results, we can express $\zeta(s)^4$ in terms of $\zeta(s)$ and $\sum_{n=1}^{\infty} \tau(n^    2) n^{-s}$, which leads to the conclusion that $\zeta(s)^3 = \zeta(2s) \sum_{n=1}^{\infty} \tau(n^2) n^{-s}$.
  -/)]
lemma zeta_pow_three_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 = riemannZeta (2 * s) * LSeries (fun n ↦ τ (n ^ 2)) s := by
  apply mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)
  linear_combination (zeta_pow_four_eq s hs) - riemannZeta (2 * s) * (zeta_mul_tau_square_eq s hs)

/--
Zeta cubed alt:
`ζ(s)^3 =  ∑_n (∑ d^2 m = n, τ (m^2)) n^(-s)`. -/
@[blueprint
  "zeta_pow_three_eq_alt"
  (title := "zeta pow three eq alt")
  (statement := /-- symmetric square $L$-function for $\zeta^2$:
  $$\zeta(s)^3 = \sum_{n=1}^{\infty} \left( \sum_{d^2 m = n} \tau(m^2) \right) n^{-s}.$$
  \begin{verbatim}
  Alternative expression for `ζ^3`, in IK between (1.30) and (1.31).
  \end{verbatim}
  -/)
  (proof := /--
  This is an alternative expression for $\zeta(s)^3$ that can be derived from the previous results. By expressing $\zeta(s)^3$ in terms of the L-series of $\tau(n^2)$ and using the properties of Dirichlet convolutions, we can rewrite the sum in a way that involves summing over divisors $d$ and corresponding $m$ such that $d^2 m = n$. This rearrangement of the series allows us to express $\zeta(s)^3$ in the desired form.
  -/)]
lemma zeta_pow_three_eq_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 3 =
    LSeries (fun n ↦
      ∑ dm ∈ n.divisors ×ˢ n.divisors with dm.1 ^ 2 * dm.2 = n, τ (dm.2 ^ 2)) s := by
  sorry

@[blueprint
  "two_pow_omega_le_sigma_zero"
  (title := "two-pow-omega-le-sigma-zero")
  (statement := /--
    We have the inequality $2^{\omega(n)}\leq\sigma_0(n)$ when $n\neq 0$.
  -/)
  (proof := /--
    Recall that $\omega(n)$ is the number of distinct prime factors of $n$. Thus,
    $$2^{\omega(n)}=\prod_{p|n}2.$$
    Likewise, $\sigma_0(n)$ is the number of divisors of $n$. We can write this as
    $$\prod_{p|n}(1+v_p(n))=\sigma_0(n)$$
    where $v_p(n)$ denotes the $p$-adic valuation of $n$. For $p|n$ we have that $2\leq 1+v_p(n)$.
    Thus the result immediately follows.
  -/)]
lemma two_pow_omega_le_sigma_zero {n : ℕ} (hn : n ≠ 0) :
    2 ^ (ω n) ≤ σ 0 n := by
  rw [show ω n = (Nat.primeFactors n).card from rfl, ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn, ← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  simpa [two_mul] using
  (Nat.Prime.dvd_iff_one_le_factorization (prime_of_mem_primeFactors hp) hn).mp
    (dvd_of_mem_primeFactors hp)

@[blueprint
  "LSeriesSummable_two_pow_omega"
  (title := "LSeriesSummable-two-pow-omega")
  (statement := /--
    The $L$-series with coefficients given by $2^{\omega(n)}$ converges on the region $1<\Re(s)$.
  -/)
  (proof := /--
    This follows by comparison test against the $L$-series with coefficients given by $\sigma_0(n)$.
  -/)]
lemma LSeriesSummable_two_pow_omega {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ 2 ^ (ω n)) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ 2 ^ ω n) s n‖ ≤ ‖LSeries.term (fun n ↦ σ 0 n) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow, Complex.norm_ofNat,
        RCLike.norm_natCast]
      exact div_le_div_of_nonneg_right (by exact_mod_cast two_pow_omega_le_sigma_zero hn) (norm_nonneg _)
  apply LSeriesSummable.of_norm_le_norm hgf
  rw [summable_norm_iff, ← LSeriesSummable]
  convert LSeries_d_summable 2 hs using 1;
  exact funext fun n => by rw [d_two]; rfl

@[blueprint
  "powOfAdditive_isMultiplicative"
  (title := "powOfAdditive-isMultiplicative")
  (statement := /--
    If $f$ is an additive function, then so to is $n\mapsto k^{f(n)}$ for any fixed $k$.
  -/)
  (proof := /--
    Note that $k^{f(mn)}=k^{f(m)+f(n)}=k^{f(m)}k^{f(n)}$.
  -/)]
lemma powOfAdditive_isMultiplicative
    {R : Type u_1} [CommMonoidWithZero R] (k : R)
    {f : ArithmeticFunction ℕ} (hf : f.IsAdditive) :
    (toArithmeticFunction (fun n ↦ k ^ (f n))).IsMultiplicative := by
  simp only [IsAdditive, ne_eq] at hf
  have := hf one_ne_zero one_ne_zero (coprime_one_right 1)
  rw [mul_one, left_eq_add] at this
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, this,
    pow_zero, mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf m_eq_zero n_eq_zero mCn, pow_add]

@[blueprint
  "two_pow_omega_isMultiplicative"
  (title := "two-pow-omega-isMultiplicative")
  (statement := /--
    The function $n\mapsto 2^{\omega(n)}$ is multiplicative.
  -/)
  (proof := /--
    This follows directly from Lemma \ref{powOfAdditive-isMultiplicative} and the fact that $\omega(mn)=\omega(m)+\omega(n)$.
  -/)]
lemma two_pow_omega_isMultiplicative :
    (toArithmeticFunction (fun n ↦ (2 : ℂ) ^ ω n)).IsMultiplicative := by
  exact powOfAdditive_isMultiplicative 2 (fun hm hn h => ArithmeticFunction.cardDistinctFactors_mul h)

@[blueprint
  "two_pow_omega_LSeries.term_isMultiplicative"
  (title := "two-pow-omega-LSeries.term-isMultiplicative")
  (statement := /--
    We have that $n\mapsto 2^{\omega(n)}/n^{-s}$ is a multiplicative function.
  -/)
  (proof := /--
    Follows as a consequence of Lemma \ref{LSeries.term-isMultiplicative-if-fun-isMultiplicative}
    and \ref{two-pow-omega-isMultiplicative}.
  -/)]
lemma two_pow_omega_LSeries.term_isMultiplicative (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term (fun n ↦ 2 ^ (ω n)) s (m * n) =
  LSeries.term (fun n ↦ 2 ^ (ω n)) s m * LSeries.term (fun n ↦ 2 ^ (ω n)) s n := by
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative two_pow_omega_isMultiplicative s mCn

@[blueprint
  "sumOnPrimePows"
  (title := "sumOnPrimePows")
  (statement := /--
    Shorthand for the sum of a function $f:\mathbb{N}\to\mathbb{C}$ at prime powers for a prime $p$.
  -/)]
noncomputable def sumOnPrimePows (f : ℕ → ℂ) (p : Primes) : ℂ := ∑' e, f (p ^ e)

@[blueprint
  "sumOnPrimePows_apply"
  (title := "sumOnPrimePows-apply")
  (statement := /--
    Helper lemma for sumOnPrimePows that rewrites the shorthand as its sum.
  -/)]
lemma sumOnPrimePows_apply (f : ℕ → ℂ) (p : Primes) :
  sumOnPrimePows f p = ∑' e, f (p ^ e) := by rfl

@[blueprint
  "two_pow_omega_tsum_prime_pow"
  (title := "two-pow-omega-tsum-prime-pow")
  (statement := /--
    For $1<\Re(s)$ and $p$ prime, we have that
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=\frac{1+p^{-s}}{1-p^{-s}}.$$
  -/)
  (proof := /--
    Note that $\omega(p^0)=0$ and $\omega(p^k)=1$ whenever $0<k$. Thus,
    $$\sum_{0\leq k}2^{\omega(p^k)}p^{-ks}=1+2p^{-s}+2p^{-2s}+\ldots.$$
    Now apply a geometric sum to the non-constant terms and simplify. We have the necessary
    convergence as $1<\Re(s)$.
  -/)]
lemma two_pow_omega_tsum_prime_pow {s : ℂ} (hs : 1 < s.re)
    (p : Primes) : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  have h_rw : sumOnPrimePows (LSeries.term (fun n ↦ 2 ^ (ω n)) s) p = 1 + ∑' e : ℕ, LSeries.term (fun n : ℕ => 2 ^ (ω n)) s (p.val ^ (e + 1)) := by
    rw [sumOnPrimePows_apply, Summable.tsum_eq_zero_add];
    · unfold LSeries.term
      simp [Nat.Prime.ne_zero p.prop]
    · have := LSeriesSummable_two_pow_omega hs;
      convert this.comp_injective (show Function.Injective (fun e : ℕ => p.val ^ e) from fun a b h => Nat.pow_right_injective p.prop.one_lt h) using 1
  have h_term_eval : ∀ e : ℕ, LSeries.term (fun n : ℕ => 2 ^ ω n) s (p.val ^ (e + 1)) = 2 * (p.val : ℂ) ^ (-(e + 1) * s) := by
    intro e
    simp only [neg_mul, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte]
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow p.prop, pow_one]
    · simp only [Complex.cpow_neg, div_eq_mul_inv, ← Complex.natCast_cpow_natCast_mul, cast_add, cast_one]
    · linarith
  have geo_series_rw : ∑' e : ℕ, (p.val : ℂ) ^ (-(e + 1) * s) = (p.val : ℂ) ^ (-s) / (1 - (p.val : ℂ) ^ (-s)) := by
    rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one]
    · rw [← tsum_mul_left]; congr; ext n; rw [← Complex.cpow_nat_mul]; ring_nf
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)]; ring_nf
    · rw [Complex.norm_cpow_of_ne_zero] <;> norm_num [p.2.ne_zero]
      exact lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt (mod_cast p.2.one_lt) (neg_lt_zero.mpr (by linarith))) (by norm_num)
  simp only [h_rw, h_term_eval, geo_series_rw, tsum_mul_left]
  rw [eq_div_iff, add_mul, one_mul, ← mul_div_assoc, div_mul_cancel₀]
  · ring_nf
  all_goals (exact Complex.one_sub_prime_cpow_ne_zero p.2 hs)

@[blueprint
  "Complex.one_add_prime_cpow_ne_zero"
  (title := "Complex.one-add-prime-cpow-ne-zero")
  (statement := /--
    For $1<\Re(s)$ and $p$ prime, we have that $1+p^{-s}\neq 0$. The naming convention is to mimic
    \begin{verbatim}
      Complex.one_sub_prime_cpow_ne_zero
    \end{verbatim}
  -/)
  (proof := /--
    Suppose for contradiction $1+p^{-s}=0$, then $|p^{-s}|=1$. However, this can not happen per
    \begin{verbatim}
      Complex.norm_prime_cpow_le_one_half
    \end{verbatim}
  -/)]
lemma Complex.one_add_prime_cpow_ne_zero {p : ℕ} (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    1 + (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have one_add_prime_cpow_h : ‖(p : ℂ) ^ (-s)‖ = 1 := by
    have := congr_arg norm (neg_eq_of_add_eq_zero_left h)
    simp only [norm_neg, one_mem, CStarRing.norm_of_mem_unitary] at this
    exact this
  linarith [Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs]

@[blueprint
  "two_pow_omega_LSeries_eulerProduct_tprod"
  (title := "two-pow-omega-LSeries-eulerProduct-tprod")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_tprod
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{two-pow-omega-LSeries.term-IsMultiplicative} and \ref{two-pow-omega-tsum-prime-pow}.
  -/)]
lemma two_pow_omega_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ 2 ^ (ω n)) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)) := by
  convert HasProd.tprod_eq ( EulerProduct.eulerProduct_hasProd (R := ℂ) ?_ ?_ _ _ ) |> Eq.symm using 1
  · apply tprod_congr
    simp only [← two_pow_omega_tsum_prime_pow hs, sumOnPrimePows_apply, implies_true]
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro m n mCn; exact two_pow_omega_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_two_pow_omega hs).norm using 1
  · unfold LSeries.term; simp only [↓reduceIte]

@[blueprint
  "two_pow_omega_LSeries_eulerProduct_hasProd"
  (title := "two-pow-omega-LSeries-eulerProduct-hasProd")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_hasProd
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{two-pow-omega-LSeries.term-IsMultiplicative} and \ref{two-pow-omega-tsum-prime-pow}.
  -/)]
lemma two_pow_omega_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s)) / (1 - ↑↑p ^ (-s))) (L (fun n ↦ (2 ^ ω n)) s) := by
  convert EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (2 ^ ω n)) s) using 1;
  · funext p; exact Eq.symm (two_pow_omega_tsum_prime_pow hs p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero,
      cardDistinctFactors_one, pow_zero, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact two_pow_omega_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_two_pow_omega hs).norm using 1

/--
  Zeta squared:
  `ζ(s)^2 = ζ(2*s) * ∑_n (2^omega(n)) n^(-s)`,
  where omega is the number of distinct prime factors.
-/
@[blueprint
  "zeta_pow_two"
  (title := "zeta pow two")
  (statement := /--
  $$\zeta(s)^2 =\zeta(2s) \sum_{n=1}^{\infty} 2^{\omega(n)} n^{-s}.$$
  \begin{verbatim}
    An expression for `ζ^2`, in IK (1.31).
  \end{verbatim}
  -/)
  (proof := /--
    Note that
    $$\zeta(s)^2=\prod_p\frac{1}{(1-p^{-s})^2}.$$
    Similarly
    $$\zeta(2s)=\prod_p\frac{1}{(1-p^{-2s})}.$$
    Applying Theorems \ref{two-pow-omega-LSeries-eulerProduct-tprod} and \ref{two-pow-omega-LSeries-eulerProduct-hasProd} we have
    $$\sum_{1\leq n}2^{\omega(n)}n^{-s}=\prod_p\frac{1+p^{-s}}{1-p^{-s}}.$$
    Thus
    $$\zeta(2s)\left(\sum_{1\leq n}2^{\omega(n)}n^{-s}\right)=\prod_p\frac{1+p^{-s}}{(1-p^{-s})(1-p^{-2s})}=\prod_p\frac{1}{(1-p^{-s})^2}$$
    by the difference of squares. This is exactly the Euler product for $\zeta(s)^2$ mentioned earlier.
  -/)]
lemma zeta_pow_two (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s ^ 2 =
    riemannZeta (2 * s) * LSeries (fun n ↦ 2 ^ (ω n)) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [sq, ← riemannZeta_eulerProduct_tprod hs, ← Multipliable.tprod_mul mulable mulable,
    mul_comm, ← riemannZeta_eulerProduct_tprod hs',
    two_pow_omega_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨LSeries (fun n ↦ 2 ^ (ω n)) s, two_pow_omega_LSeries_eulerProduct_hasProd s hs⟩
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩

@[blueprint
  "LSeriesSummable_moebius_sq"
  (title := "LSeriesSummable-moebius-sq")
  (statement := /--
    The $L$-series with coefficients given by $\mu^2(n)$ converges on the region $1<\Re(s)$.
  -/)
  (proof := /--
    This follows by comparison test against the Riemann zeta function.
  -/)]
lemma LSeriesSummable_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (μ n) ^ 2) s := by
  have hgf : ∀ (n : ℕ), ‖LSeries.term (fun n ↦ (μ n) ^ 2) s n‖ ≤ ‖LSeries.term (fun n ↦ 1) s n‖ := by
    intro n
    by_cases hn : n = 0
    · simp only [LSeries.term, hn, ↓reduceIte, norm_zero, Std.le_refl]
    · simp only [LSeries.term, hn, ↓reduceIte, Complex.norm_div, norm_pow]
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      simp only [Complex.norm_intCast, sq_abs, one_mem, CStarRing.norm_of_mem_unitary,
        sq_le_one_iff_abs_le_one]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have zetaSummable : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  rw [LSeriesSummable, ← summable_norm_iff] at zetaSummable;
  apply LSeriesSummable.of_norm_le_norm hgf zetaSummable

@[blueprint
  "powOfMultiplicative_isMultiplicative"
  (title := "powOfMultiplicative-isMultiplicative")
  (statement := /--
    If $f$ is a multiplicative function, then so to is $n\mapsto f(n)^k$ for any $k\in\mathbb{N}$.
  -/)
  (proof := /--
    Note that $f(mn)^k=(f(m)f(n))^k=(f(m)^k)(f(n)^k)$.
  -/)]
lemma powOfMultiplicative_isMultiplicative {R : Type u_1} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (k : ℕ) :
    (toArithmeticFunction (fun n ↦ (f n) ^ k)).IsMultiplicative := by
  simp only [IsMultiplicative, toArithmeticFunction, coe_mk, one_ne_zero, ↓reduceIte, _root_.mul_eq_zero, mul_ite, mul_zero, ite_mul, zero_mul, hf.1, one_pow, true_and]
  intro m n mCn
  by_cases m_eq_zero : m = 0 <;> simp only [m_eq_zero, true_or, ↓reduceIte, ite_self]
  by_cases n_eq_zero : n = 0 <;> simp only [n_eq_zero, or_true, ↓reduceIte]
  simp only [or_self, ↓reduceIte, hf.2 mCn, mul_pow]

@[blueprint
  "moebius_sq_LSeries.term_isMultiplicative"
  (title := "moebius-sq-LSeries.term-isMultiplicative")
  (statement := /--
    We have that $n\mapsto \mu^2(n)/n^{-s}$ is a multiplicative function.
  -/)
  (proof := /--
    Follows as a consequence of Lemma \ref{LSeries.term-isMultiplicative-if-fun-isMultiplicative}
    and \ref{moebius-sq-isMultiplicative}.
  -/)]
lemma moebius_sq_LSeries.term_isMultiplicative (s : ℂ) {m n : ℕ} (mCn : m.Coprime n) :
    LSeries.term (fun n ↦ (μ n) ^ 2) s (m * n) =
  LSeries.term (fun n ↦ (μ n) ^ 2) s m * LSeries.term (fun n ↦ (μ n) ^ 2) s n := by
  simp only [← intCoe_apply]
  exact LSeries.term_isMultiplicative_if_fun_isMultiplicative (powOfMultiplicative_isMultiplicative (ArithmeticFunction.IsMultiplicative.intCast isMultiplicative_moebius) 2) s mCn

@[blueprint
  "moebius_sq_tsum_prime_pow"
  (title := "moebius-sq-tsum-prime-pow")
  (statement := /--
    For $p$ prime, we have that
    $$\sum_{0\leq k}\mu^2(p^k)p^{-ks}=1+p^{-s}.$$
  -/)
  (proof := /--
    Note that $\mu^2(p^0)=1$ and $\mu^2(p^1)=1$ but $\mu^2(p^k)=0$ whenever $1<k$. Thus,
    $$\sum_{0\leq k}\mu^2(p^k)p^{-ks}=1+p^{-s}.$$
  -/)]
lemma moebius_sq_tsum_prime_pow {s : ℂ} (p : Nat.Primes) :
    sumOnPrimePows (LSeries.term (fun n ↦ (μ n) ^ 2) s) p = (1 + (p : ℂ) ^ (-s)) := by
  have h_rw : 1 + ↑↑p ^ (-s) = ∑' (e : ℕ), (if e ≤ 1 then 1 else 0) / ((p : ℂ) ^ e) ^ s := by
    rw [tsum_eq_sum (s := {0, 1})]
    · simp only [mem_singleton, zero_ne_one, not_false_eq_true, sum_insert, _root_.zero_le,
        ↓reduceIte, pow_zero, Complex.one_cpow, ne_eq, one_ne_zero, div_self, sum_singleton,
        le_refl, pow_one, one_div, Complex.cpow_neg]
    · intro e he; simp at he
      simp [show ¬e ≤ 1 by omega]
  simp only [sumOnPrimePows_apply, LSeries.term, Nat.pow_eq_zero, ne_eq, cast_pow, Nat.Prime.ne_zero p.prop, false_and, ↓reduceIte, ← Int.cast_pow, moebius_sq, h_rw]
  apply tsum_congr
  intro e
  congr 1
  by_cases h : (e ≤ 1) <;> simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, h, ↓reduceIte, ite_eq_left_iff,
    zero_ne_one, imp_false, Decidable.not_not, ite_eq_right_iff, one_ne_zero, imp_false]
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    interval_cases e
    · simp only [zero_mul, zero_le, implies_true]
    · simp only [one_mul, ← Nat.squarefree_iff_factorization_le_one (Nat.Prime.ne_zero p.prop)]
      exact (Nat.squarefree_and_prime_pow_iff_prime.mpr p.prop).1
  · rw [Nat.squarefree_iff_factorization_le_one (pow_ne_zero _ (Nat.Prime.ne_zero p.prop))]
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, not_forall, not_le]
    use p
    simp only [Nat.Prime.factorization_self p.prop, mul_one]
    exact Nat.lt_of_not_le h

@[blueprint
  "moebius_sq_LSeries_eulerProduct_tprod"
  (title := "moebius-sq-LSeries-eulerProduct-tprod")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}\mu^2(n)n^{-s}=\prod_p(1+p^{-s}).$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_tprod
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{moebius-sq-LSeries.term-IsMultiplicative} and \ref{moebius-sq-tsum-prime-pow}.
  -/)]
lemma moebius_sq_LSeries_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n ↦ (μ n) ^ 2) s = ∏' (p : Primes), (1 + (p : ℂ) ^ (-s)) := by
  convert (EulerProduct.eulerProduct_hasProd (R := ℂ) ?_ ?_ _ _).tprod_eq.symm using 1
  · apply tprod_congr
    simp only [← moebius_sq_tsum_prime_pow, sumOnPrimePows_apply, implies_true]
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro m n mCn; exact moebius_sq_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_moebius_sq hs).norm using 1
  · unfold LSeries.term; simp only [↓reduceIte]

@[blueprint
  "moebius_sq_LSeries_eulerProduct_hasProd"
  (title := "moebius-sq-LSeries-eulerProduct-hasProd")
  (statement := /--
    For $1<\Re(s)$ we have that
    $$\sum_{1\leq n}\mu^2(n)n^{-s}=\prod_p(1+p^{-s}).$$
    The naming convention here is designed to match
    \begin{verbatim}
      riemannZeta_eulerProduct_hasProd
    \end{verbatim}
  -/)
  (proof := /--
    Immediately follows from Lemmas \ref{moebius-sq-LSeries.term-IsMultiplicative} and \ref{moebius-sq-tsum-prime-pow}.
  -/)]
lemma moebius_sq_LSeries_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun (p : Primes) ↦ (1 + ↑↑p ^ (-s))) (L (fun n ↦ (μ n) ^ 2) s) := by
  convert EulerProduct.eulerProduct_hasProd _ _ _ (LSeries.term_zero (fun n ↦ (μ n) ^ 2) s) using 1;
  · funext p; exact Eq.symm (moebius_sq_tsum_prime_pow p)
  · simp only [ne_eq, one_ne_zero, not_false_eq_true, LSeries.term_of_ne_zero, isUnit_iff_eq_one,
      IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero,
      Int.cast_one, one_pow, cast_one, Complex.one_cpow, div_self]
  · intro _ _ mCn; exact moebius_sq_LSeries.term_isMultiplicative s mCn
  · convert (LSeriesSummable_moebius_sq hs).norm using 1

-- **Zulip question** Do we want `|μ n| = μ^2 (n)` to be a standalone function? It is the indicator
-- of `n` being squarefree.

/--
Zeta alt:
`ζ(s) = ζ(2*s) * ∑_n (|μ(n)|) n^(-s)`,
where omega is the number of distinct prime factors. -/
@[blueprint
  "zeta_alt"
  (title := "zeta alt")
  (statement := /--
  $$\zeta(s) =\zeta(2s) \sum_{n=1}^{\infty}\mu^2(n)n^{-s}.$$
  \begin{verbatim}
    An expression for `ζ`, in IK (1.32).
  \end{verbatim}
  -/)
  (proof := /--
  The series $\sum_{n=1}^{\infty}\mu^2(n)n^{-s}$ has Euler product $\prod_{p} (1 + p^{-s})$. On the other hand, $\zeta(2s)=\prod_p (1 - p^{-2s})^{-1}$. The product of these two Euler products is $\prod_p (1 - p^{-s})^{-1} = \zeta(s)$, which gives the desired formula.
  -/)]
lemma zeta_alt (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s =
    riemannZeta (2 * s) * LSeries (fun (n : ℕ) ↦ (μ n : ℂ) ^ 2) s := by
  have hs' : 1 < (2 * s).re := by rw [Complex.mul_re]; norm_num; linarith
  have mulable := (riemannZeta_eulerProduct_hasProd hs).multipliable
  rw [← riemannZeta_eulerProduct_tprod hs, ← riemannZeta_eulerProduct_tprod hs',
    moebius_sq_LSeries_eulerProduct_tprod s hs, ← Multipliable.tprod_mul, tprod_congr]
  · intro p
    have hsub := Complex.one_sub_prime_cpow_ne_zero p.2 hs
    have hsq : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
      rw [show 1 - ((p : ℂ) ^ (-s)) ^ 2 = (1 - (p : ℂ) ^ (-s)) * (1 + (p : ℂ) ^ (-s)) from by ring]
      exact mul_ne_zero hsub (Complex.one_add_prime_cpow_ne_zero p.2 hs)
    rw [show (-(2 * s) : ℂ) = -s + -s from by ring, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.2.ne_zero)]
    field_simp
    ring
  · exact ⟨riemannZeta (2 * s), riemannZeta_eulerProduct_hasProd hs'⟩
  · exact ⟨LSeries (fun n ↦ (μ n) ^ 2) s, moebius_sq_LSeries_eulerProduct_hasProd s hs⟩

@[blueprint
  "pow_divisors_mul"
  (title := "pow-divisors-mul")
  (statement := /--
    Let $m$ and $n$ be coprime natural numbers, with a fixed power $k$. The divisors of $mn$ that
    can be expressed as perfect $k$-powers are exactly the product of the divisors of $m$ and $n$
    that can be expressed as perfect $k$-powers.
  -/)
  (proof := /--
    Since $m$ and $n$ are coprime, they share no common prime factors. Therefore, any divisor of
    $mn$ can be uniquely expressed as a product of a divisor of $m$ and a divisor of $n$. The
    condition that a divisor is a perfect $k$-power can be checked separately for the divisors of
    $m$ and $n$. Thus, the divisors of $mn$ that are perfect $k$-powers correspond exactly to the
    products of divisors of $m$ and $n$ that are perfect $k$-powers.
  -/)]
lemma pow_divisors_mul {m n k : ℕ} (hmn : Nat.Coprime m n) :
    (m * n).divisors.filter (fun x => x ^ k ∣ m * n) =
    (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)).image
      (fun p => p.1 * p.2) := by
  ext x
  simp only [mem_image, mem_product, mem_filter, mem_divisors, ne_eq, Prod.exists]
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ a * b = x := Nat.dvd_mul.mp hx.1.1
    simp only [mul_eq_zero, not_or, ← hab, mul_pow] at hx
    exact ⟨a, b, ⟨⟨⟨⟨ha, hx.1.2.1⟩, (hmn.coprime_dvd_left ha).pow_left k |>.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx.2)⟩,
      ⟨⟨hb, hx.1.2.2⟩, (hmn.symm.coprime_dvd_left hb).pow_left k |>.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx.2)⟩⟩, hab⟩⟩
  · intro ⟨a, b, hab⟩
    rw[← hab.2, mul_pow]
    exact ⟨⟨Nat.mul_dvd_mul hab.1.1.1.1 hab.1.2.1.1, Nat.mul_ne_zero_iff.mpr ⟨hab.1.1.1.2, hab.1.2.1.2⟩⟩, mul_dvd_mul hab.1.1.2 hab.1.2.2⟩

@[blueprint
  "divisors_mul_injective"
  (title := "divisors-mul-injective")
  (statement := /--
    Let $m$ and $n$ be coprime natural numbers. The function $(a,b) \mapsto ab$ is injective on the
    product of the divisors of $m$ and $n$.
    \begin{verbatim}
    Upstreamed to mathlib via PR #36495.
    \end{verbatim}
  -/)
  (proof := /--
    Since $m$ and $n$ are coprime, any element in the product of their divisors can be uniquely
    expressed as a product of an element from each set. The injectivity follows from the uniqueness
    of this decomposition.
  -/)]
lemma divisors_mul_injective {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (m.divisors ×ˢ n.divisors) := by
  /-- comes from mathlib PR #36495 -/
  sorry

@[blueprint
  "pow_divisors_mul_injective"
  (title := "pow-divisors-mul-injective")
  (statement := /--
    Let $m$ and $n$ be coprime natural numbers, with a fixed power $k$. The function
    $(a,b) \mapsto ab$ is injective on the product of the divisors of $m$ and $n$ that can be
    expressed as perfect $k$-powers.
  -/)
  (proof := /--
    This follows from the injectivity of the function on the product of all divisors, as shown in
    the previous lemma. Since we are restricting to a subset of the divisors, the injectivity still
    holds.
  -/)]
lemma pow_divisors_mul_injective {m n k : ℕ} (hmn : Nat.Coprime m n) :
    Set.InjOn (fun (p : ℕ × ℕ) => p.1 * p.2) (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)) := by
  apply Set.InjOn.mono _ (divisors_mul_injective hmn)
  intro ⟨_, _⟩ hab
  simp only [Finset.coe_filter, Set.mem_prod, Set.mem_setOf_eq, Finset.mem_coe] at hab ⊢
  exact ⟨hab.1.1, hab.2.1⟩

@[blueprint
  "sum_moebius_sq_divisors"
  (title := "sum-moebius-sq-divisors")
  (statement := /-- The function $n \mapsto \sum_{d^2|n} \mu(d)$. -/)]
noncomputable def sum_moebius_sq_divisors : ArithmeticFunction ℤ where
  toFun := fun n ↦ ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d
  map_zero' := by simp

@[blueprint
  "sum_moebius_sq_divisors_apply"
  (title := "sum-moebius-sq-divisors-apply")
  (statement := /-- A simple helper lemma for the above definition. -/)]
lemma sum_moebius_sq_divisors_apply (n : ℕ) :
  sum_moebius_sq_divisors n = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by rfl

@[blueprint
  "sum_moebius_sq_divisors_IsMultiplicative"
  (title := "sum-moebius-sq-divisors-is-multiplicative")
  (statement := /-- The function $n \mapsto \sum_{d^2|n} \mu(d)$ is multiplicative. -/)
  (proof := /--
    We will show that for coprime $m$ and $n$, we have
    $\sum_{d^2|mn} \mu(d) = \sum_{d^2|m} \mu(d) \cdot \sum_{d^2|n} \mu(d)$. This follows from the
    fact that the divisors of $mn$ that are perfect squares correspond to the products of divisors
    of $m$ and $n$ that are perfect squares, as shown in the previous lemmas. The multiplicativity
    of the Möbius function then allows us to factor the sum accordingly.
  -/)]
lemma sum_moebius_sq_divisors_IsMultiplicative : sum_moebius_sq_divisors.IsMultiplicative := by
  unfold sum_moebius_sq_divisors
  refine ⟨by simp only [sum_filter, coe_mk, divisors_one, dvd_one, pow_eq_one_iff,
    OfNat.ofNat_ne_zero, or_false, sum_ite_eq', mem_singleton, ↓reduceIte, isUnit_iff_eq_one,
    IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one, pow_zero], ?_⟩
  intro m n mCn
  simp only [coe_mk, pow_divisors_mul mCn, Finset.sum_product,
    Finset.sum_image (fun x hx y hy => pow_divisors_mul_injective (k := 2) mCn
      (Finset.coe_product _ _ ▸ Finset.mem_coe.mpr hx)
      (Finset.coe_product _ _ ▸ Finset.mem_coe.mpr hy))]
  trans (∑ i ∈ m.divisors.filter (fun x => x ^ 2 ∣ m), ∑ j ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ i * μ j)
  · apply Finset.sum_congr rfl
    intro _ hi
    apply Finset.sum_congr rfl
    intro _ hj
    exact isMultiplicative_moebius.map_mul_of_coprime
      (mCn.coprime_dvd_left (Nat.dvd_of_mem_divisors (Finset.filter_subset _ _ hi))
        |>.coprime_dvd_right (Nat.dvd_of_mem_divisors (Finset.filter_subset _ _ hj)))
  · rw [← Finset.sum_mul_sum]

@[blueprint
  "sum_moebius_sq_divisors_apply_prime_pow"
  (title := "sum-moebius-sq-divisors-apply-prime-pow")
  (statement := /-- Applied at prime powers, sum-moebius-sq-divisors coincides with $\mu^2$. -/)
  (proof := /--
    For a prime power $p^k$, note that if $k\leq 1$ then the only square divisor is $1$, so the sum
    evaluates as $\mu(1)=1$. If $k\geq 2$, then $1$ and $p^2$ are square divisors of $p^k$. Thus,
    the sum evaluates as $\mu(1)+\mu(p)+\ldots$ where the remaining terms are moebius of higher
    powers (if necessary). Since $\mu(p)=-1$ and $\mu$ of higher powers of $p$ is zero, this is
    $0$. This agrees with $\mu(p^k)^2$, which is simply an indicator function for $k\leq 1$ (i.e.
    $p^k$ is squarefree).
  -/)]
lemma sum_moebius_sq_divisors_apply_prime_pow {p k : ℕ} (hp : Nat.Prime p) :
  sum_moebius_sq_divisors (p ^ k) = (μ (p ^ k)) ^ 2 := by
  have h_filter : ((Nat.divisors (p ^ k)).filter (fun x => x ^ 2 ∣ p ^ k)) = Finset.image (fun j => p ^ j) (Finset.range (k / 2 + 1)) := by
    ext; simp only [Nat.divisors_prime_pow hp, mem_filter, mem_map, mem_range, Order.lt_add_one_iff, Function.Embedding.coeFn_mk, mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨a, Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by
        rw [← pow_mul] at h
        exact Nat.le_of_not_lt fun ha' => absurd (Nat.le_of_dvd (pow_pos hp.pos _) h)
          (not_le_of_gt (pow_lt_pow_right₀ hp.one_lt ha')), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, by omega, rfl⟩, by rw [← pow_mul]; exact pow_dvd_pow _ (by omega)⟩
  simp only [moebius_sq, sum_moebius_sq_divisors_apply, h_filter]
  rw [Finset.sum_image <| by intros a ha b hb hab; exact Nat.pow_right_injective hp.two_le hab, Finset.sum_range_succ']
  split_ifs with h
  · have hk : k / 2 = 0 := by
      rw [Nat.div_eq_zero_iff, or_iff_right (two_ne_zero)]
      by_contra hk
      exact absurd h (by rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; exact not_and_of_not_right _ (by linarith))
    simp [hk]
  · simp only [pow_zero, isUnit_iff_eq_one, IsUnit.squarefree, moebius_apply_of_squarefree, Int.reduceNeg, cardFactors_one]
    rcases k with _ | _ | _
    · simp at ⊢ h
    · simp [hp.squarefree] at ⊢ h
    · simp_all +decide [ArithmeticFunction.moebius_apply_prime_pow]

/-- I-K (1.33): `μ^2(n) = ∑ d^2|n μ(d)`. -/
@[blueprint
  "moebius_sq_eq"
  (title := "moebius-sq-eq")
  (statement := /-- I-K (1.33): $\mu^2(n) = \sum_{d^2|n} \mu(d)$. -/)
  (proof := /-- Apply the previous two lemmas. -/)]
lemma moebius_sq_eq (n : ℕ) : (μ n) ^ 2 = ∑ d ∈ n.divisors.filter (fun x => x ^ 2 ∣ n), μ d := by
  by_cases n_zero : n = 0
  · simp [n_zero]
  · rw[← sum_moebius_sq_divisors_apply, IsMultiplicative.multiplicative_factorization sum_moebius_sq_divisors sum_moebius_sq_divisors_IsMultiplicative n_zero]
    have hpf : ∀ p ∈ n.factorization.support, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    simp only [Finset.prod_pow, Finsupp.prod, Nat.support_factorization, Finset.prod_congr rfl (fun x hx =>
      sum_moebius_sq_divisors_apply_prime_pow ((Nat.support_factorization n ▸ hpf) x hx))]
    congr; exact IsMultiplicative.multiplicative_factorization μ isMultiplicative_moebius n_zero

/--
Liouville function:
`λ(n) = (-1)^Ω(n)`. -/
@[blueprint
  "liouville"
  (title := "liouville")
  (statement := /-- Liouville function: $\lambda(n) = (-1)^{\Omega(n)}$. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ is the total number of prime factors of $n$ counted with multiplicity. This means that for each prime factor of $n$, we contribute a factor of $-1$ to the product, and the overall sign of $\lambda(n)$ depends on whether the total number of prime factors is even or odd. Thus, we have $\lambda(n) = (-1)^{\Omega(n)}$ by definition.
  -/)]
def liouville : ArithmeticFunction ℤ :=
  toArithmeticFunction (fun n => (-1 : ℤ) ^ Ω n)

-- **NOTE:** `def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
--  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b` exists in the `SelbergBound` file.

/--
Define Complete Multiplicativity for an arithmetic function. -/
@[blueprint
  "IsCompletelyMultiplicative"
  (title := "IsCompletelyMultiplicative")
  (statement := /-- Define Complete Multiplicativity for an arithmetic function. -/)]
def IsCompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

/-- A function that is completely multiplicative is also multiplicative. -/
@[blueprint
  "IsCompletelyMultiplicative.isMultiplicative"
  (title := "IsCompletelyMultiplicative.isMultiplicative")
  (statement := /-- A function that is completely multiplicative is also multiplicative. -/)
  (proof := /--
  Let $f$ be a completely multiplicative function. To show that $f$ is multiplicative, we need to verify that $f(1) = 1$ and that $f(ab) = f(a)f(b)$ for all coprime natural numbers $a$ and $b$. Since $f$ is completely multiplicative, we have $f(1) = 1$ by definition. For coprime $a$ and $b$, we can write $ab$ as a product of prime factors, and since $f$ is completely multiplicative, it will factor as the product of the values of $f$ at those prime factors. This means that $f(ab) = f(a)f(b)$ for coprime $a$ and $b$, which shows that $f$ is multiplicative.
  -/)]
lemma IsCompletelyMultiplicative.isMultiplicative {f : ArithmeticFunction ℝ} (hf : IsCompletelyMultiplicative f) : f.IsMultiplicative := by
  exact ⟨hf.1, fun {m n} _ => hf.2 m n⟩

/--
The Liouville function is completely multiplicative. -/
@[blueprint
  "isCompletelyMultiplicative_liouville"
  (title := "isCompletelyMultiplicative liouville")
  (statement := /-- The Liouville function is completely multiplicative. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ counts the total number of prime factors of $n$ with multiplicity. To show that $\lambda$ is completely multiplicative, we need to verify that $\lambda(1) = 1$ and that $\lambda(ab) = \lambda(a)\lambda(b)$ for all natural numbers $a$ and $b$.
  -/)]
lemma isCompletelyMultiplicative_liouville : IsCompletelyMultiplicative (liouville : ArithmeticFunction ℤ) := by
  sorry

/--
The Dirichlet series of the Liouville function is `ζ(2s)/ζ(s)`. -/
@[blueprint
  "LSeries_liouville_eq"
  (title := "LSeries liouville eq")
  (statement := /-- The Dirichlet series of the Liouville function is $\zeta(2s)/\zeta(s)$. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is multiplicative, and its value at prime powers is given by $\lambda(p^k) = (-1)^k$. The Dirichlet series of $\lambda$ can be expressed as an Euler product over primes:
\[
L(\lambda, s) = \prod_{p} \left(1 + \lambda(p)p^{-s} + \lambda(p^2)p^{-2s} + \ldots\right) = \prod_{p} \left(1 - p^{-s}\right)^{-1} \left(1 - p^{-2s}\right) = \frac{\zeta(2s)}{\zeta(s)}.
\]
  -/)]
lemma LSeries_liouville_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(liouville : ArithmeticFunction ℤ)) s = riemannZeta (2 * s) / riemannZeta s := by
  sorry

/-- `liouville` agrees with `moebius` on square-free numbers -/
@[blueprint
  "liouville_eq_moebius_on_squarefree"
  (title := "liouville eq moebius on squarefree")
  (statement := /-- The Liouville function agrees with the Möbius function on square-free numbers. -/)
  (proof := /--
  The Liouville function $\lambda(n)$ is defined as $(-1)^{\Omega(n)}$, where $\Omega(n)$ counts the total number of prime factors of $n$ with multiplicity. The Möbius function $\mu(n)$ is defined as $0$ if $n$ has a squared prime factor, and otherwise it is $(-1)^{\omega(n)}$, where $\omega(n)$ counts the number of distinct prime factors of $n$. For square-free numbers, we have $\Omega(n) = \omega(n)$, since there are no repeated prime factors. Therefore, for square-free numbers, we have $\lambda(n) = (-1)^{\omega(n)} = \mu(n)$, which shows that the Liouville function agrees with the Möbius function on square-free numbers.
  -/)]
lemma liouville_eq_moebius_on_squarefree (n : ℕ) (hn : Squarefree n) : liouville n = μ n := by
  sorry

/-- Euler totient series: `∑ φ(n) n^-s = ζ(s-1)/ζ(s)`. -/
@[blueprint
  "LSeries_totient_eq"
  (title := "LSeries totient eq")
  (statement := /-- Euler totient series: $\sum_{n=1}^{\infty} \varphi(n) n^{-s} = \zeta(s-1)/\zeta(s)$.
  \begin{verbatim}
  This is IK (1.35).
  \end{verbatim}
   -/)
  (proof := /--
  The Euler totient function $\varphi(n)$ counts the positive integers up to $n$ that are relatively prime to $n$. It is a multiplicative function, and its value at prime powers is given by $\varphi(p^k) = p^k - p^{k-1}$. The Dirichlet series of $\varphi$ can be expressed as an Euler product over primes:
\[
L(\varphi, s) = \prod_{p} \left(1 + \varphi(p)p^{-s} + \varphi(p^2)p^{-2s} + \ldots\right) = \prod_{p} \left(1 - p^{-s  +1}\right)^{-1} \left(1 - p^{-s}\right) = \frac{\zeta(s-1)}{\zeta(s)}.
\]
  -/)]
lemma LSeries_totient_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗totient) s = riemannZeta (s - 1) / riemannZeta s := by
  sorry


end ArithmeticFunction
