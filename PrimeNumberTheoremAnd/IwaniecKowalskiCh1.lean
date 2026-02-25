import Architect
import Mathlib

open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

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
  (statement := /-- Additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for coprime $m$, $n$. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Coprime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (statement := /-- Completely additive arithmetic function: satisfies $f(mn) = f(m) + f(n)$ for all $m, n \ne 0$. -/)]
def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive.isAdditive"
  (statement := /-- A completely additive function is additive. -/)]
lemma IsCompletelyAdditive.isAdditive [AddZeroClass R] {f : ArithmeticFunction R}
    (hf : IsCompletelyAdditive f) : IsAdditive f :=
  fun hm hn _ ↦ hf hm hn

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

@[blueprint
  "unique_divisor_decomposition"
  (statement := /-- If $a$ and $b$ are coprime, then any divisor $d$ of $ab$ can be uniquely expressed as a product of a divisor of $a$ and a divisor of $b$. -/)
  (proof := /--
  Let $a$ and $b$ be coprime natural numbers, and let $d$ be a divisor of $ab$. Since $a$ and $b$ are coprime, we can use the fact that the divisors of $ab$ correspond to pairs of divisors of $a$ and $b$. Specifically, we can express $d$ as $d = d_a \cdot d_b$, where $d_a$ divides $a$ and $d_b$ divides $b$. The uniqueness of this decomposition follows from the coprimality of $a$ and $b$, which ensures that the divisors of $a$ and $b$ do not share any common factors. Therefore, there is a one-to-one correspondence between the divisors of $ab$ and the pairs of divisors of $a$ and $b$, which guarantees the uniqueness of the decomposition.
  -/)]
lemma unique_divisor_decomposition {a b d : ℕ} (hab : Coprime a b) (hd : d ∣ a * b) :
    ∃! p : ℕ × ℕ, p.1 ∣ a ∧ p.2 ∣ b ∧ p.1 * p.2 = d := by
  -- Existence
  obtain ⟨d₁, d₂, h1, h2, h3⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  refine ⟨(d₁, d₂), ⟨h1, h2, h3.symm⟩, ?_⟩
  -- Uniqueness
  rintro ⟨q₁, q₂⟩ ⟨hq1, hq2, hq3⟩
  have h_eq : d₁ * d₂ = q₁ * q₂ := by rw [← h3, ← hq3]
  apply Prod.ext
  -- d₁ = q₁
  · apply dvd_antisymm
    -- q₁ | d₁
    · have : Coprime q₁ d₂ := (hab.coprime_dvd_left hq1).coprime_dvd_right h2
      exact this.dvd_of_dvd_mul_right (by rw [h_eq]; apply dvd_mul_right)
    -- d₁ | q₁
    · have : Coprime d₁ q₂ := (hab.coprime_dvd_left h1).coprime_dvd_right hq2
      exact this.dvd_of_dvd_mul_right (by rw [← h_eq]; apply dvd_mul_right)
  -- d₂ = q₂
  · apply dvd_antisymm
    -- q₂ ∣ d₂
    · have : Coprime q₂ d₁ := (hab.symm.coprime_dvd_left hq2).coprime_dvd_right h1
      exact this.dvd_of_dvd_mul_left (by rw [h_eq]; apply dvd_mul_left)
    -- d₂ ∣ q₂
    · have : Coprime d₂ q₁ := (hab.symm.coprime_dvd_left h2).coprime_dvd_right hq1
      exact this.dvd_of_dvd_mul_left (by rw [← h_eq]; apply dvd_mul_left)

/-- If `f` is a multiplicative arithmetic function, then for coprime `a` and `b`, we have $\sum_{d | ab} f(d) = (\sum_{d | a} f(d)) \cdot (\sum_{d | b} f(d))$. -/
@[blueprint
  "sum_divisors_mul_of_coprime"
  (statement := /-- If $f$ is a multiplicative arithmetic function, then for coprime, nonzero $a$ and $b$, we have that
  $\sum_{d | ab} f(d) = (\sum_{d | a} f(d)) \cdot (\sum_{d | b} f(d))$. -/)
  (proof := /--
  Since $f$ is multiplicative, we can express the sum over divisors of $ab$ in terms of the sums over divisors of $a$ and $b$. The key idea is to use the fact that the divisors of $ab$ can be expressed as products of divisors of $a$ and divisors of $b$, due to the coprimality condition. Specifically, each divisor $d$ of $ab$ can be uniquely written as $d = d_a * d_b$, where $d_a$ divides $a$ and $d_b$ divides $b$. Therefore, we can rewrite the sum as a double sum over the divisors of $a$ and $b$, which factorizes into the product of the two separate sums.
  -/)]
theorem sum_divisors_mul_of_coprime {R : Type*} [CommRing R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {a b : ℕ} (hab : Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ d ∈ (a * b).divisors, f d = (∑ d ∈ a.divisors, f d) * (∑ d ∈ b.divisors, f d) := by
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
-- (ab).divisors = Image
  have h_image : (a * b).divisors = (a.divisors ×ˢ b.divisors).image (g) := by
    ext d
    simp only [Finset.mem_image, Finset.mem_product, Nat.mem_divisors]
    constructor
    · rintro ⟨hd_dvd, _⟩
      obtain ⟨p, ⟨hp1, hp2, rfl⟩, _⟩ := unique_divisor_decomposition hab hd_dvd
      exact ⟨p, ⟨⟨hp1, ha⟩, ⟨hp2, hb⟩⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp1, _⟩, ⟨hp2, _⟩⟩, rfl⟩
      exact ⟨mul_dvd_mul hp1 hp2, mul_ne_zero ha hb⟩
  -- Injectivity
  have h_inj : Set.InjOn g (↑(a.divisors ×ˢ b.divisors)) := by
    intro p1 hp1 p2 hp2 h_eq
    simp only [Finset.mem_coe, Finset.mem_product] at hp1 hp2
    have hd : p1.1 * p1.2 ∣ a * b :=
      mul_dvd_mul (Nat.dvd_of_mem_divisors hp1.1) (Nat.dvd_of_mem_divisors hp1.2)
    obtain ⟨p, _, h_unique_imp⟩ := unique_divisor_decomposition hab hd
    rw [h_unique_imp p1 ⟨Nat.dvd_of_mem_divisors hp1.1, Nat.dvd_of_mem_divisors hp1.2, rfl⟩,
        h_unique_imp p2 ⟨Nat.dvd_of_mem_divisors hp2.1, Nat.dvd_of_mem_divisors hp2.2, h_eq.symm⟩]
  -- Change summation
  rw [h_image, sum_image h_inj, Finset.sum_product,sum_mul_sum]
  -- Prove equality of terms
-- Prove equality of terms
  refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ ?_
  exact hf.map_mul_of_coprime <|
    Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_divisors hy) <|
      Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors hx) hab

/-- If `g` is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p | n} (1 - g(p))$. -/
@[blueprint
  "sum_moebius_pmul_eq_prod_one_sub"
  (statement := /-- If $g$ is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p | n} (1 - g(p))$. -/)
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
  (statement := /-- $d_k$ is the $k$-fold divisor function: the number of ways to write $n$ as an ordered
    product of $k$ natural numbers. Equivalently, the Dirichlet convolution of $\zeta$ with
    itself $k$ times.-/)]
def d (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

/-- `d 0` is the multiplicative identity (indicator at 1). -/
@[blueprint
  "d_zero"
  (statement := /-- $d_0$ is the multiplicative identity (indicator at 1). -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 0$, this corresponds to the empty convolution, which is defined to be the multiplicative identity in the algebra of arithmetic functions. The multiplicative identity is the function that takes the value $1$ at $n=1$ and $0$ elsewhere, which can be expressed as $\zeta^0$.
  -/)]
theorem d_zero : d 0 = 1 := pow_zero zeta

/-- `d 1` is `ζ`. -/
@[blueprint
  "d_one"
  (statement := /-- $d_1$ is $\zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 1$, this means we are taking the convolution of $\zeta$ with itself once, which simply gives us $\zeta$. Therefore, $d_1 = \zeta^1 = \zeta$.
  -/)]
theorem d_one : d 1 = zeta := pow_one zeta

/-- `d 2` is the classical divisor count function `τ`. -/
@[blueprint
  "d_two"
  (statement := /-- $d_2$ is the classical divisor count function $\tau$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 2$, this means we are taking the convolution of $\zeta$ with itself twice, which gives us $\zeta * \zeta$. From the earlier theorem, we know that $\zeta * \zeta = \tau$, where $\tau$ is the divisor count function. Therefore, $d_2 = \zeta^2 = \tau$.
  -/)]
theorem d_two : d 2 = τ := by simp [d, sq, zeta_mul_zeta]

/-- Recurrence: `d_(k+1) = d_k * ζ`. -/
@[blueprint
  "d_succ"
  (statement := /-- Recurrence: $d_{k+1} = d_k * \zeta$. -/)
  (proof := /--
  By definition, $d_k$ is the $k$-fold Dirichlet convolution of $\zeta$. Therefore, $d_{k + 1}$ is the $(k + 1)$-fold convolution of $\zeta$, which can be expressed as the convolution of $d_k$ (the $k$-fold convolution) with $\zeta$. Thus, we have $d_{k + 1} = d_k * \zeta$.
  -/)]
theorem d_succ (k : ℕ) : d (k + 1) = d k * zeta := pow_succ zeta k

/-- The L-series for `d k` is summable -/
@[blueprint
  "LSeries_d_summable"
  (statement := /-- The L-series for $d_k$ is summable for $\Re(s) > 1$. -/)
  (proof := /--
  Since $d_k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$, and we know that the L-series of $\zeta$ converges for $\Re(s) > 1$, it follows that the L-series of $d_k$ also converges for $\Re(s) > 1$. This is because the convolution of functions with convergent L-series will also have a convergent L-series in the same region. Therefore, we can conclude that $L(d_k, s)$ is summable for $\Re(s) > 1$.
  -/)]
theorem LSeries_d_summable (k : ℕ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (↗(d k)) s := by
  sorry

/-- The L-series of `d k` equals `ζ(s)^k` for `Re(s) > 1`. -/
@[blueprint
  "LSeries_d_eq_riemannZeta_pow"
  (statement := /-- The $L$-series of $d_k$ equals $\zeta(s)^k$ for $\Re(s) > 1$. -/)
  (proof := /--
  From the definition of $d_k$ as the $k$-fold Dirichlet convolution of $\zeta$, we can express $d_k$ as $\zeta^k$. The L-series of a Dirichlet convolution corresponds to the product of the L-series of the individual functions. Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, it follows that $L(d_k, s) = L(\zeta^k, s) = (L(\zeta, s))^k = \zeta(s)^k$ for $\Re(s) > 1$ where the series converges.
  -/)]
theorem LSeries_d_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(d k)) s = riemannZeta s ^ k := by
  have natCoe_d_succ (j : ℕ) :
    (d (j + 1) : ArithmeticFunction ℂ) = (d j : ArithmeticFunction ℂ) * ζ := by
    rw [d_succ, natCoe_mul]
  suffices ∀ j, LSeries (↗(d j : ArithmeticFunction ℂ)) s = riemannZeta s ^ j ∧
      LSeriesSummable (↗(d j : ArithmeticFunction ℂ)) s from (this k).1
  intro j
  induction j with
  | zero =>
    simp only [d_zero, natCoe_one, pow_zero, one_eq_delta]
    exact ⟨congr_fun LSeries_delta s,
      (hasSum_single 1 fun n hn => by simp [LSeries.term_delta, hn]).summable⟩
  | succ j ih =>
    obtain ⟨ih_eq, ih_sum⟩ := ih
    have hζ : LSeriesSummable (↗(ζ : ArithmeticFunction ℂ)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    constructor
    · rw [pow_succ, LSeries_congr (fun {n} _ => show (d (j + 1) : ArithmeticFunction ℂ) n =
        ((d j : ArithmeticFunction ℂ) * ζ) n by rw [natCoe_d_succ]) s,
        LSeries_mul' ih_sum hζ, ih_eq]
      congr 1
      exact LSeries_zeta_eq_riemannZeta hs
    · rw [(LSeriesSummable_congr s (fun {n} _ => show (d (j + 1) : ArithmeticFunction ℂ) n =
        ((d j : ArithmeticFunction ℂ) * ζ) n by rw [natCoe_d_succ]))]
      exact LSeriesSummable_mul ih_sum hζ


/-- `d k` is multiplicative for all `k`. -/
@[blueprint
  "d_isMultiplicative"
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

/-- Explicit formula: `d k (p^a) = (a + k - 1).choose (k - 1) for prime p` for `k ≥ 1`. -/
@[blueprint
  "d_apply_prime_pow"
  (statement := /-- Explicit formula: $d_k (p^a) = (a + k - 1).choose (k - 1)$ for prime $p$ and $k \geq 1$. -/)
  (proof := /--
  The function $d_k$ counts the number of ways to write a natural number as an ordered product of $k$ natural numbers. For a prime power $p^a$, the number of ways to factor it into $k$ factors corresponds to the number of non-negative integer solutions to the equation $x_1 + x_2 + ... + x_k = a$, where each $x_i$ represents the exponent of $p$ in the factorization of the corresponding factor. This is a classic combinatorial problem, and the number of solutions is given by the formula $(a + k - 1).choose (k - 1)$, which counts the ways to distribute $a$ indistinguishable items (the prime factors) into $k$ distinguishable boxes (the factors).
  -/)]
theorem d_apply_prime_pow {k : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    d k (p ^ a) = (a + k - 1).choose (k - 1) := by
  sorry

/-- (1.25) in Iwaniec-Kowalski: a formula for `d_k` for all `n`.-/
@[blueprint
  "d_apply"
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
  sorry

/-- Divisor power sum with exponents in an arbitrary semiring `R`. -/
@[blueprint
  "sigmaR"
  (statement := /-- Divisor power sum with complex exponent. -/)]
noncomputable def sigmaR {R : Type*} [Semiring R] [HPow R R R] (s : R) : ArithmeticFunction R where
  toFun := fun n ↦ ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

@[inherit_doc]
scoped[ArithmeticFunction] notation "σᴿ" => ArithmeticFunction.sigmaR

/-- For natural exponents, sigmaR agrees with sigma. -/
@[blueprint
  "sigmaR_natCast"
  (statement := /-- For natural exponents, $\sigma^R$ agrees with $\sigma$. -/)
  (proof := /--
  The function $\sigma^R$ is defined as the sum of the $s$-th powers of the divisors of $n$. When $s$ is a natural number $k$, this definition coincides with the classical divisor power sum function $\sigma_k(n)$, which also sums the $k$-th powers of the divisors of $n$. Therefore, for natural exponents, we have $\sigma^R_k(n) = \sigma_k(n)$ when we view $\sigma_k(n)$ as a complex number. This can be shown by directly comparing the definitions and noting that both functions sum over the same set of divisors with the same exponentiation.
  -/)]
lemma sigmaR_natCast (k n : ℕ) :
    σᴿ k n = σ k n := by
  unfold sigmaR sigma
  simp

@[blueprint
  "powR"
  (statement := /-- Arithmetic function with complex parameter $\nu$. Evaluates as $n\mapsto n^{\nu}$ for $n\neq 0$ and $0$ at $n=0$. -/)]
noncomputable def powR (ν : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ ν, by grind⟩

@[blueprint
  "sigmaR_eq_zeta_mul_powR"
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
  "LSeries_powR_eq"
  (statement := /-- $L(\text{pow}^R(\nu), s) = \zeta(s - \nu)$ for $\Re(s - \nu) > 1$. -/)
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
  (statement := /-- $\zeta(s)\zeta(s - \nu) = \sum_{n=1}^{\infty} \sigma_\nu(n) n^{-s}$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$. -/)
  (proof := /--
  The divisor power sum function $\sigma_\nu$ is the Dirichlet convolution of the constant function $1$ (i.e., $\zeta$) and the power function $n \mapsto n^\nu$. The L-series of a Dirichlet convolution is the product of the L-series of the individual functions. Since $L(1, s) = \zeta(s)$ and $L(n \mapsto n^\nu, s) = \zeta(s - \nu)$, we have $L(\sigma_\nu, s) = \zeta(s) \cdot \zeta(s - \nu)$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$.
  -/)]
theorem LSeries_sigma_eq_riemannZeta_mul (ν : ℂ) {s : ℂ} (hs : 1 < s.re) (hsν : 1 < (s - ν).re) :
    LSeries (↗(σᴿ ν)) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [ ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, ← LSeries_powR_eq ν hsν, sigmaR_eq_zeta_mul_powR];
  apply ArithmeticFunction.LSeries_mul
  · apply (ArithmeticFunction.abscissaOfAbsConv_zeta.trans_lt _ )
    exact_mod_cast hs
  · apply lt_of_le_of_lt (abscissa_powR_le ν)
    rw[Complex.sub_re] at hsν
    exact_mod_cast (by linarith)

/-
Serious conversation to be had over zulip:

Do we want to change the `σ` function in Mathlib (NumberTheory.ArithmeticFunction.Misc) to take values in `ℕ` or `ℚ` or `ℝ` or `ℂ`, (like `[RorCLike]` for functions elsewhere) so that we can do the general theory. Alternative: define a second `σ` that plays this
more general role, and have the current `σ` be a special case of it.

Answer: make `σ[R] k` and prove all existing API for it, then derive original `σ k` as `σ[ℕ] k` as a
special case.

Next time: Make `σᴿ` versions of all existing `σ` API.
-/



end ArithmeticFunction
