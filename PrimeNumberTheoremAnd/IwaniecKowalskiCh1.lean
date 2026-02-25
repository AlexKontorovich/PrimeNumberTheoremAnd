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
  (statement := /-- Additive arithmetic function: satisfies `f(mn) = f(m) + f(n)` for coprime `m, n`. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Coprime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (statement := /-- Completely additive arithmetic function: satisfies `f(mn) = f(m) + f(n)` for all `m, n ≠ 0`. -/)]
def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive.isAdditive"
  (statement := /-- A completely additive function is additive. -/)]
lemma IsCompletelyAdditive.isAdditive [AddZeroClass R] {f : ArithmeticFunction R}
    (hf : IsCompletelyAdditive f) : IsAdditive f :=
  fun hm hn _ ↦ hf hm hn

-- **Think about more API for additive/completely additive functions, e.g. `f (p^k) = k * f p` for prime p, etc.**

/-- If `g` is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p \in n.\text{primeFactors}} (1 - g(p))$. -/
@[blueprint
  "sum_moebius_pmul_eq_prod_one_sub"
  (statement := /-- If `g` is a multiplicative arithmetic function, then for any $n \neq 0$,
    $\sum_{d | n} \mu(d) \cdot g(d) = \prod_{p \in n.\text{primeFactors}} (1 - g(p))$. -/)
  (proof := /--
  Multiply out and collect terms.
  -/)]
theorem sum_moebius_pmul_eq_prod_one_sub {R : Type*} [CommRing R]
    {g : ArithmeticFunction R} (hg : g.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (moebius d : R) * g d = ∏ p ∈ n.primeFactors, (1 - g p) := by
  sorry

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
  sorry

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
  (statement := /-- $d k$ is the $k$-fold divisor function: the number of ways to write $n$ as an ordered
    product of $k$ natural numbers. Equivalently, the Dirichlet convolution of $\zeta$ with
    itself $k$ times.-/)]
def d (k : ℕ) : ArithmeticFunction ℕ := zeta ^ k

/-- `d 0` is the multiplicative identity (indicator at 1). -/
@[blueprint
  "d_zero"
  (statement := /-- $d 0$ is the multiplicative identity (indicator at 1). -/)
  (proof := /--
  By definition, $d k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 0$, this corresponds to the empty convolution, which is defined to be the multiplicative identity in the algebra of arithmetic functions. The multiplicative identity is the function that takes the value $1$ at $n=1$ and $0$ elsewhere, which can be expressed as $\zeta^0$.
  -/)]
theorem d_zero : d 0 = 1 := pow_zero zeta

/-- `d 1` is `ζ`. -/
@[blueprint
  "d_one"
  (statement := /-- $d 1$ is $\zeta$. -/)
  (proof := /--
  By definition, $d k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 1$, this means we are taking the convolution of $\zeta$ with itself once, which simply gives us $\zeta$. Therefore, $d 1 = \zeta^1 = \zeta$.
  -/)]
theorem d_one : d 1 = zeta := pow_one zeta

/-- `d 2` is the classical divisor count function `τ`. -/
@[blueprint
  "d_two"
  (statement := /-- $d 2$ is the classical divisor count function $\tau$. -/)
  (proof := /--
  By definition, $d k$ is the $k$-fold Dirichlet convolution of $\zeta$. When $k = 2$, this means we are taking the convolution of $\zeta$ with itself twice, which gives us $\zeta * \zeta$. From the earlier theorem, we know that $\zeta * \zeta = \tau$, where $\tau$ is the divisor count function. Therefore, $d 2 = \zeta^2 = \tau$.
  -/)]
theorem d_two : d 2 = τ := by simp [d, sq, zeta_mul_zeta]

/-- Recurrence: d (k+1) = d k * ζ. -/
@[blueprint
  "d_succ"
  (statement := /-- Recurrence: $d (k+1) = d k * \zeta$. -/)
  (proof := /--
  By definition, $d k$ is the $k$-fold Dirichlet convolution of $\zeta$. Therefore, $d (k + 1)$ is the $(k + 1)$-fold convolution of $\zeta$, which can be expressed as the convolution of $d k$ (the $k$-fold convolution) with $\zeta$. Thus, we have $d (k + 1) = d k * \zeta$.
  -/)]
theorem d_succ (k : ℕ) : d (k + 1) = d k * zeta := pow_succ zeta k

/-- The L-series of `d k` equals `ζ(s)^k` for `Re(s) > 1`. -/
@[blueprint
  "LSeries_d_eq_riemannZeta_pow"
  (statement := /-- The $L$-series of $d k$ equals $\zeta(s)^k$ for $\Re(s) > 1$. -/)
  (proof := /--
  From the definition of $d k$ as the $k$-fold Dirichlet convolution of $\zeta$, we can express $d k$ as $\zeta^k$. The L-series of a Dirichlet convolution corresponds to the product of the L-series of the individual functions. Since $L(\zeta, s)$ is the Riemann zeta function $\zeta(s)$, it follows that $L(d k, s) = L(\zeta^k, s) = (L(\zeta, s))^k = \zeta(s)^k$ for $\Re(s) > 1$ where the series converges.
  -/)]
theorem LSeries_d_eq_riemannZeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(d k)) s = riemannZeta s ^ k := by
  have natCoe_zeta : (↑(ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = ζ := by
    ext n; simp [natCoe_apply, zeta_apply]
  have natCoe_d_succ (j : ℕ) :
    (↑(d (j + 1)) : ArithmeticFunction ℂ) = (↑(d j) : ArithmeticFunction ℂ) * ζ := by
    rw [d_succ, natCoe_mul, natCoe_zeta]
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
    · rw [pow_succ, LSeries_congr (fun {n} _ => show (↑(d (j + 1)) : ArithmeticFunction ℂ) n =
        ((↑(d j) : ArithmeticFunction ℂ) * ζ) n by rw [natCoe_d_succ]) s,
        LSeries_mul' ih_sum hζ, ih_eq]
      congr 1
      exact LSeries_zeta_eq_riemannZeta hs
    · rw [(LSeriesSummable_congr s (fun {n} _ => show (↑(d (j + 1)) : ArithmeticFunction ℂ) n =
        ((↑(d j) : ArithmeticFunction ℂ) * ζ) n by rw [natCoe_d_succ]))]
      exact LSeriesSummable_mul ih_sum hζ


/-- `d k` is multiplicative for all `k`. -/
@[blueprint
  "d_isMultiplicative"
  (statement := /-- $d k$ is multiplicative for all $k$. (Is $k \ge1$ needed?) -/)
  (proof := /--
  The function $d k$ is defined as the $k$-fold Dirichlet convolution of $\zeta$. Since $\zeta$ is a multiplicative function, and the Dirichlet convolution of multiplicative functions is also multiplicative, it follows that $d k$ is multiplicative for all $k$. This can be shown by induction on $k$, using the fact that the convolution of a multiplicative function with another multiplicative function remains multiplicative.
  -/)]
theorem d_isMultiplicative (k : ℕ) : (d k).IsMultiplicative := by
  induction k with
  | zero => rw [d_zero]; exact isMultiplicative_one
  | succ k ih =>
    sorry -- follows from IsMultiplicative.pow and isMultiplicative_zeta

/-- Explicit formula: `d k (p^a) = (a + k - 1).choose (k - 1) for prime p` for `k ≥ 1`. -/
@[blueprint
  "d_apply_prime_pow"
  (statement := /-- Explicit formula: $d k (p^a) = (a + k - 1).choose (k - 1)$ for prime $p$ and $k \geq 1$. -/)
  (proof := /--
  The function $d k$ counts the number of ways to write a natural number as an ordered product of $k$ natural numbers. For a prime power $p^a$, the number of ways to factor it into $k$ factors corresponds to the number of non-negative integer solutions to the equation $x_1 + x_2 + ... + x_k = a$, where each $x_i$ represents the exponent of $p$ in the factorization of the corresponding factor. This is a classic combinatorial problem, and the number of solutions is given by the formula $(a + k - 1).choose (k - 1)$, which counts the ways to distribute $a$ indistinguishable items (the prime factors) into $k$ distinguishable boxes (the factors).
  -/)]
theorem d_apply_prime_pow {k : ℕ} (hk : 0 < k) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    d k (p ^ a) = (a + k - 1).choose (k - 1) := by
  classical
  cases k with
  | zero =>
      -- impossible: 0 < 0
      cases (Nat.lt_irrefl 0 hk)
  | succ k =>
      -- After `k = succ k`, the goal is equivalent to:
      --   d (k+1) (p^a) = (a+k).choose k
      -- We'll prove that directly by induction on `k`.
      have hk' : d (k + 1) (p ^ a) = (a + k).choose k := by
        induction k generalizing a with
        | zero =>
            -- k = 0: d 1 = ζ and ζ(p^a)=1
            have hn : p ^ a ≠ 0 := pow_ne_zero a hp.ne_zero
            simp [d_one, ArithmeticFunction.zeta_apply_ne hn]
        | succ k ih =>
            -- k -> k+1: use the recurrence d(j+1)=d(j)*ζ, then sum over divisors of p^a
            calc
              d (k + 2) (p ^ a)
                  = ((d (k + 1)) * zeta) (p ^ a) := by
                      -- apply d_succ to j = k+1 and then evaluate at p^a
                      simpa [Nat.add_assoc] using
                        congrArg (fun f => f (p ^ a)) (d_succ (k + 1))
              _ = ∑ x ∈ (p ^ a).divisors, d (k + 1) x := by
                      -- (f*ζ)(n) = ∑_{d|n} f(d)
                      simpa using
                        (ArithmeticFunction.mul_zeta_apply (f := d (k + 1)) (x := p ^ a))
              _ = ∑ x ∈ Finset.range (a + 1), d (k + 1) (p ^ x) := by
                      -- divisors of p^a are exactly p^x, x=0..a
                      simpa using
                        (Nat.sum_divisors_prime_pow (k := a) (p := p)
                          (f := fun x => d (k + 1) x) hp)
              _ = ∑ x ∈ Finset.range (a + 1), (x + k).choose k := by
                      -- rewrite with IH inside the sum
                      simp [ih]
              _ = (a + k + 1).choose (k + 1) := by
                      -- hockey-stick identity
                      simpa using (Nat.sum_range_add_choose a k)
              _ = (a + (k + 1)).choose (k + 1) := by
                      -- tidy arithmetic
                      simp [Nat.add_assoc]
      -- Now translate back to the original statement (undo the "k = succ k" rewrite)
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk'

/-- (1.25) in Iwaniec-Kowalski: a formula for `d k` for all `n`. -/
@[blueprint
  "d_apply"
  (statement := /-- (1.25) in Iwaniec-Kowalski: a formula for $d k$ for all $n$. -/)
  (proof := /--
  The function $d k$ is multiplicative, so to compute $d k(n)$ for a general natural number $n$, we can factor $n$ into its prime power decomposition: $n = p_1^{a_1} p_2^{a_2} ... p_m^{a_m}$. Since $d k$ is multiplicative, we have:

  \[
  d k(n) = d k(p_1^{a_1}) \cdot d k(p_2^{a_2}) \cdot ... \cdot d k(p_m^{a_m})
  \]

  Using the explicit formula for prime powers from the previous theorem, we can substitute to get:

  \[
  d k(n) = \prod_{i=1}^{m} (a_i + k - 1).choose (k - 1)
  \]

  This gives us a complete formula for $d k(n)$ in terms of the prime factorization of $n$.
  -/)]
lemma d_apply {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    d k n = ∏ p ∈ n.primeFactors, (n.factorization p + k - 1).choose (k - 1) := by
  have hmult : (d k).IsMultiplicative := d_isMultiplicative k

  calc
    d k n
        = n.factorization.prod (fun (p a : ℕ) => d k (p ^ a)) := by
            exact ArithmeticFunction.IsMultiplicative.multiplicative_factorization (d k) hmult hn
    _   = ∏ p ∈ n.primeFactors, d k (p ^ n.factorization p) := by
            exact Nat.prod_factorization_eq_prod_primeFactors (n := n)
              (f := fun (p a : ℕ) => d k (p ^ a))
    _   = ∏ p ∈ n.primeFactors, (n.factorization p + k - 1).choose (k - 1) := by
            refine Finset.prod_congr rfl ?_
            intro p hp
            have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
            simpa using d_apply_prime_pow (k := k) hk hp' (n.factorization p)

/-- Divisor power sum with exponents in an arbitrary semiring `R`. -/
@[blueprint
  "sigmaC"
  (statement := /-- Divisor power sum with complex exponent. -/)]
noncomputable def sigmaC {R : Type*} [Semiring R] [HPow R R R] (s : R) : ArithmeticFunction R where
  toFun := fun n ↦ ∑ d ∈ n.divisors, (d : R) ^ s
  map_zero' := by simp

/-- For natural exponents, sigmaC agrees with sigma. -/
@[blueprint
  "sigmaC_natCast"
  (statement := /-- For natural exponents, $\sigma_C$ agrees with $\sigma$. -/)
  (proof := /--
  The function $\sigma_C$ is defined as the sum of the $s$-th powers of the divisors of $n$. When $s$ is a natural number $k$, this definition coincides with the classical divisor power sum function $\sigma k n$, which also sums the $k$-th powers of the divisors of $n$. Therefore, for natural exponents, we have $\sigma_C k n = \sigma k n$ when we view $\sigma k n$ as a complex number. This can be shown by directly comparing the definitions and noting that both functions sum over the same set of divisors with the same exponentiation.
  -/)]
lemma sigmaC_natCast (k : ℕ) (n : ℕ) :
    sigmaC k n = (σ k n : ℂ) := by
  sorry

/-- `ζ(s)ζ(s - ν) = Σ σ_ν(n) n^(-s)` for `Re(s) > 1` and `Re(s - ν) > 1`. -/
@[blueprint
  "LSeries_sigma_eq_riemannZeta_mul"
  (statement := /-- $\zeta(s)\zeta(s - \nu) = \sum_{n=1}^{\infty} \sigma_\nu(n) n^{-s}$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$. -/)
  (proof := /--
  The divisor power sum function $\sigma_\nu$ is the Dirichlet convolution of the constant function $1$ (i.e., $\zeta$) and the power function $n \mapsto n^\nu$. The L-series of a Dirichlet convolution is the product of the L-series of the individual functions. Since $L(1, s) = \zeta(s)$ and $L(n \mapsto n^\nu, s) = \zeta(s - \nu)$, we have $L(\sigma_\nu, s) = \zeta(s) \cdot \zeta(s - \nu)$ for $\Re(s) > 1$ and $\Re(s - \nu) > 1$.
  -/)]
theorem LSeries_sigma_eq_riemannZeta_mul (ν : ℂ) {s : ℂ} (hs : 1 < s.re) (hsν : 1 < (s - ν).re) :
    LSeries (↗(sigmaC ν)) s = riemannZeta s * riemannZeta (s - ν) := by
  sorry

/-
Serious conversation to be had over zulip:

Do we want to change the `σ` function in Mathlib (NumberTheory.ArithmeticFunction.Misc) to take values in `ℕ` or `ℚ` or `ℝ` or `ℂ`, (like `[RorCLike]` for functions elsewhere) so that we can do the general theory. Alternative: define a second `σ` that plays this
more general role, and have the current `σ` be a special case of it.
-/

end ArithmeticFunction
