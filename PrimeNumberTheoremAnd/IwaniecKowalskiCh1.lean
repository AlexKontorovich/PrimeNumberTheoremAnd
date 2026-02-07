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
  (statement := /-- Additive function. -/)]
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  ∀ {m n : ℕ}, IsRelPrime m n → f (m * n) = f m + f n

@[blueprint
  "IsCompletelyAdditive"
  (statement := /-- Completely additive function. -/)]
def IsCompletelyAdditive [MulZeroOneClass R] :=
  MonoidWithZeroHom ℕ R


-- A helper lemma for the proof of `sum_divisors_mul_of_coprime`.
-- Break d into d₁ and d₂, where d₁ ∣ a and d₂ ∣ b.
-- The coprimality of a and b ensures that this decomposition is unique.
lemma unique_divisor_decomposition {a b d : ℕ} (hab : Coprime a b) (hd : d ∣ a * b) :
    ∃! p : ℕ × ℕ, p.1 ∣ a ∧ p.2 ∣ b ∧ p.1 * p.2 = d := by
  -- 1. Existence
  obtain ⟨d₁, d₂, h1, h2, h3⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  refine ⟨(d₁, d₂), ⟨h1, h2, h3.symm⟩, ?_⟩

  -- 2. Uniqueness
  rintro ⟨q₁, q₂⟩ ⟨hq1, hq2, hq3⟩
  dsimp at hq1 hq2 hq3
  have h_eq : d₁ * d₂ = q₁ * q₂ := by rw [← h3, ← hq3]

  have heq_1 : d₁ = q₁ := by
    -- d₁ ∣ q₁
    have : d₁ ∣ q₁ * q₂ := by rw [← h_eq]; apply dvd_mul_right
    have c1 : Coprime d₁ q₂ := by
      apply Coprime.of_dvd_right hq2
      apply Coprime.of_dvd_left h1
      exact hab
    rw [mul_comm] at this
    have hd1_q1 : d₁ ∣ q₁ := c1.dvd_of_dvd_mul_left this
    have : q₁ ∣ d₁ * d₂ := by rw [h_eq]; apply dvd_mul_right
    have c2 : Coprime q₁ d₂ := by
      apply Coprime.of_dvd_right h2
      apply Coprime.of_dvd_left hq1
      exact hab
    rw [mul_comm] at this
    have hq1_d1 : q₁ ∣ d₁ := c2.dvd_of_dvd_mul_left this

    exact dvd_antisymm hd1_q1 hq1_d1

  have heq_2 : d₂ = q₂ := by
    -- d₂ ∣ q₂
    have : d₂ ∣ q₁ * q₂ := by rw [← h_eq]; apply dvd_mul_left
    have c3 : Coprime d₂ q₁ := by
      apply Coprime.of_dvd_right hq1
      apply Coprime.of_dvd_left h2
      exact hab.symm
    have hd2_q2 : d₂ ∣ q₂ := c3.dvd_of_dvd_mul_left this

    -- q₂ ∣ d₂
    have : q₂ ∣ d₁ * d₂ := by rw [h_eq]; apply dvd_mul_left
    have c4 : Coprime q₂ d₁ := by
      apply Coprime.of_dvd_right h1
      apply Coprime.of_dvd_left hq2
      exact hab.symm
    have hq2_d2 : q₂ ∣ d₂ := c4.dvd_of_dvd_mul_left this

    exact dvd_antisymm hd2_q2 hq2_d2

  rw [heq_1, heq_2]

-- A more general version of sum_moebius_pmul_eq_prod_one_sub
-- If `f` is a multiplicative arithmetic function,
-- then for any two coprime natural numbers `a` and `b`,
-- the sum of `f(d)` over all divisors `d` of the product `a * b` equals the product of
-- the sums of `f(d)` over all divisors of `a` and `b` respectively.
theorem sum_divisors_mul_of_coprime {R : Type*} [CommRing R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {a b : ℕ} (hab : Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ d ∈ (a * b).divisors, f d = (∑ d ∈ a.divisors, f d) * (∑ d ∈ b.divisors, f d) := by
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2

  -- (ab).divisors = Image
  have h_image : (a * b).divisors = (a.divisors ×ˢ b.divisors).image g := by
    ext d
    constructor
    · intro hd
      obtain ⟨p, ⟨hp1, hp2, hp_eq⟩, _⟩ := unique_divisor_decomposition hab (mem_divisors.mp hd).1
      rw [mem_image]
      use p
      constructor
      · rw [mem_product, mem_divisors, mem_divisors]
        exact ⟨⟨hp1, ha⟩, ⟨hp2, hb⟩⟩
      · exact hp_eq
    · intro hd
      rw [mem_image] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      rw [mem_product, mem_divisors, mem_divisors] at hp
      rw [mem_divisors]
      exact ⟨mul_dvd_mul hp.1.1 hp.2.1, mul_ne_zero hp.1.2 hp.2.2⟩

  -- Injectivity
  have h_inj : Set.InjOn g (↑(a.divisors ×ˢ b.divisors)) := by
    intro p1 hp1 p2 hp2 h_eq
    simp only [Finset.mem_coe, Finset.mem_product] at hp1 hp2
    dsimp [g] at h_eq

    have h_dvd1 : p1.1 ∣ a := (Nat.mem_divisors.mp hp1.1).1
    have h_dvd2 : p1.2 ∣ b := (Nat.mem_divisors.mp hp1.2).1
    have hd : p1.1 * p1.2 ∣ a * b := mul_dvd_mul h_dvd1 h_dvd2

    obtain ⟨p, _, h_unique_imp⟩ := unique_divisor_decomposition hab hd
    have eq1 : p1 = p := h_unique_imp p1 ⟨h_dvd1, h_dvd2, rfl⟩

    have h_dvd1' : p2.1 ∣ a := (Nat.mem_divisors.mp hp2.1).1
    have h_dvd2' : p2.2 ∣ b := (Nat.mem_divisors.mp hp2.2).1
    have eq2 : p2 = p := h_unique_imp p2 ⟨h_dvd1', h_dvd2', h_eq.symm⟩

    rw [eq1, eq2]

  -- Change summation
  rw [h_image]
  rw [sum_image h_inj]
  rw [Finset.sum_product]
  rw [sum_mul_sum]

  -- Prove equality of terms
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  dsimp [g]
  apply hf.map_mul_of_coprime
  rw [mem_divisors] at hx hy
  apply Nat.Coprime.of_dvd_right hy.1
  apply Nat.Coprime.of_dvd_left hx.1
  exact hab


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
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _
    simp [hg.map_one]
  | prime_pow p k hp hk =>
    intro _
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
    rw [sum_divisors_prime_pow hp, Finset.sum_range_succ']
    simp only [pow_zero, moebius_apply_one, Int.cast_one, hg.map_one, mul_one]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hk)]
    · simp [moebius_apply_prime hp]; ring
    · intro i _ hi
      have hge2 : 2 ≤ i + 1 := by omega
      have hp1 : p ≠ 1 := hp.ne_one
      have hnsq : ¬Squarefree (p ^ (i + 1)) := by
        rw [Nat.squarefree_pow_iff hp1 (by omega : i + 1 ≠ 0)]
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
      -- h 1 = 1
      · simp only [h, ArithmeticFunction.coe_mk]
        simp [hg.left]

      --- Multiplicativity: h(mn) = h(m) * h(n) for coprime m, n
      · intro m n hmn
        simp only [h, ArithmeticFunction.coe_mk]
        rw [ArithmeticFunction.isMultiplicative_moebius.right hmn, hg.right hmn]
        -- Make ↑(μ(m) * μ(n)) to ↑μ(m) * ↑μ(n)
        push_cast
        --(a*b*c*d = c*d*a*b)
        ring

    -- Change the left-hand side to match the form required by sum_divisors_mul_of_coprime
    change ∑ d ∈ (a * b).divisors, h d = (∑ d ∈ a.divisors, h d) * (∑ d ∈ b.divisors, h d)
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
  sorry



end ArithmeticFunction
