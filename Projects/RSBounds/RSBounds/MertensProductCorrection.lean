import RSBounds.Totient
import RSBounds.PrimeLogTail
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The elementary prime-product / Mangoldt correction

The logarithmic Euler product contains all positive powers of its primes;
the finite Mangoldt sum contains only the powers not exceeding the cutoff.
Splitting the omitted powers at the square root, Chebyshev's elementary
`theta_le_log4_mul_x` gives a correction at most `5.6 / (sqrt n * log n)`
for `n ≥ 100000`. No RH, zero-free region, or prime number theorem is used.

The finite Taylor-tail proof is adapted from the unconditional lemma
`neg_log_le'` in `calr3/ternary-goldbach` at
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`,
`TernaryGoldbach/Prelim/MertensProduct.lean`. Its conditional analytic
theorems are not imported. The prime-power reindexing below strengthens
that source's finite-sum comparison to equality.

The exact-source compiler receipt and transitive axiom audit are recorded
separately in `verification/mertens-product-correction-run.json`.
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensProductCorrection

def primesTo (n : ℕ) : Finset ℕ := (Icc 1 n).filter Nat.Prime

noncomputable def powerMain (n p : ℕ) : ℝ :=
  ∑ i ∈ range (Nat.log p n), (1 / (p : ℝ)) ^ (i + 1) / (i + 1)

noncomputable def powerTail (n p : ℕ) : ℝ :=
  (1 / (p : ℝ)) ^ (Nat.log p n + 1) /
    ((Nat.log p n + 1) * (1 - 1 / p))

theorem log_prime_factor (p : ℕ) (hp : p.Prime) :
    Real.log ((p : ℝ) / (p - 1)) = -Real.log (1 - 1 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  rw [← Real.log_inv]
  congr 1
  field_simp [hp0, hp1]

/-- A finite partial Taylor series and its geometric remainder. -/
theorem log_factor_bounds (n p : ℕ) (hp : p.Prime) :
    powerMain n p ≤ Real.log ((p : ℝ) / (p - 1)) ∧
      Real.log ((p : ℝ) / (p - 1)) ≤ powerMain n p + powerTail n p := by
  let K := Nat.log p n
  let y : ℝ := 1 / (p : ℝ)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y < 1 := by dsimp [y]; exact (div_lt_one hp0).2 hp1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |y| < 1 by rwa [abs_of_nonneg hy0])
  rw [log_prime_factor p hp]
  constructor
  · change ∑ i ∈ range K, y ^ (i + 1) / (i + 1) ≤ -Real.log (1 - y)
    rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum _ (fun i _ => by positivity)
  · change -Real.log (1 - y) ≤
      (∑ i ∈ range K, y ^ (i + 1) / (i + 1)) +
        y ^ (K + 1) / ((K + 1) * (1 - y))
    rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add K]
    gcongr
    have hg := (hasSum_geometric_of_lt_one hy0 hy1).mul_left
      (y ^ (K + 1) / (K + 1))
    have ht := (summable_nat_add_iff K).2 hs.summable
    refine (Summable.tsum_le_tsum (fun i => ?_) ht hg.summable).trans (le_of_eq ?_)
    · have hK : (0 : ℝ) < K + 1 := by positivity
      have hi : (K : ℝ) + 1 ≤ ((i + K : ℕ) : ℝ) + 1 := by
        push_cast
        linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      rw [show i + K + 1 = (K + 1) + i by ring, pow_add]
      calc
        y ^ (K + 1) * y ^ i / (((i + K : ℕ) : ℝ) + 1) ≤
            y ^ (K + 1) * y ^ i / (K + 1) :=
          div_le_div_of_nonneg_left (by positivity) hK hi
        _ = y ^ (K + 1) / (K + 1) * y ^ i := by ring
    · rw [hg.tsum_eq]
      field_simp

/-- Exact finite reindexing by the prime base and positive exponent. -/
theorem sum_powerMain_eq (n : ℕ) :
    ∑ p ∈ primesTo n, powerMain n p =
      ∑ d ∈ Ioc 0 n, (Λ d : ℝ) / (d * Real.log d) := by
  rw [show (∑ p ∈ primesTo n, powerMain n p) =
      ∑ p ∈ primesTo n, ∑ i ∈ range (Nat.log p n),
        (1 / (p : ℝ)) ^ (i + 1) / (i + 1) by rfl, sum_sigma']
  let S := (primesTo n).sigma (fun p => range (Nat.log p n))
  let f : ℕ → ℝ := fun d => (Λ d : ℝ) / (d * Real.log d)
  let g : (Σ _ : ℕ, ℕ) → ℕ := fun z => z.1 ^ (z.2 + 1)
  have hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
    rintro ⟨p, i⟩ ha ⟨q, j⟩ hb he
    have hp := (mem_filter.1 (mem_sigma.1 ha).1).2
    have hq := (mem_filter.1 (mem_sigma.1 hb).1).2
    obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj hp hq he
    rfl
  have hval : ∀ z ∈ S,
      (1 / (z.1 : ℝ)) ^ (z.2 + 1) / (z.2 + 1) = f (g z) := by
    rintro ⟨p, i⟩ hz
    have hp := (mem_filter.1 (mem_sigma.1 hz).1).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    simp only [f, g]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    rw [Real.log_pow, one_div_pow]
    push_cast
    field_simp
  rw [sum_congr rfl hval, ← sum_image hinj]
  have hsub : S.image g ⊆ Ioc 0 n := by
    intro d hd
    obtain ⟨⟨p, i⟩, hz, rfl⟩ := mem_image.1 hd
    have hp := (mem_filter.1 (mem_sigma.1 hz).1).2
    have hpn := (mem_Icc.1 (mem_filter.1 (mem_sigma.1 hz).1).1).2
    have hi := mem_range.1 (mem_sigma.1 hz).2
    refine mem_Ioc.2 ⟨pow_pos hp.pos _, ?_⟩
    exact (Nat.pow_le_pow_right hp.pos hi).trans
      (Nat.pow_log_le_self p (Nat.ne_of_gt (hp.pos.trans_le hpn)))
  apply sum_subset hsub
  intro d hd hnot
  have hnotpow : ¬IsPrimePow d := by
    intro hdpp
    obtain ⟨p, i, hp, he⟩ := (isPrimePow_iff_pow_succ d).1 hdpp
    have hprime : p.Prime := hp.nat_prime
    have hpn : p ≤ n := by
      have hpd : p ≤ d := by
        rw [← he]
        exact Nat.le_self_pow (Nat.succ_ne_zero i) p
      exact hpd.trans (mem_Ioc.1 hd).2
    have hi : i < Nat.log p n := by
      have hh : i + 1 ≤ Nat.log p n :=
        Nat.le_log_of_pow_le hprime.one_lt (by simpa only [he] using (mem_Ioc.1 hd).2)
      omega
    apply hnot
    apply mem_image.2
    refine ⟨⟨p, i⟩, mem_sigma.2 ⟨?_, mem_range.2 hi⟩, he⟩
    exact mem_filter.2 ⟨mem_Icc.2 ⟨hprime.one_le, hpn⟩, hprime⟩
  dsimp [f]
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hnotpow, zero_div]

/-- The correction is nonnegative and is bounded by the sum of geometric tails. -/
theorem correction_le_sum_tail (n : ℕ) :
    0 ≤ Real.log (Totient.primeProduct n) -
        ∑ d ∈ Ioc 0 n, (Λ d : ℝ) / (d * Real.log d) ∧
      Real.log (Totient.primeProduct n) -
        (∑ d ∈ Ioc 0 n, (Λ d : ℝ) / (d * Real.log d)) ≤
          ∑ p ∈ primesTo n, powerTail n p := by
  have hlog : Real.log (Totient.primeProduct n) =
      ∑ p ∈ primesTo n, Real.log ((p : ℝ) / (p - 1)) := by
    apply Real.log_prod
    intro p hp
    have hprime := (mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    exact (div_pos (by linarith) (by linarith)).ne'
  have hlo := sum_le_sum (s := primesTo n) fun p hp =>
    (log_factor_bounds n p (mem_filter.1 hp).2).1
  have hhi := sum_le_sum (s := primesTo n) fun p hp =>
    (log_factor_bounds n p (mem_filter.1 hp).2).2
  rw [sum_add_distrib, sum_powerMain_eq] at hhi
  rw [sum_powerMain_eq] at hlo
  rw [hlog]
  constructor <;> linarith

/-- For any prime base, the missing powers cost at most `2 log p/(n log n)`. -/
theorem powerTail_le_log {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) :
    powerTail n p ≤ 2 * Real.log p / ((n : ℝ) * Real.log n) := by
  let K := Nat.log p n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpden : 0 < (p : ℝ) - 1 := by linarith
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hK0 : (0 : ℝ) < K + 1 := by positivity
  have hlt : (n : ℝ) < (p : ℝ) ^ (K + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt n
  have hlog := Real.log_lt_log hn0 hlt
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hK : (1 : ℝ) / (K + 1) ≤ Real.log p / Real.log n := by
    rw [div_le_div_iff₀ hK0 hLn]
    nlinarith
  have hq : (p : ℝ) / (p - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have he : powerTail n p =
      (1 / (p : ℝ) ^ (K + 1) * (p / (p - 1))) * (1 / (K + 1)) := by
    dsimp [powerTail, K]
    rw [one_div_pow]
    field_simp [hp0.ne', hpden.ne', hK0.ne'] <;> ring
  rw [he]
  calc
    _ ≤ (1 / (n : ℝ) * 2) * (Real.log p / Real.log n) := by
      apply mul_le_mul _ hK (by positivity) (by positivity)
      exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hn0 hlt.le) hq
        (by positivity) (by positivity)
    _ = _ := by ring

/-- Every prime at most the cutoff has at least its first power included. -/
theorem powerTail_le_half_geom {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    powerTail n p ≤ 1 / (2 * ((p : ℝ) * (p - 1))) := by
  let K := Nat.log p n
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by linarith
  have hK1 : 1 ≤ K := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpn)
  have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (K + 1) :=
    pow_le_pow_right₀ hp1.le (by omega)
  have hK2 : (2 : ℝ) ≤ K + 1 := by exact_mod_cast (by omega : 2 ≤ K + 1)
  have he : powerTail n p =
      1 / (p : ℝ) ^ (K + 1) * (p / (p - 1)) / (K + 1) := by
    dsimp [powerTail, K]
    rw [one_div_pow]
    field_simp [hp0.ne', hpden.ne'] <;> ring
  rw [he]
  calc
    _ ≤ 1 / (p : ℝ) ^ 2 * (p / (p - 1)) / 2 := by
      apply div_le_div₀ (by positivity) _ (by norm_num) hK2
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow) (by positivity)
    _ = _ := by field_simp [hp0.ne', hpden.ne'] <;> ring

/-- The contribution of primes at most the square root. -/
theorem low_tail_le {n : ℕ} (hn : 2 ≤ n) :
    ∑ p ∈ (primesTo n).filter (fun p : ℕ => (p : ℝ) ≤ √(n : ℝ)), powerTail n p ≤
      2 * Real.log 4 / (√(n : ℝ) * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hy0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hy2 := Real.sq_sqrt hn0.le
  have htheta :
      (∑ p ∈ (primesTo n).filter (fun p : ℕ => (p : ℝ) ≤ √(n : ℝ)), Real.log p) ≤
        Chebyshev.theta √(n : ℝ) := by
    unfold Chebyshev.theta
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpp := mem_filter.1 hp
      have hprime := (mem_filter.1 hpp.1).2
      exact mem_filter.2 ⟨mem_Ioc.2 ⟨hprime.pos, Nat.le_floor hpp.2⟩, hprime⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  calc
    _ ≤ ∑ p ∈ (primesTo n).filter (fun p : ℕ => (p : ℝ) ≤ √(n : ℝ)),
        2 * Real.log p / ((n : ℝ) * Real.log n) := by
      exact sum_le_sum fun p hp => powerTail_le_log hn (mem_filter.1 (mem_filter.1 hp).1).2
    _ = (2 / ((n : ℝ) * Real.log n)) *
        ∑ p ∈ (primesTo n).filter (fun p : ℕ => (p : ℝ) ≤ √(n : ℝ)), Real.log p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ (2 / ((n : ℝ) * Real.log n)) * (Real.log 4 * √(n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (htheta.trans (Chebyshev.theta_le_log4_mul_x hy0.le)) (by positivity)
    _ = _ := by
      field_simp [hn0.ne', hy0.ne', hLn.ne']
      nlinarith [congrArg (fun t : ℝ => (2 * Real.log 4) * t) hy2]

/-- The contribution of primes above the square root, via finite Abel summation. -/
theorem high_tail_le {n : ℕ} (hn : 4 ≤ n) :
    ∑ p ∈ (primesTo n).filter (fun p : ℕ => ¬(p : ℝ) ≤ √(n : ℝ)), powerTail n p ≤
      2 * Real.log 4 / ((√(n : ℝ) - 1) * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hy0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hy1 : 1 < √(n : ℝ) := by
    have h2 : (2 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
    linarith
  have hyn : √(n : ℝ) ≤ (n : ℝ) :=
    Real.sqrt_le_self_iff.2 (Or.inr (by exact_mod_cast (show 1 ≤ n by omega)))
  have hset : (primesTo n).filter (fun p : ℕ => ¬(p : ℝ) ≤ √(n : ℝ)) =
      (Ioc ⌊√(n : ℝ)⌋₊ ⌊(n : ℝ)⌋₊).filter Nat.Prime := by
    ext p
    simp only [primesTo, mem_filter, mem_Icc, mem_Ioc, Nat.floor_natCast, not_le]
    rw [Nat.floor_lt hy0.le]
    constructor
    · rintro ⟨⟨⟨h1, hpn⟩, hp⟩, hpy⟩
      exact ⟨⟨hpy, hpn⟩, hp⟩
    · rintro ⟨⟨hpy, hpn⟩, hp⟩
      exact ⟨⟨⟨hp.one_le, hpn⟩, hp⟩, hpy⟩
  have hpoint : ∀ p ∈ (primesTo n).filter (fun p : ℕ => ¬(p : ℝ) ≤ √(n : ℝ)),
      powerTail n p ≤ (1 / Real.log n) * (Real.log p / ((p : ℝ) * (p - 1))) := by
    intro p hp
    have hpp := mem_filter.1 hp
    have hprime := (mem_filter.1 hpp.1).2
    have hpn := (mem_Icc.1 (mem_filter.1 hpp.1).1).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hlog : Real.log n ≤ 2 * Real.log p := by
      have h := Real.log_le_log hy0 (le_of_lt (lt_of_not_ge hpp.2))
      rw [Real.log_sqrt hn0.le] at h
      linarith
    refine (powerTail_le_half_geom hprime hpn).trans ?_
    have hd : 0 < (p : ℝ) * (p - 1) := by positivity
    have hhalf : (1 : ℝ) / 2 ≤ Real.log p / Real.log n := by
      apply (le_div_iff₀ hLn).2
      linarith
    calc
      _ = ((1 : ℝ) / 2) / ((p : ℝ) * (p - 1)) := by rw [div_div]
      _ ≤ (Real.log p / Real.log n) / ((p : ℝ) * (p - 1)) :=
        div_le_div_of_nonneg_right hhalf hd.le
      _ = _ := by simp only [div_eq_mul_inv]; ring
  calc
    _ ≤ ∑ p ∈ (primesTo n).filter (fun p : ℕ => ¬(p : ℝ) ≤ √(n : ℝ)),
        (1 / Real.log n) * (Real.log p / ((p : ℝ) * (p - 1))) := sum_le_sum hpoint
    _ = (1 / Real.log n) *
        ∑ p ∈ (Ioc ⌊√(n : ℝ)⌋₊ ⌊(n : ℝ)⌋₊).filter Nat.Prime,
          Real.log p / ((p : ℝ) * (p - 1)) := by rw [hset, mul_sum]
    _ ≤ (1 / Real.log n) * (2 * Real.log 4 / (√(n : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (PrimeLogTail.sum_prime_log_div_mul_pred_le hy1 hyn)
        (by positivity)
    _ = _ := by field_simp [hLn.ne', (sub_pos.mpr hy1).ne'] <;> ring

theorem correction_budget {y L : ℝ} (hy : 316 ≤ y) (hL : 0 < L) :
    2 * Real.log 4 / (y * L) + 2 * Real.log 4 / ((y - 1) * L) ≤
      5.6 / (y * L) := by
  have hy0 : 0 < y := by linarith
  have hy1 : 0 < y - 1 := by linarith
  have hlog4 : Real.log 4 ≤ 1.39 := by
    have h := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  calc
    _ ≤ 2 * 1.39 / (y * L) + 2 * 1.39 / ((y - 1) * L) := by gcongr
    _ = (2 * 1.39 * (2 * y - 1)) / ((y - 1) * (y * L)) := by
      field_simp [hy0.ne', hy1.ne', hL.ne'] <;> ring
    _ ≤ (5.6 * (y - 1)) / ((y - 1) * (y * L)) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by field_simp [hy1.ne'] <;> ring

/-- The unconditional correction, with the exact finite product and Mangoldt sum visible. -/
theorem primeProduct_correction_bounds {n : ℕ} (hn : 100000 ≤ n) :
    0 ≤ Real.log (Totient.primeProduct n) -
        ∑ d ∈ Ioc 0 n, (Λ d : ℝ) / (d * Real.log d) ∧
      Real.log (Totient.primeProduct n) -
        (∑ d ∈ Ioc 0 n, (Λ d : ℝ) / (d * Real.log d)) ≤
          5.6 / (√(n : ℝ) * Real.log n) := by
  refine ⟨(correction_le_sum_tail n).1, (correction_le_sum_tail n).2.trans ?_⟩
  have hsplit : (∑ p ∈ primesTo n, powerTail n p) =
      (∑ p ∈ (primesTo n).filter (fun p : ℕ => (p : ℝ) ≤ √(n : ℝ)), powerTail n p) +
      ∑ p ∈ (primesTo n).filter (fun p : ℕ => ¬(p : ℝ) ≤ √(n : ℝ)), powerTail n p := by
    rw [sum_filter_add_sum_filter_not]
  rw [hsplit]
  refine (add_le_add (low_tail_le (by omega : 2 ≤ n))
    (high_tail_le (by omega : 4 ≤ n))).trans ?_
  apply correction_budget
  · apply Real.le_sqrt_of_sq_le
    have : (100000 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))

end TernaryGoldbach.RSBounds.MertensProductCorrection
