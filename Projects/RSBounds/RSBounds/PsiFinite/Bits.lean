import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import RSBounds.PsiFinite.Kernel

/-!
# Bit-level soundness of the kernel sieve

`testBit_repK` describes the doubling comb, `combK_testBit` the comb of one
base prime, `startPos_spec` the first crossed index, and `sieveK_fst_testBit`
the OR over the base primes. `primeBits_testBit` combines them: after the
sieve, bit `i < L` of the complement is set iff `lo + 2i` is prime, provided
the base list is increasing, odd, at least 3, and contains every odd prime `p`
with `p*p ≤ hi`.
-/

namespace PsiFinite

theorem brk_eq {α : Sort*} (x : α) : brk x = x := rfl

theorem repK_zero (x s : ℕ) : repK 0 x s = x := rfl

theorem repK_succ (k x s : ℕ) : repK (k + 1) x s = repK k (x ||| (x <<< s)) (s + s) := rfl

/-- The doubling comb is the OR of `2^k` shifted copies of `x`, spaced by `s`. -/
theorem testBit_repK (k : ℕ) : ∀ x s i : ℕ,
    (repK k x s).testBit i = true ↔ ∃ t < 2 ^ k, s * t ≤ i ∧ x.testBit (i - s * t) = true := by
  induction k with
  | zero =>
    intro x s i
    simp only [repK_zero, pow_zero, Nat.lt_one_iff]
    constructor
    · intro h; exact ⟨0, rfl, by simp, by simpa using h⟩
    · rintro ⟨t, rfl, -, h⟩; simpa using h
  | succ k ih =>
    intro x s i
    rw [repK_succ, ih]
    constructor
    · rintro ⟨t, ht, hle, hb⟩
      have e1 : (s + s) * t = 2 * (s * t) := by ring
      rw [e1] at hle hb
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_iff] at hb
      rcases hb with hb | ⟨hs, hb⟩
      · refine ⟨2 * t, by rw [pow_succ]; omega, ?_, ?_⟩
        · rw [show s * (2 * t) = 2 * (s * t) by ring]; exact hle
        · rw [show s * (2 * t) = 2 * (s * t) by ring]; exact hb
      · refine ⟨2 * t + 1, by rw [pow_succ]; omega, ?_, ?_⟩
        · rw [show s * (2 * t + 1) = 2 * (s * t) + s by ring]; omega
        · rw [show s * (2 * t + 1) = 2 * (s * t) + s by ring,
            show i - (2 * (s * t) + s) = i - 2 * (s * t) - s by omega]; exact hb
    · rintro ⟨t, ht, hle, hb⟩
      rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
      · refine ⟨u, by rw [pow_succ] at ht; omega, ?_, ?_⟩
        · rw [show (s + s) * u = s * (2 * u) by ring]; exact hle
        · rw [Nat.testBit_or, show (s + s) * u = s * (2 * u) by ring, hb, Bool.true_or]
      · refine ⟨u, by rw [pow_succ] at ht; omega, ?_, ?_⟩
        · rw [show (s + s) * u = 2 * (s * u) by ring]
          rw [show s * (2 * u + 1) = 2 * (s * u) + s by ring] at hle; omega
        · rw [show s * (2 * u + 1) = 2 * (s * u) + s by ring] at hle hb
          rw [Nat.testBit_or, Nat.testBit_shiftLeft, show (s + s) * u = 2 * (s * u) by ring]
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
          right
          refine ⟨by omega, ?_⟩
          rw [show i - 2 * (s * u) - s = i - (2 * (s * u) + s) by omega]; exact hb

theorem combK_of_lt {lo L d : ℕ} (h : startPos lo d < L) :
    combK lo L d = repK (Nat.log2 ((L - 1 - startPos lo d) / d) + 1) (1 <<< startPos lo d) d := by
  unfold combK; dsimp only
  rw [show Nat.blt (startPos lo d) L = true from by simpa using h]; rfl

theorem combK_of_ge {lo L d : ℕ} (h : L ≤ startPos lo d) : combK lo L d = 0 := by
  unfold combK; dsimp only
  rw [show Nat.blt (startPos lo d) L = false from by
    rw [Bool.eq_false_iff]; intro h'
    exact absurd (Nat.le_of_ble_eq_true h' : startPos lo d + 1 ≤ L) (by omega)]

/-- Bit `i < L` of the comb of `d` is set iff `i` is `startPos lo d` plus a
multiple of `d`. -/
theorem combK_testBit {lo L d i : ℕ} (hd : 0 < d) (hi : i < L) :
    (combK lo L d).testBit i = true ↔ startPos lo d ≤ i ∧ d ∣ i - startPos lo d := by
  by_cases hjL : startPos lo d < L
  · rw [combK_of_lt hjL, testBit_repK]
    set j0 := startPos lo d
    constructor
    · rintro ⟨t, -, hle, hbit⟩
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at hbit
      exact ⟨by omega, ⟨t, by omega⟩⟩
    · rintro ⟨hle, t, ht⟩
      refine ⟨t, ?_, by omega, ?_⟩
      · have h1 : t ≤ (L - 1 - j0) / d := by
          rw [Nat.le_div_iff_mul_le hd, mul_comm]; omega
        exact lt_of_le_of_lt h1 Nat.lt_log2_self
      · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]; omega
  · rw [combK_of_ge (by omega)]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_and]
    intro h; omega

theorem startPos_of_le {lo d : ℕ} (h : lo ≤ d * d) : startPos lo d = (d * d - lo) / 2 := by
  unfold startPos
  rw [show Nat.ble lo (Nat.mul d d) = true from Nat.ble_eq_true_of_le h]; rfl

theorem startPos_of_lt {lo d : ℕ} (h : d * d < lo) :
    startPos lo d = ((d - lo % d) % d * ((d + 1) / 2)) % d := by
  unfold startPos
  rw [show Nat.ble lo (Nat.mul d d) = false from by
    rw [Bool.eq_false_iff]; intro h'
    exact absurd (Nat.le_of_ble_eq_true h' : lo ≤ d * d) (by omega)]; rfl

/-- The defining property of `startPos`, for odd `lo` and odd `d`. -/
theorem startPos_spec {lo d : ℕ} (hlo : lo % 2 = 1) (hd : d % 2 = 1) (i : ℕ) :
    (d ∣ lo + 2 * i ∧ d * d ≤ lo + 2 * i) ↔ (startPos lo d ≤ i ∧ d ∣ i - startPos lo d) := by
  have hd0 : 0 < d := by omega
  have hcop : Nat.Coprime d 2 := by
    rw [Nat.coprime_comm, Nat.coprime_two_left]; exact Nat.odd_iff.mpr hd
  -- `lo + 2 * startPos lo d` is a multiple of `d` that is at least `d*d`, or at least `lo`.
  have key : d ∣ lo + 2 * startPos lo d ∧
      (lo ≤ d * d → lo + 2 * startPos lo d = d * d) ∧
      (d * d < lo → startPos lo d < d) := by
    by_cases h : lo ≤ d * d
    · rw [startPos_of_le h]
      have hpar : (d * d - lo) % 2 = 0 := by
        have : (d * d) % 2 = 1 := by rw [Nat.mul_mod, hd]
        omega
      have e : lo + 2 * ((d * d - lo) / 2) = d * d := by omega
      exact ⟨by rw [e]; exact Dvd.intro d rfl, fun _ => e, fun h' => absurd h (by omega)⟩
    · rw [startPos_of_lt (by omega)]
      refine ⟨?_, fun h' => absurd h' h, fun _ => Nat.mod_lt _ hd0⟩
      rw [← ZMod.natCast_eq_zero_iff]
      have h2 : 2 * ((d + 1) / 2) = d + 1 := by omega
      have hr : lo % d ≤ d := (Nat.mod_lt _ hd0).le
      have hc : (2 : ZMod d) * (((d + 1) / 2 : ℕ) : ZMod d) = 1 := by
        have := congrArg (fun n : ℕ => (n : ZMod d)) h2
        push_cast at this; rw [this]; simp
      push_cast [ZMod.natCast_mod, Nat.cast_sub hr]
      rw [show (lo : ZMod d) + 2 * (((d : ZMod d) - (lo : ZMod d)) * (((d + 1) / 2 : ℕ) : ZMod d))
          = lo + ((d : ZMod d) - lo) * (2 * (((d + 1) / 2 : ℕ) : ZMod d)) by ring, hc]
      simp
  obtain ⟨hdiv, hcase1, hcase2⟩ := key
  set j0 := startPos lo d
  constructor
  · rintro ⟨hdi, hsq⟩
    by_cases h : lo ≤ d * d
    · have e := hcase1 h
      have hij : j0 ≤ i := by omega
      refine ⟨hij, ?_⟩
      have : d ∣ 2 * (i - j0) := by
        have e2 : lo + 2 * i = (lo + 2 * j0) + 2 * (i - j0) := by omega
        rw [e2] at hdi; exact (Nat.dvd_add_right hdiv).mp hdi
      exact hcop.dvd_of_dvd_mul_left this
    · have hj := hcase2 (by omega)
      by_cases hij : j0 ≤ i
      · refine ⟨hij, ?_⟩
        have : d ∣ 2 * (i - j0) := by
          have e2 : lo + 2 * i = (lo + 2 * j0) + 2 * (i - j0) := by omega
          rw [e2] at hdi; exact (Nat.dvd_add_right hdiv).mp hdi
        exact hcop.dvd_of_dvd_mul_left this
      · exfalso
        have : d ∣ 2 * (j0 - i) := by
          have e2 : lo + 2 * j0 = (lo + 2 * i) + 2 * (j0 - i) := by omega
          rw [e2] at hdiv; exact (Nat.dvd_add_right hdi).mp hdiv
        have h3 := hcop.dvd_of_dvd_mul_left this
        have := Nat.le_of_dvd (by omega) h3
        omega
  · rintro ⟨hij, t, ht⟩
    have e2 : lo + 2 * i = (lo + 2 * j0) + d * (2 * t) := by
      rw [show d * (2 * t) = 2 * (d * t) by ring, ← ht]; omega
    refine ⟨?_, ?_⟩
    · rw [e2]; exact dvd_add hdiv (Dvd.intro _ rfl)
    · by_cases h : lo ≤ d * d
      · have := hcase1 h; rw [e2, this]; exact Nat.le_add_right _ _
      · omega

theorem sieveK_nil (lo L hi top acc : ℕ) (E : List (ℕ × ℕ)) :
    sieveK lo L hi top [] acc E = (acc, E) := rfl

theorem sieveK_cons_stop {lo L hi top d acc : ℕ} {ds : List ℕ} {E : List (ℕ × ℕ)}
    (h : hi < d * d) : sieveK lo L hi top (d :: ds) acc E = (acc, E) := by
  show Bool.rec (motive := fun _ => ℕ × List (ℕ × ℕ)) _ _ (Nat.ble (Nat.mul d d) hi) = _
  rw [show Nat.ble (Nat.mul d d) hi = false from by
    rw [Bool.eq_false_iff]; intro h'
    exact absurd (Nat.le_of_ble_eq_true h' : d * d ≤ hi) (by omega)]

theorem sieveK_cons_go {lo L hi top d acc : ℕ} {ds : List ℕ} {E : List (ℕ × ℕ)}
    (h : d * d ≤ hi) : sieveK lo L hi top (d :: ds) acc E =
      sieveK lo L hi top ds (acc ||| combK lo L d) (powsK 64 d (d * d) 2 lo top E) := by
  show Bool.rec (motive := fun _ => ℕ × List (ℕ × ℕ)) _ _ (Nat.ble (Nat.mul d d) hi) = _
  rw [show Nat.ble (Nat.mul d d) hi = true from Nat.ble_eq_true_of_le h]
  show Bool.rec (motive := fun _ => ℕ × List (ℕ × ℕ))
    (brk (sieveK lo L hi top ds (acc ||| combK lo L d) _))
    (brk (sieveK lo L hi top ds 0 _)) (Nat.beq (acc ||| combK lo L d) 0) = _
  cases hb : Nat.beq (acc ||| combK lo L d) 0
  · rfl
  · have : acc ||| combK lo L d = 0 := Nat.eq_of_beq_eq_true hb
    show brk (sieveK lo L hi top ds 0 _) = _
    rw [brk_eq, this]; rfl

/-- The composite mask is the OR of the combs of the base primes `d` with
`d*d ≤ hi`, for an increasing list. -/
theorem sieveK_fst_testBit {lo L hi top : ℕ} : ∀ (l : List ℕ), l.Pairwise (· < ·) →
    ∀ (acc : ℕ) (E : List (ℕ × ℕ)) (i : ℕ),
    (sieveK lo L hi top l acc E).1.testBit i = true ↔
      acc.testBit i = true ∨ ∃ d ∈ l, d * d ≤ hi ∧ (combK lo L d).testBit i = true := by
  intro l
  induction l with
  | nil => intro _ acc E i; simp [sieveK_nil]
  | cons d ds ih =>
    intro hl acc E i
    rw [List.pairwise_cons] at hl
    by_cases h : d * d ≤ hi
    · rw [sieveK_cons_go h, ih hl.2, Nat.testBit_or, Bool.or_eq_true]
      constructor
      · rintro ((h1 | h1) | ⟨e, he, h2⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨d, List.mem_cons_self, h, h1⟩
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, h2⟩
      · rintro (h1 | ⟨e, he, h2, h3⟩)
        · exact Or.inl (Or.inl h1)
        · rcases List.mem_cons.mp he with rfl | he
          · exact Or.inl (Or.inr h3)
          · exact Or.inr ⟨e, he, h2, h3⟩
    · rw [sieveK_cons_stop (by omega)]
      constructor
      · intro h1; exact Or.inl h1
      · rintro (h1 | ⟨e, he, h2, -⟩)
        · exact h1
        · exfalso
          rcases List.mem_cons.mp he with rfl | he
          · exact h h2
          · have := hl.1 e he
            exact h (le_trans (Nat.mul_le_mul this.le this.le) h2)

/-- An odd `n ≥ 3` is composite iff it has a divisor `d` in the list with
`d*d ≤ n`, given that the list holds all odd primes up to `√hi` and only odd
numbers `≥ 3`. -/
theorem not_prime_iff_crossed {l : List ℕ} {hi n : ℕ}
    (hodd : ∀ d ∈ l, d % 2 = 1 ∧ 3 ≤ d)
    (hcomp : ∀ p, p.Prime → p % 2 = 1 → p * p ≤ hi → p ∈ l)
    (hn : n % 2 = 1) (hn3 : 3 ≤ n) (hnhi : n ≤ hi) :
    ¬ n.Prime ↔ ∃ d ∈ l, d * d ≤ hi ∧ d ∣ n ∧ d * d ≤ n := by
  constructor
  · intro hnp
    have hmin := Nat.minFac_prime (show n ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hdvd := Nat.minFac_dvd n
    have hodd' : n.minFac % 2 = 1 := by
      rcases hmin.eq_two_or_odd with h2 | h2
      · rw [h2] at hdvd; omega
      · exact h2
    refine ⟨n.minFac, hcomp _ hmin hodd' (by nlinarith), by nlinarith, hdvd, by nlinarith⟩
  · rintro ⟨d, hd, -, hdn, hsq⟩ hp
    have h3 := (hodd d hd).2
    rcases hp.eq_one_or_self_of_dvd d hdn with h | h
    · omega
    · subst h; nlinarith

/-- After the sieve, bit `i < L` of the complement of the mask is set iff
`lo + 2i` is prime. -/
theorem sieve_testBit_iff_prime {lo L hi top : ℕ} {l : List ℕ} {E : List (ℕ × ℕ)}
    (hl : l.Pairwise (· < ·)) (hodd : ∀ d ∈ l, d % 2 = 1 ∧ 3 ≤ d)
    (hcomp : ∀ p, p.Prime → p % 2 = 1 → p * p ≤ hi → p ∈ l)
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo) {i : ℕ} (hiL : i < L) (hihi : lo + 2 * i ≤ hi) :
    (sieveK lo L hi top l 0 E).1.testBit i = false ↔ (lo + 2 * i).Prime := by
  rw [← Bool.not_eq_true, sieveK_fst_testBit l hl, Nat.zero_testBit]
  simp only [Bool.false_eq_true, false_or]
  rw [← not_iff_not, not_not, not_prime_iff_crossed hodd hcomp (by omega) (by omega) hihi]
  constructor
  · rintro ⟨d, hd, h1, h2⟩
    have hd' := hodd d hd
    exact ⟨d, hd, h1, (startPos_spec hlo hd'.1 i).mpr ((combK_testBit (by omega) hiL).mp h2)⟩
  · rintro ⟨d, hd, h1, h2, h3⟩
    have hd' := hodd d hd
    exact ⟨d, hd, h1, (combK_testBit (by omega) hiL).mpr ((startPos_spec hlo hd'.1 i).mp ⟨h2, h3⟩)⟩

/-- The prime bitset of a segment. -/
theorem primeBits_testBit {lo L hi top : ℕ} {l : List ℕ} {E : List (ℕ × ℕ)}
    (hl : l.Pairwise (· < ·)) (hodd : ∀ d ∈ l, d % 2 = 1 ∧ 3 ≤ d)
    (hcomp : ∀ p, p.Prime → p % 2 = 1 → p * p ≤ hi → p ∈ l)
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo) (hLhi : ∀ i < L, lo + 2 * i ≤ hi) (i : ℕ) :
    (Nat.xor (2 ^ L - 1) (Nat.land (sieveK lo L hi top l 0 E).1 (2 ^ L - 1))).testBit i = true ↔
      i < L ∧ (lo + 2 * i).Prime := by
  change ((2 ^ L - 1) ^^^ ((sieveK lo L hi top l 0 E).1 &&& (2 ^ L - 1))).testBit i = true ↔ _
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hiL : i < L
  · rw [← sieve_testBit_iff_prime (top := top) (E := E) hl hodd hcomp hlo hlo3 hiL (hLhi i hiL)]
    cases (sieveK lo L hi top l 0 E).1.testBit i <;> simp [hiL]
  · simp [hiL]

/-- The prime bitset of a sieve, as a constant applied to its parameters. -/
noncomputable def primeBitsOf (lo L hi top : ℕ) (l : List ℕ) (E : List (ℕ × ℕ)) : ℕ :=
  Nat.xor (2 ^ L - 1) (Nat.land (sieveK lo L hi top l 0 E).1 (2 ^ L - 1))

theorem primeBitsOf_testBit {lo L hi top : ℕ} {l : List ℕ} {E : List (ℕ × ℕ)}
    (hl : l.Pairwise (· < ·)) (hodd : ∀ d ∈ l, d % 2 = 1 ∧ 3 ≤ d)
    (hcomp : ∀ p, p.Prime → p % 2 = 1 → p * p ≤ hi → p ∈ l)
    (hlo : lo % 2 = 1) (hlo3 : 3 ≤ lo) (hLhi : ∀ i < L, lo + 2 * i ≤ hi) (i : ℕ) :
    (primeBitsOf lo L hi top l E).testBit i = true ↔ i < L ∧ (lo + 2 * i).Prime :=
  primeBits_testBit hl hodd hcomp hlo hlo3 hLhi i

end PsiFinite
