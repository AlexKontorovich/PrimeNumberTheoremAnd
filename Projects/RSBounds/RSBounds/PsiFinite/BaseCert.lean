import TernaryGoldbach.Prelim.LogWalk
import RSBounds.PsiFinite.Segment

/-!
# Certification of `basePrimes`

`baseFacts : BaseFacts` is proved by kernel computation:

* `chainK basePrimes 0 = true`: the list is strictly increasing;
* `oddK basePrimes true = true`: its entries are odd, between 3 and 99999;
* `smallK = true`: every odd prime below 317 is in the list (trial division,
  `TernaryGoldbach.Prelim.LogWalk.isPr`);
* `baseBits = encK basePrimes 0`: the sieve of `3, 5, …, 99999` by the list's
  own entries up to 316 leaves exactly the bits of the list's entries.

By `primeBits_testBit`, the last check says that the entries are exactly the
odd primes up to 99999.
-/

namespace PsiFinite

open TernaryGoldbach.Prelim.LogWalk (isPr isPr_iff)

/-- Strictly increasing, above `prev`. -/
noncomputable def chainK (l : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun d _ ih prev => Bool.rec false (brk (ih d)) (Nat.blt prev d)) l

/-- All entries odd, between 3 and 99999. -/
noncomputable def oddK (l : List ℕ) : Bool → Bool :=
  List.rec (motive := fun _ => Bool → Bool) (fun b => b)
    (fun d _ ih b => Bool.rec false
      (brk (ih true)) (Bool.and b (Bool.and (Nat.beq (Nat.mod d 2) 1)
        (Bool.and (Nat.ble 3 d) (Nat.ble d 99999))))) l

/-- Bit `(d-3)/2` for each entry `d`. -/
noncomputable def encK (l : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun d _ ih acc =>
      let a := Nat.lor acc (Nat.shiftLeft 1 (Nat.div (Nat.sub d 3) 2))
      Bool.rec (brk (ih a)) (brk (ih 0)) (Nat.beq a 0)) l

/-- Every odd prime below 317 is listed. -/
def smallK : Bool :=
  (List.range 317).all fun n => !(isPr n && n % 2 == 1) || basePrimes.contains n

/-- The sieve of `3, 5, …, 99999` by the listed primes up to 316. -/
noncomputable def baseBits : ℕ := primeBitsOf 3 49999 99999 99999 basePrimes []

theorem chainK_true : chainK basePrimes 0 = true := by decide +kernel
theorem oddK_true : oddK basePrimes true = true := by decide +kernel
theorem smallK_true : smallK = true := by decide +kernel
theorem baseBits_eq : Nat.beq baseBits (encK basePrimes 0) = true := by decide +kernel

theorem chainK_spec : ∀ (l : List ℕ) (p : ℕ), chainK l p = true →
    (∀ d ∈ l, p < d) ∧ l.Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro p _; simp
  | cons d ds ih =>
    intro p h
    change Bool.rec (motive := fun _ => Bool) false (brk (chainK ds d)) (Nat.blt p d) = true at h
    cases hb : Nat.blt p d
    · rw [hb] at h; cases h
    · rw [hb] at h
      have hpd : p < d := by simpa using hb
      obtain ⟨h1, h2⟩ := ih d h
      refine ⟨?_, List.Pairwise.cons h1 h2⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hpd
      · exact hpd.trans (h1 e he)

theorem oddK_spec : ∀ (l : List ℕ) (b : Bool), oddK l b = true →
    ∀ d ∈ l, d % 2 = 1 ∧ 3 ≤ d ∧ d ≤ 99999 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons d ds ih =>
    intro b h
    change Bool.rec (motive := fun _ => Bool) false (brk (oddK ds true))
      (Bool.and b (Bool.and (Nat.beq (Nat.mod d 2) 1) (Bool.and (Nat.ble 3 d) (Nat.ble d 99999))))
      = true at h
    cases hb : Bool.and b (Bool.and (Nat.beq (Nat.mod d 2) 1) (Bool.and (Nat.ble 3 d)
        (Nat.ble d 99999)))
    · rw [hb] at h; cases h
    · rw [hb] at h
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩
      · exact ih true h e he

theorem encK_testBit : ∀ (l : List ℕ) (acc i : ℕ),
    (encK l acc).testBit i = true ↔ acc.testBit i = true ∨ ∃ d ∈ l, (d - 3) / 2 = i := by
  intro l
  induction l with
  | nil => intro acc i; simp [encK]
  | cons d ds ih =>
    intro acc i
    have e : encK (d :: ds) acc = encK ds (acc ||| 2 ^ ((d - 3) / 2)) := by
      change Bool.rec (motive := fun _ => ℕ)
        (brk (encK ds (Nat.lor acc (Nat.shiftLeft 1 (Nat.div (Nat.sub d 3) 2)))))
        (brk (encK ds 0)) (Nat.beq (Nat.lor acc (Nat.shiftLeft 1 (Nat.div (Nat.sub d 3) 2))) 0) = _
      have h1 : Nat.lor acc (Nat.shiftLeft 1 (Nat.div (Nat.sub d 3) 2)) = acc ||| 2 ^ ((d - 3) / 2) := by
        rw [← Nat.one_shiftLeft]; rfl
      rw [h1]
      cases hb : Nat.beq (acc ||| 2 ^ ((d - 3) / 2)) 0
      · rfl
      · show brk (encK ds 0) = _
        rw [brk_eq, Nat.eq_of_beq_eq_true hb]
    rw [e, ih, Nat.testBit_or, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem smallK_spec (p : ℕ) (hp : p.Prime) (ho : p % 2 = 1) (hp317 : p < 317) : p ∈ basePrimes := by
  have h := List.all_eq_true.mp smallK_true p (List.mem_range.mpr hp317)
  have hi : isPr p = true := (isPr_iff (by omega)).mpr hp
  simp only [hi, ho, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] at h
  exact h

/-- **The base list is exactly the odd primes up to 99999.** -/
theorem baseFacts : BaseFacts := by
  obtain ⟨-, hsorted⟩ := chainK_spec basePrimes 0 chainK_true
  have hodd := oddK_spec basePrimes true oddK_true
  have hodd3 : ∀ d ∈ basePrimes, d % 2 = 1 ∧ 3 ≤ d := fun d hd => ⟨(hodd d hd).1, (hodd d hd).2.1⟩
  have hsmall : ∀ p, p.Prime → p % 2 = 1 → p * p ≤ 99999 → p ∈ basePrimes := by
    intro p hp ho hpp
    exact smallK_spec p hp ho (by nlinarith)
  have hX : ∀ i, baseBits.testBit i = true ↔ i < 49999 ∧ (3 + 2 * i).Prime := by
    intro i
    exact primeBitsOf_testBit (lo := 3) (L := 49999) (hi := 99999) (top := 99999) (E := [])
      hsorted hodd3 hsmall rfl le_rfl (by intro i hi; omega) i
  have heq : baseBits = encK basePrimes 0 := Nat.eq_of_beq_eq_true baseBits_eq
  have key : ∀ i, (i < 49999 ∧ (3 + 2 * i).Prime) ↔ ∃ d ∈ basePrimes, (d - 3) / 2 = i := by
    intro i
    rw [← hX i, heq, encK_testBit]; simp
  refine ⟨hsorted, ?_, ?_⟩
  · intro d hd
    obtain ⟨h1, h2, h3⟩ := hodd d hd
    obtain ⟨-, hp⟩ := (key ((d - 3) / 2)).mpr ⟨d, hd, rfl⟩
    rw [show 3 + 2 * ((d - 3) / 2) = d by omega] at hp
    exact ⟨hp, h1⟩
  · intro p hp ho hpp
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hp5 : p ≤ 99999 := by
      by_contra h
      have : 100001 * 100001 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
      simp only [baseCover] at hpp
      exact absurd (le_trans this hpp) (by norm_num)
    obtain ⟨d, hd, hdi⟩ := (key ((p - 3) / 2)).mp ⟨by omega, by
      rw [show 3 + 2 * ((p - 3) / 2) = p by omega]; exact hp⟩
    obtain ⟨h1, h2, -⟩ := hodd d hd
    have : d = p := by omega
    exact this ▸ hd

end PsiFinite
